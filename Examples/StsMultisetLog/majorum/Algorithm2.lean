import Examples.StsMultisetLog.majorum.Components
import Mathlib.Data.Set.Functor

/-!
# Algorithm 2: the probabilistically-safe TOB-SVD variant with fast confirmations

The dynamically available component on its own — Majorum (Algorithm 5) is this plus the
finality component. **Lemma 2 and Theorems 1–2 are about this algorithm** (Appendix A), a
course correction recorded in `CONTEXT.md` (2026-08-03): the finality-free `chfrozen` makes
Lemma 2's vote-round half reachable without any justified-checkpoint reasoning.

Sources: arXiv:2601.03862v1, Algorithm 2 (§3.3), with `MFC` from Algorithm 1 and
the joining protocol from §2 — all of whose functions already live in `Components.lean`
and are used here directly, with no `Components` record: the paper defines everything
Algorithm 2 calls.

## Message reuse, and the paper's "·"

Algorithm 2's messages are Algorithm 5's with the finality fields left blank — the paper
writes `[vote, ch, ·, t, vi]` and `[propose, chp, chC, QC, ·, t, vp]`, the `·` being the
placeholder the fin-vote and checkpoint later fill. The blank is **nondeterministic**:
the handler is `Set`-valued with the filler assigned by nondeterministic assignment at
its use site (`let dot ← Set.univ`), the tick step ties in by membership — the
framework's `step` is a relation exactly so this is expressible — and on the receiving
side `ValidProposal2` accepts certified votes with *any* filler. So nothing anywhere can depend on what fills the blank, which is the
paper's `·` taken literally (user decision, 2026-08-03; this replaced a `dot` parameter
of the protocol, which itself replaced a fixed `dotCk := ⟨[], 0⟩`). The same `Msg` type
serves both algorithms; that keeps every filter and fork-choice function applicable
verbatim, and makes Appendix C's lifting ("honest validators send identical messages in
both protocols except for the finality component") a statement about message values up
to the blank fields.

## The certificate check

A proposal carries `(chC, QC)` and is valid only if the certificate vouches for `chC`. A
`QCert` payload is unauthenticated data — an adversary can fabricate one — so the
signature-idealized reading of "verify the QC" is that the certified votes are ones the
receiver *holds*: each entry's vote message is in the view (gossip makes carried votes
held: "a validator receiving a proposal also gossips the … votes contained"), from slot
`t' − 1`, for a chain extending `chC`, with at least `2n/3` distinct signers. A genesis
`chC` needs no certificate, matching `fastconfirmsimple`'s `(B_genesis, ∅)`.
-/

set_option autoImplicit false

attribute [local instance] Set.monad

namespace Majorum

open the framework's flat multiset-log flavour Classical

variable {Node Tx : Type} [DecidableEq Node] [DecidableEq Tx]

/-- Algorithm 2's per-validator state: the confirmed chain and the two merge-round
    snapshots, plus the activation round of the joining protocol (§2, shared by every
    protocol in this model). -/
structure NodeState2 (Node Tx : Type) [DecidableEq Node] [DecidableEq Tx] where
  /-- The confirmed chain `Ch_i`, Algorithm 2's one output. -/
  chi : Chain Tx
  /-- Snapshot of the view at `4Δt + 3Δ`. -/
  vFrozen : View Node (Msg (Chain Tx) (QCert Node Tx))
  /-- Snapshot of the fast-confirmed chain at `4Δt + 3Δ`. -/
  chFrozen : Chain Tx
  /-- The first round from which this validator may send (`activationRound`). -/
  activeAt : Time

/-- Proposal validity, certificate included: the proposed chain belongs to the proposal's
    slot and extends the carried fast-confirmed chain, and the certificate's votes — held
    in the receiver's own view — give `chC` at least `2n/3` distinct supporters from the
    previous slot. A certified vote counts **with any filler** in its blank fields,
    matching the sender side's nondeterministic choice. See the module docstring for why
    the check runs against the view. -/
def ValidProposal2 (n : Nat) (V : View Node (Msg (Chain Tx) (QCert Node Tx)))
    (sm : SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) : Prop :=
  match sm.msg with
  | .propose chp chC qc _ t' =>
      proposedAt chp = t' ∧ chainLe chC chp ∧
        (chC = [] ∨ ∃ cert : QCert Node Tx, qc = some cert ∧
          2 * n ≤ 3 * (cert.image Prod.fst).card ∧
          ∀ e ∈ cert, chainLe chC e.2.1 ∧ e.2.2 = t' - 1 ∧
            ∃ src tgt : Checkpoint (Chain Tx),
              (⟨e.1, Msg.vote e.2.1 src tgt e.2.2⟩ :
                SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ V)
  | .vote .. => False

/-- Algorithm 2 lines 33–36: a valid slot-`t` proposal whose fast-confirmed chain extends
    the frozen one replaces it. Received during `[4Δt, 4Δt+Δ]`, processed at the vote
    reading, folded over the view — the same arrival-order caveat as Algorithm 5's
    `processProposals`. -/
noncomputable def processProposals2 (n : Nat)
    (V : View Node (Msg (Chain Tx) (QCert Node Tx)))
    (t : Nat) (s : NodeState2 Node Tx) : NodeState2 Node Tx :=
  V.toList.foldl (fun acc sm =>
    match sm.msg with
    | .propose _ chC _ _ t' =>
        if t' = t ∧ ValidProposal2 n V sm ∧ chainLe acc.chFrozen chC then
          { acc with chFrozen := chC }
        else acc
    | .vote .. => acc) s

/-- The deterministic core of `handler2`: Algorithm 2's four phase actions with the
    blank filler given. The proof layer works over this — `mem_handler2_iff` recovers it
    from the protocol's `Set`-valued handler below.

    Differences from Algorithm 5's handler, all of them the *absence* of finality: no
    `gjFrozen`, votes carry the placeholder `dot` in the fin-vote fields, the propose
    message carries it for the checkpoint, fast confirmation is `fastconfirmsimple` unwrapped (line
    28 assigns whenever a quorum exists, with no greatest-justified floor), and the one
    output chain is `chi`. The joining gates are the same. -/
noncomputable def handler2Core (Q : Params) (n kappa : Nat) (pool : Nat → Tx)
    (proposer : Nat → Node) (dot : Checkpoint (Chain Tx)) (p : Node) (r : Time)
    (V : View Node (Msg (Chain Tx) (QCert Node Tx))) (s : NodeState2 Node Tx) :
    NodeStepResult (NodeState2 Node Tx) (Msg (Chain Tx) (QCert Node Tx)) :=
  let slot : Nat := r / Q.slotLength
  let phase : Nat := r % Q.slotLength
  if phase = 0 then
    -- Propose, lines 14–19 — only once active
    if p = proposer slot ∧ s.activeAt ≤ r then
      let cq := fastConfirmSimple n V (slot - 1)
      let chMFC := mfc V V cq.1 slot
      let chp := extend pool chMFC slot
      { state := s, send := {.propose chp cq.1 cq.2 dot slot} }
    else { state := s, send := 0 }
  else if phase = Q.delta then
    -- Vote, lines 20–25, after the lines 33–36 proposal processing
    let s' := processProposals2 n V slot s
    let chMFC := mfc s'.vFrozen V s'.chFrozen slot
    -- line 22: `Ch_i ← max({ch ∈ {Ch_i, (chMFC)⌈κ} : ch ⪯ chMFC})`
    let chi :=
      [s'.chi, kappaPrefix kappa chMFC].foldl
        (fun acc c => if chainLe c chMFC then (if chainLe acc c then c else acc) else acc)
        s'.chi
    let proposedNow : Option (Chain Tx) :=
      V.toList.findSome? (fun sm => match sm.msg with
        | .propose chp _ _ _ t' =>
            if t' == slot && proposedAt chp == slot && chainLe chMFC chp then some chp
            else none
        | .vote .. => none)
    let ch := proposedNow.getD chMFC
    { state := { s' with chi := chi },
      -- a joining validator executes silently
      send := if s.activeAt ≤ r then {.vote ch dot dot slot} else 0 }
  else if phase = 2 * Q.delta then
    -- Fast Confirm, lines 26–29: adopt whenever a quorum certificate exists
    let fq := fastConfirmSimple n V slot
    { state := if fq.2.isSome then { s with chi := fq.1 } else s, send := 0 }
  else if phase = 3 * Q.delta then
    -- Merge, lines 30–32
    { state := { s with vFrozen := V, chFrozen := (fastConfirmSimple n V slot).1 }, send := 0 }
  else
    { state := s, send := 0 }

/-- Algorithm 2's four phase actions, as one `do` block over the `Set` monad: `←` is a
    nondeterministic assignment — the blank finality fields, assigned any value at their
    use sites in the propose and vote branches — and `return` marks each branch's
    outcome. This is the protocol's handler; `handler2Core` is its deterministic core,
    recovered by `mem_handler2_iff`. -/
noncomputable def handler2 (Q : Params) (n kappa : Nat) (pool : Nat → Tx)
    (proposer : Nat → Node) (p : Node) (r : Time)
    (V : View Node (Msg (Chain Tx) (QCert Node Tx))) (s : NodeState2 Node Tx) :
    Set (NodeStepResult (NodeState2 Node Tx) (Msg (Chain Tx) (QCert Node Tx))) := do
  let slot : Nat := r / Q.slotLength
  let phase : Nat := r % Q.slotLength
  if phase = 0 then
    if p = proposer slot ∧ s.activeAt ≤ r then
      let dot ← (Set.univ : Set (Checkpoint (Chain Tx)))
      let cq := fastConfirmSimple n V (slot - 1)
      let chMFC := mfc V V cq.1 slot
      let chp := extend pool chMFC slot
      return { state := s, send := {.propose chp cq.1 cq.2 dot slot} }
    else
      return { state := s, send := 0 }
  else if phase = Q.delta then
    let dot ← (Set.univ : Set (Checkpoint (Chain Tx)))
    let s' := processProposals2 n V slot s
    let chMFC := mfc s'.vFrozen V s'.chFrozen slot
    let chi :=
      [s'.chi, kappaPrefix kappa chMFC].foldl
        (fun acc c => if chainLe c chMFC then (if chainLe acc c then c else acc) else acc)
        s'.chi
    let proposedNow : Option (Chain Tx) :=
      V.toList.findSome? (fun sm => match sm.msg with
        | .propose chp _ _ _ t' =>
            if t' == slot && proposedAt chp == slot && chainLe chMFC chp then some chp
            else none
        | .vote .. => none)
    let ch := proposedNow.getD chMFC
    return { state := { s' with chi := chi },
             send := if s.activeAt ≤ r then {.vote ch dot dot slot} else 0 }
  else if phase = 2 * Q.delta then
    let fq := fastConfirmSimple n V slot
    return { state := if fq.2.isSome then { s with chi := fq.1 } else s, send := 0 }
  else if phase = 3 * Q.delta then
    return { state := { s with vFrozen := V, chFrozen := (fastConfirmSimple n V slot).1 },
             send := 0 }
  else
    return { state := s, send := 0 }

/-- Membership in a nondeterministic assignment followed by a deterministic
    continuation — Event-B's `x :∈ S; y := f(x)`, inverted. -/
theorem mem_assign {α β : Type} {f : α → β} {res : β} :
    (res ∈ do { let x ← (Set.univ : Set α); pure (f x) }) ↔ ∃ x, res = f x := by
  rw [Set.bind_def]
  simp [Set.pure_def, eq_comm]

/-- Membership in a deterministic branch, phrased with the vacuous choice the
    deterministic core still binds. -/
theorem mem_pure_exists {α β : Type} [Nonempty α] {b res : β} :
    (res ∈ (pure b : Set β)) ↔ ∃ _ : α, res = b := by
  simp [Set.pure_def]

/-- **The inversion lemma**: membership in the handler is exactly "the deterministic
    core, for some filler". The one bridge the proof layer needs. -/
theorem mem_handler2_iff {Q : Params} {n kappa : Nat} {pool : Nat → Tx}
    {proposer : Nat → Node} {p : Node} {r : Time}
    {V : View Node (Msg (Chain Tx) (QCert Node Tx))} {s : NodeState2 Node Tx}
    {res : NodeStepResult (NodeState2 Node Tx) (Msg (Chain Tx) (QCert Node Tx))} :
    res ∈ handler2 Q n kappa pool proposer p r V s ↔
      ∃ dot, res = handler2Core Q n kappa pool proposer dot p r V s := by
  haveI hne : Nonempty (Checkpoint (Chain Tx)) := ⟨⟨[], 0⟩⟩
  simp only [handler2, handler2Core]
  split_ifs <;>
    first
      | exact mem_assign
      | exact mem_pure_exists (α := Checkpoint (Chain Tx))

/-- Algorithm 2 as a framework protocol: a tick may produce anything the `Set`-valued
    handler contains — the blanks are chosen anew at each tick. Everything else is
    deterministic; no protocol-specific events; the wake event runs the joining
    protocol, exactly as in Algorithm 5. -/
noncomputable def protocol2 (Q : Params) (n kappa : Nat) (pool : Nat → Tx)
    (proposer : Nat → Node) :
    Protocol Node (Msg (Chain Tx) (QCert Node Tx)) (NodeState2 Node Tx) Empty where
  init _ := { chi := [], vFrozen := ∅, chFrozen := [], activeAt := 0 }
  step p r V s e res := match e with
    | .tick => res ∈ handler2 Q n kappa pool proposer p r V s
    | .recv _ => res = { state := s, send := 0 }
    | .wake => res = { state := { s with activeAt := activationRound Q r }, send := 0 }
    | .custom ev => ev.elim
  total p r V s e := match e with
    | .tick => ⟨handler2Core Q n kappa pool proposer ⟨[], 0⟩ p r V s,
        mem_handler2_iff.mpr ⟨⟨[], 0⟩, rfl⟩⟩
    | .recv _ => ⟨_, rfl⟩
    | .wake => ⟨_, rfl⟩
    | .custom ev => ev.elim
  enabled _ _ ev := ev.elim

end Majorum
