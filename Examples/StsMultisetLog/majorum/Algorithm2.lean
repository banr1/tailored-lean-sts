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
    the check runs against the view.

    **The proposal must be signed by its slot's proposer** (`sm.sender = proposer t'`).
    The paper's `valid([propose, …])` is never defined; Lemma 4 is false without this
    conjunct (a corrupt validator could have a certificate-backed `chC` processed, or —
    at line 23 — its fabricated slot-`t` chain voted for), and the paper's own base-case
    equalities need it. Structural signing makes it enforceable: nobody can forge the
    proposer's sender field. Decision of 2026-08-04; third authors'-note finding. -/
def ValidProposal2 (n : Nat) (proposer : Nat → Node)
    (V : View Node (Msg (Chain Tx) (QCert Node Tx)))
    (sm : SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) : Prop :=
  match sm.msg with
  | .propose chp chC qc _ t' =>
      sm.sender = proposer t' ∧ proposedAt chp = t' ∧ chainLe chC chp ∧
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
noncomputable def processProposals2 (n : Nat) (proposer : Nat → Node)
    (V : View Node (Msg (Chain Tx) (QCert Node Tx)))
    (t : Nat) (s : NodeState2 Node Tx) : NodeState2 Node Tx :=
  V.toList.foldl (fun acc sm =>
    match sm.msg with
    | .propose _ chC _ _ t' =>
        if t' = t ∧ ValidProposal2 n proposer V sm ∧ chainLe acc.chFrozen chC then
          { acc with chFrozen := chC }
        else acc
    | .vote .. => acc) s

/-- Algorithm 2's four phase actions, as one `do` block over the `Set` monad: `←` is a
    nondeterministic assignment — the blank finality fields, assigned any value at their
    use sites in the propose and vote branches — and `return` marks each branch's
    outcome. This is the protocol's handler; its deterministic core `handler2Core`,
    which the proof layer works over, lives in `Provenance2.lean`. -/
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
    let s' := processProposals2 n proposer V slot s
    let chMFC := mfc s'.vFrozen V s'.chFrozen slot
    -- Line 22 runs only once active: the κ-deep rule reads the *frozen* snapshots, and a
    -- validator that slept through the merge round has stale ones — κ-deep-confirming
    -- from them is unsound (fifth authors'-note finding; see `CONTEXT.md`, 2026-08-04,
    -- Lemma 5 is false without this guard). The joining protocol's silence is read as
    -- covering the frozen-state-dependent confirmation rule, not just the sends; the
    -- fast-confirmation rule below stays unguarded — it reads the current view, and any
    -- `2n/3` quorum there is network-anchored.
    let chi :=
      if s.activeAt ≤ r then
        [s'.chi, kappaPrefix kappa slot chMFC].foldl
          (fun acc c => if chainLe c chMFC then (if chainLe acc c then c else acc) else acc)
          s'.chi
      else s'.chi
    let proposedNow : Option (Chain Tx) :=
      V.toList.findSome? (fun sm => match sm.msg with
        | .propose chp _ _ _ t' =>
            if sm.sender == proposer slot && t' == slot && proposedAt chp == slot &&
                slotsIncreasing chp && chainLe chMFC chp then some chp
            else none
        | .vote .. => none)
    let ch := proposedNow.getD chMFC
    return { state := { s' with chi := chi },
             send := if s.activeAt ≤ r then {.vote ch dot dot slot} else 0 }
  else if phase = 2 * Q.delta then
    -- Fast Confirm, lines 26–29 — with **Algorithm 5's line-23 guard** (`if chAva ⪰̸
    -- fastcand then chAva ← fastcand`): Algorithm 2's own line 29 is a plain
    -- `Chi ← fastcand`, which lets an adversarially completed quorum on an old prefix
    -- of the confirmed chain regress `Ch` below an already-κ-confirmed proposal,
    -- breaking Theorem 2's liveness (seventh authors'-note finding; user decision,
    -- 2026-08-04; see `CONTEXT.md`).
    let fq := fastConfirmSimple n V slot
    let sF :=
      if fq.2.isSome then
        { s with chi := if chainLe fq.1 s.chi then s.chi else fq.1 }
      else s
    return { state := sF, send := 0 }
  else if phase = 3 * Q.delta then
    return { state := { s with vFrozen := V, chFrozen := (fastConfirmSimple n V slot).1 },
             send := 0 }
  else
    return { state := s, send := 0 }

/-- Every branch of `handler2` offers at least one result — the feasibility fact
    `protocol2`'s `total` obligation needs. Proved directly on the `Set` structure; the
    proof layer's inversion through the deterministic core lives in `Provenance2.lean`. -/
theorem handler2_nonempty (Q : Params) (n kappa : Nat) (pool : Nat → Tx)
    (proposer : Nat → Node) (p : Node) (r : Time)
    (V : View Node (Msg (Chain Tx) (QCert Node Tx))) (s : NodeState2 Node Tx) :
    (handler2 Q n kappa pool proposer p r V s).Nonempty := by
  simp only [handler2]
  split_ifs <;>
    first
      | exact ⟨_, by
          rw [Set.bind_def]
          exact Set.mem_biUnion (Set.mem_univ (⟨[], 0⟩ : Checkpoint (Chain Tx))) rfl⟩
      | exact ⟨_, rfl⟩

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
    | .tick => handler2_nonempty Q n kappa pool proposer p r V s
    | .recv _ => ⟨_, rfl⟩
    | .wake => ⟨_, rfl⟩
    | .custom ev => ev.elim
  enabled _ _ ev := ev.elim

end Majorum
