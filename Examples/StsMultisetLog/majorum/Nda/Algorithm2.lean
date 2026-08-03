import Examples.StsMultisetLog.majorum.Algorithm2
import Mathlib.Data.Set.Functor

/-!
# Algorithm 2 with nondeterministic assignment — a comparison attempt

The same protocol as `Majorum.protocol2`, written in the other style discussed on
2026-08-04: instead of hoisting the blank-filler choice to the step relation
(`∃ dot, res = handler2 … dot …`), the handler itself is **`Set`-valued** and the choice
is a *nondeterministic assignment at its use site* — `let dot ← Set.univ` is Event-B's
`dot :∈ Checkpoint`, written where the paper writes "·". The step relation ties in by
membership: `res ∈ handler2 …`.

Kept in its own directory and namespace so the two styles can be compared side by side;
neither imports the other's *proof* layer, but this one deliberately reuses the parent's
spec components (`NodeState2`, `ValidProposal2`, `processProposals2`) and — the crux —
recovers the parent's deterministic `handler2` as its **core** through one inversion
lemma, `mem_handler2_iff`. Everything the proofs need about a tick then comes from the
parent's handler-level lemmas, which is the honest accounting of this style's cost: a
`Set`-monadic handler is a deterministic core plus an inversion lemma, and the do-notation
is what you buy for it. The comparison would tilt further in this style's favor if more
choice points went nondeterministic (any received valid proposal instead of `findSome?`'s
first match, fork-choice tie-breaks) — then each `←` line replaces a hand-hoisted `∃`.

Semantically identical to the parent: same executions, same theorems (`Nda.lemma2` in
`Nda/Lemmas.lean`).
-/

set_option autoImplicit false

attribute [local instance] Set.monad

namespace Majorum.Nda

open the framework's flat multiset-log flavour

variable {Node Tx : Type} [DecidableEq Node] [DecidableEq Tx]

/-- Algorithm 2's four phase actions, with the blank finality fields **assigned
    nondeterministically where they occur**: `let dot ← Set.univ` in the propose and vote
    branches. The deterministic branches are `pure`. Compare `Majorum.handler2`,
    which takes the filler as a parameter instead. -/
noncomputable def handler2 (Q : Params) (n kappa : Nat) (pool : Nat → Tx)
    (proposer : Nat → Node) (p : Node) (r : Time)
    (V : View Node (Msg (Chain Tx) (QCert Node Tx))) (s : NodeState2 Node Tx) :
    Set (NodeStepResult (NodeState2 Node Tx) (Msg (Chain Tx) (QCert Node Tx))) :=
  let slot : Nat := r / Q.slotLength
  let phase : Nat := r % Q.slotLength
  if phase = 0 then
    if p = proposer slot ∧ s.activeAt ≤ r then do
      let dot ← (Set.univ : Set (Checkpoint (Chain Tx)))
      let cq := fastConfirmSimple n V (slot - 1)
      let chMFC := mfc V V cq.1 slot
      let chp := extend pool chMFC slot
      pure { state := s, send := {.propose chp cq.1 cq.2 dot slot} }
    else pure { state := s, send := 0 }
  else if phase = Q.delta then do
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
    pure { state := { s' with chi := chi },
           send := if s.activeAt ≤ r then {.vote ch dot dot slot} else 0 }
  else if phase = 2 * Q.delta then
    let fq := fastConfirmSimple n V slot
    pure { state := if fq.2.isSome then { s with chi := fq.1 } else s, send := 0 }
  else if phase = 3 * Q.delta then
    pure { state := { s with vFrozen := V, chFrozen := (fastConfirmSimple n V slot).1 },
           send := 0 }
  else
    pure { state := s, send := 0 }

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

/-- **The inversion lemma**: membership in the monadic handler is exactly "the parent's
    deterministic handler, for some filler". This is the one bridge the proof layer
    needs — after it, every handler-level fact comes from the parent's lemmas. -/
theorem mem_handler2_iff {Q : Params} {n kappa : Nat} {pool : Nat → Tx}
    {proposer : Nat → Node} {p : Node} {r : Time}
    {V : View Node (Msg (Chain Tx) (QCert Node Tx))} {s : NodeState2 Node Tx}
    {res : NodeStepResult (NodeState2 Node Tx) (Msg (Chain Tx) (QCert Node Tx))} :
    res ∈ handler2 Q n kappa pool proposer p r V s ↔
      ∃ dot, res = the framework's flat multiset-log flavour.handler2 Q n kappa pool proposer dot p r V s := by
  haveI hne : Nonempty (Checkpoint (Chain Tx)) := ⟨⟨[], 0⟩⟩
  simp only [handler2, the framework's flat multiset-log flavour.handler2]
  split_ifs <;>
    first
      | exact mem_assign
      | exact mem_pure_exists (α := Checkpoint (Chain Tx))

/-- Algorithm 2 as a framework protocol, membership-style: a tick may produce anything
    the `Set`-valued handler contains. -/
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
    | .tick => ⟨the framework's flat multiset-log flavour.handler2 Q n kappa pool proposer ⟨[], 0⟩ p r V s,
        mem_handler2_iff.mpr ⟨⟨[], 0⟩, rfl⟩⟩
    | .recv _ => ⟨_, rfl⟩
    | .wake => ⟨_, rfl⟩
    | .custom ev => ev.elim
  enabled _ _ ev := ev.elim

end Majorum.Nda
