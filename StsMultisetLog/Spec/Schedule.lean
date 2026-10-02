module
public import StsMultisetLog.Spec.Message

@[expose] public section

/-!
# The adversary's schedule

What the adversary controls over an execution: who is corrupted when, and which
honest validators are awake when. Nothing else — in particular there is no notion
of being "active": refraining from acting after waking is something an honest
validator's *program* does (Majorum's joining protocol), so it belongs to that
protocol, not here. Both are functions of the round, because both
papers need time-dependent honesty — Majorum's `A_r`, TOB-SVD's growing `B_t`.

**Indexed by `Int`, not `Time`.** Both papers query the schedule at negative
times and they use *different* conventions there (Majorum: `H_i := ∅` for
`i < 0`; TOB-SVD: `H_t` is every validator and `B_t := ∅` for `t < 0`). Making the index `Int`
puts that convention in the schedule, where the model can choose it, instead of
hardcoding one.

Nothing here is assumed. Monotone corruption, corruption delay, participation
constraints — each is a separate predicate a model opts into.
-/

set_option autoImplicit false

namespace Framework.StsMultisetLog

variable {Node : Type} [Fintype Node] [DecidableEq Node]

/-- The adversary's choices over an execution. -/
structure Schedule (Node : Type) where
  /-- Adversarial validators at a round (Majorum's `A_r`, TOB-SVD's `B_t`). -/
  adv : Int → Finset Node
  /-- Awake honest validators at a round. Adversarial validators are always
      awake in both papers, so they are deliberately *not* included here — this
      is the awake **honest** set. The atomic semantics (`Spec/AtomicExecution.lean`)
      does not rely on a schedule keeping the two apart: its honest actions (delivery,
      protocol event, forward, the tick's reactions) are enabled only at validators in
      `awake` and outside `adv`, so a validator in both acts only adversarially. -/
  awake : Int → Finset Node

namespace Schedule

variable (S : Schedule Node)

/-! ### Constraints a model may impose -/

/-- Corruption is irreversible: TOB-SVD's growing-adversary assumption, and
    implicit in Majorum's `A_∞ = lim A_{voting(t)}`. -/
def MonotoneCorruption : Prop := ∀ r r' : Int, r ≤ r' → S.adv r ⊆ S.adv r'

/-- Awake honest validators are not adversarial: the schedule itself keeps `awake` and
    `adv` disjoint. The fine semantics needs it to make every reaction an honest node's.
    The atomic semantics does not: there, a validator in both sets is treated as
    adversarial by the enabling conditions themselves, so this constraint only says the
    schedule never lists such a validator. -/
def AwakeHonest : Prop := ∀ r : Int, Disjoint (S.awake r) (S.adv r)

/-- Mildly adaptive corruption: a validator adversarial at `r + d` was already
    committed to at `r`. TOB-SVD needs this with `d = Δ` for VRF-based leader
    election; state it against a `requested` schedule the adversary fixes. -/
def CorruptionDelay (d : Time) (requested : Int → Finset Node) : Prop :=
  ∀ r : Int, S.adv (r + d) ⊆ requested r

/-- Total corruption budget, as `f = |A_∞|` in Majorum. -/
def CorruptionBounded (f : Nat) : Prop := ∀ r : Int, (S.adv r).card ≤ f

/-- Global awake time: after `gat`, every honest validator stays awake. Majorum
    assumes one; TOB-SVD does not. -/
def GlobalAwakeTime (gat : Time) (honest : Finset Node) : Prop :=
  ∀ r : Int, (gat : Int) ≤ r → honest \ S.adv r ⊆ S.awake r

/-! ### Interval operators

The two papers aggregate awakeness over an interval in **opposite** ways, and
both are needed, so the framework provides both and neither is privileged. -/

/-- Awake at *some point* in `[a, b]` — Majorum's `H_{r,r'} = ⋃ H_i`. -/
def awakeSomewhere (a b : Int) : Finset Node := (Finset.Icc a b).sup S.awake

/-- Awake *throughout* `[a, b]` — TOB-SVD's `H_{t₁,t₂} = ⋂ H_t`. -/
def awakeThroughout (a b : Int) : Finset Node := (Finset.Icc a b).inf S.awake

end Schedule

end Framework.StsMultisetLog
