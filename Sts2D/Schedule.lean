import Framework.Sts2D.Message

/-!
# The adversary's schedule

What the adversary controls over an execution: who is corrupted when, and which
honest validators are awake when. Nothing else — in particular there is no notion
of being "active": refraining from acting after waking is something an honest
validator's *program* does (Majorum's joining protocol), so it belongs to that
protocol, not here. Both are functions of the round, because both
papers need time-dependent honesty — Majorum's `A_r`, TOB-SVD's growing `B_t`.

**Indexed by `Int`, not `Round`.** Both papers query the schedule at negative
times and they use *different* conventions there (Majorum: `H_i := ∅` for
`i < 0`; TOB-SVD: `H_t := V` and `B_t := ∅` for `t < 0`). Making the index `Int`
puts that convention in the schedule, where the model can choose it, instead of
hardcoding one.

Nothing here is assumed. Monotone corruption, corruption delay, participation
constraints — each is a separate predicate a model opts into.
-/

set_option autoImplicit false

namespace Framework.Sts2D

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The adversary's choices over an execution. -/
structure Schedule (V : Type) where
  /-- Adversarial validators at a round (Majorum's `A_r`, TOB-SVD's `B_t`). -/
  adv : Int → Finset V
  /-- Awake honest validators at a round. Adversarial validators are always
      awake in both papers, so they are deliberately *not* included here — this
      is the awake **honest** set. -/
  awake : Int → Finset V

namespace Schedule

variable (S : Schedule V)

/-! ### Constraints a model may impose -/

/-- Corruption is irreversible: TOB-SVD's growing-adversary assumption, and
    implicit in Majorum's `A_∞ = lim A_{voting(t)}`. -/
def MonotoneCorruption : Prop := ∀ r r' : Int, r ≤ r' → S.adv r ⊆ S.adv r'

/-- Awake honest validators are not adversarial. -/
def AwakeHonest : Prop := ∀ r : Int, Disjoint (S.awake r) (S.adv r)

/-- Mildly adaptive corruption: a validator adversarial at `r + d` was already
    committed to at `r`. TOB-SVD needs this with `d = Δ` for VRF-based leader
    election; state it against a `requested` schedule the adversary fixes. -/
def CorruptionDelay (d : Round) (requested : Int → Finset V) : Prop :=
  ∀ r : Int, S.adv (r + d) ⊆ requested r

/-- Total corruption budget, as `f = |A_∞|` in Majorum. -/
def CorruptionBounded (f : Nat) : Prop := ∀ r : Int, (S.adv r).card ≤ f

/-- Global awake time: after `gat`, every honest validator stays awake. Majorum
    assumes one; TOB-SVD does not. -/
def GlobalAwakeTime (gat : Round) (honest : Finset V) : Prop :=
  ∀ r : Int, (gat : Int) ≤ r → honest \ S.adv r ⊆ S.awake r

/-! ### Interval operators

The two papers aggregate awakeness over an interval in **opposite** ways, and
both are needed, so the framework provides both and neither is privileged. -/

/-- Awake at *some point* in `[a, b]` — Majorum's `H_{r,r'} = ⋃ H_i`. -/
def awakeSomewhere (a b : Int) : Finset V := (Finset.Icc a b).sup S.awake

/-- Awake *throughout* `[a, b]` — TOB-SVD's `H_{t₁,t₂} = ⋂ H_t`. -/
def awakeThroughout (a b : Int) : Finset V := (Finset.Icc a b).inf S.awake

end Schedule

end Framework.Sts2D
