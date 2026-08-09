import Mathlib.Data.Rat.Defs
import Sts2D.Execution

/-!
# Two models, expressed

The point of the framework is that these are *instances*, not the framework
itself. Both are stated here so the parameterisation is validated by use rather
than asserted: if either stops being expressible, this file stops compiling.

* `Models.Majorum` — the generalized partially synchronous sleepy model of
  Majorum (a.k.a. 3SF) §Model/§Adversary: rounds, slots of `4Δ`, partial
  synchrony with GST, GAT, awake-vs-active with a joining protocol, and
  Constraint (1) over validators active *at some point*.
* `Models.TobSvd` — TOB-SVD §3.1: synchrony (`GST = 0`), a growing adversary,
  awake = active, and `(Tb, Ts, ρ)`-compliance over validators awake
  *throughout* an interval.

The two disagree about how to aggregate awakeness over an interval (union vs
intersection), so the framework supplies both operators and privileges neither.
Neither model mentions "active": Majorum's joining protocol is behaviour of
validators running Majorum, so its effect on the counting condition is written out
in terms of continuous wakefulness instead.
-/

set_option autoImplicit false

namespace Framework.Sts2D.Models

variable {V Msg State Ev : Type} [Fintype V] [DecidableEq V] [DecidableEq Msg]

/-! ## Majorum -/

namespace Majorum

/-- Parameters of Majorum's model. -/
structure Params where
  /-- Number of validators. -/
  n : Nat
  /-- Corruption budget, `f = |A_∞|`. -/
  f : Nat
  /-- Message delay bound after GST. -/
  delta : Round
  /-- Global stabilization time. -/
  gst : Round
  /-- Global awake time. -/
  gat : Round
  /-- `f < n/3`. -/
  fBound : 3 * f < n
  /-- Slots are `4Δ` rounds, so Δ must be positive. -/
  deltaPos : 0 < delta

namespace Params

variable (Q : Params)

/-- Rounds per slot: `4Δ`. -/
def slotLength : Nat := 4 * Q.delta

/-- First round of slot `t`, where proposals happen. -/
def proposing (t : Nat) : Round := Q.slotLength * t

/-- The voting round of slot `t`: `4Δt + Δ`. -/
def voting (t : Nat) : Round := Q.slotLength * t + Q.delta

/-- Constraint (1): for every slot after GST,
    `|H_{voting(t−1)} \ A_{voting(t)}| > |A_{voting(t)}|`.

    `H_r` is the set of validators *active* at `r`, which for Majorum means having
    finished joining. Joining is protocol behaviour — but it is **deterministic in
    the wake schedule**: a validator is active at `voting(t−1)` exactly when it has
    been awake continuously since `voting(t−2)+Δ`. So the condition is expressible
    over the schedule alone, with no handle on protocol state, which is what
    `awakeThroughout` is for.

    The correspondence is not free: whatever Majorum protocol we write must
    actually stay silent until it has been awake that long, or this assumption and
    the protocol disagree. That is a lemma about the protocol, to be discharged
    where the protocol lives.

    Guarded by `2 ≤ t` so `t - 2` is genuine subtraction rather than `Nat`
    truncation, and by `proposing t` rather than `voting t` — "every slot after
    GST" means the slot *starts* after GST. -/
def Compliant (S : Schedule V) : Prop :=
  ∀ t : Nat, 2 ≤ t → Q.gst ≤ Q.proposing t →
    (S.adv ((Q.voting t : Int))).card <
      ((S.awakeThroughout ((Q.voting (t - 2) : Int) + (Q.delta : Int))
          ((Q.voting (t - 1) : Int))) \ S.adv ((Q.voting t : Int))).card

/-- The model: everything Majorum assumes of an execution. -/
def Model {Pr : Protocol V Msg State Ev} {S : Schedule V}
    (x : Exec Pr S) : Prop :=
  S.MonotoneCorruption ∧ S.AwakeHonest ∧ S.CorruptionBounded Q.f ∧
    S.GlobalAwakeTime Q.gat Finset.univ ∧ Q.Compliant S ∧
    ViewsSound x ∧ Synchronized x ∧ Synchrony Q.gst Q.delta x ∧
    Relay Q.gst Q.delta x ∧ AdvanceFair x ∧ TickFair x

end Params

end Majorum

/-! ## TOB-SVD -/

namespace TobSvd

/-- Parameters of the `(Tb, Ts, ρ)`-sleepy model. -/
structure Params where
  /-- Synchronous delay bound. -/
  delta : Round
  /-- Backward-simulation window: Byzantine validators are counted `Tb` ahead. -/
  Tb : Round
  /-- Stabilization period: honest validators must be awake throughout `Ts`. -/
  Ts : Round
  /-- Failure ratio of Byzantine to active validators. -/
  rho : ℚ
  /-- `ρ ≤ 1/2`. -/
  rhoLe : rho ≤ 1 / 2

namespace Params

variable (Q : Params)

/-- The set the compliance ratio is taken over: `H_{t−Ts,t} ∪ B_{t+Tb}` — honest
    validators awake *throughout* `[t−Ts, t]`, plus those Byzantine by `t+Tb`.

    The paper calls these the "active" validators, but that is a *counting* set
    for Condition (1) and has nothing to do with permission to act — TOB-SVD has
    no joining protocol, so permission to act is just `ActiveEqAwake`. Renamed
    here to keep the two apart. -/
def counted (S : Schedule V) (t : Int) : Finset V :=
  S.awakeThroughout (t - (Q.Ts : Int)) t ∪ S.adv (t + (Q.Tb : Int))

/-- Condition (1): `|B_{t+Tb}| < ρ · |H_{t−Ts,t} ∪ B_{t+Tb}|` for every `t ≥ 0`. -/
def Compliant (S : Schedule V) : Prop :=
  ∀ t : Int, 0 ≤ t →
    ((S.adv (t + (Q.Tb : Int))).card : ℚ) < Q.rho * ((Q.counted S t).card : ℚ)

/-- The model. `Synchrony 0` is the synchronous network: TOB-SVD assumes a delay
    bound Δ from the start, with no GST. -/
def Model {Pr : Protocol V Msg State Ev} {S : Schedule V}
    (x : Exec Pr S) : Prop :=
  S.MonotoneCorruption ∧ S.AwakeHonest ∧ Q.Compliant S ∧
    ViewsSound x ∧ Synchronized x ∧ Synchrony 0 Q.delta x ∧
    Relay 0 Q.delta x ∧ AdvanceFair x ∧ TickFair x

end Params

end TobSvd

end Framework.Sts2D.Models
