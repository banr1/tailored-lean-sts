import Mathlib.Data.Rat.Defs
import StsMultisetLog.Spec.Execution

/-!
# Two models, expressed — example scaffolding

Two paper models assembled out of the framework's à-la-carte predicates, so that
`Examples.Example` can place a toy protocol under both.

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

## This is **not** the authoritative statement of either model

It reads as though it were, and it is not — which is why it sits under `Examples/`.

`Majorum.Params.Compliant` has two known defects as a statement of the paper's assumption. It
inlines the joining window into the sleepiness constraint instead of naming an `Active`
predicate, so the constraint reads as though joining were part of the bound. And it indexes
slots by `Nat`, which forces a `2 ≤ t` condition — only because `t - 2` truncates — where an
`Int` indexing holds at every slot with no such condition. The `Params` here also carry `n` and
`fBound`, which a protocol stating this assumption need not have. **A protocol built on this
framework should state its own assumptions, and read the paper, not this file.**

The original claim here was that stating both models "validates the parameterisation by use
rather than asserting it: if either stops being expressible, this file stops compiling." That
does not hold. Compilation only confirms that *something named* `Compliant` typechecks — it
stayed green throughout being replaced by a better statement elsewhere. What validates the
parameterisation is a protocol actually built on the framework, not this file.

## What it is still good for

It is the only place both interval operators — `awakeSomewhere` and `awakeThroughout` — are
used, so the framework's claim to privilege neither is checked here. And putting
`MonotoneCorruption`, `AwakeHonest`, `CorruptionBounded`, `GlobalAwakeTime`,
`SynchronizedClocks`, `Synchrony`, `Relay`, `TimeMonotone`, `ClocksSound`, `TimeDiverges` and
`Diligent` into two plausible whole models is a smoke test that the à-la-carte predicates
compose. That is worth a file; it is not worth being mistaken for the paper.
-/

set_option autoImplicit false

namespace Framework.StsMultisetLog.Models

variable {Node Msg NodeState Ev : Type} [Fintype Node] [DecidableEq Node] [DecidableEq Msg]

/-! ## Majorum -/

namespace Majorum

/-- Parameters of Majorum's model. -/
structure Params where
  /-- Number of validators. -/
  n : Nat
  /-- Corruption budget, `f = |A_∞|`. -/
  f : Nat
  /-- Message delay bound after GST. -/
  delta : Time
  /-- Global stabilization time. -/
  gst : Time
  /-- Global awake time. -/
  gat : Time
  /-- `f < n/3`. -/
  fBound : 3 * f < n
  /-- Slots are `4Δ` rounds, so Δ must be positive. -/
  deltaPos : 0 < delta

namespace Params

variable (Q : Params)

/-- Rounds per slot: `4Δ`. -/
def slotLength : Nat := 4 * Q.delta

/-- First round of slot `t`, where proposals happen. -/
def proposing (t : Nat) : Time := Q.slotLength * t

/-- The voting round of slot `t`: `4Δt + Δ`. -/
def voting (t : Nat) : Time := Q.slotLength * t + Q.delta

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

    Requires `2 ≤ t` so `t - 2` is genuine subtraction rather than `Nat`
    truncation, and by `proposing t` rather than `voting t` — "every slot after
    GST" means the slot *starts* after GST. -/
def Compliant (S : Schedule Node) : Prop :=
  ∀ t : Nat, 2 ≤ t → Q.gst ≤ Q.proposing t →
    (S.adv ((Q.voting t : Int))).card <
      ((S.awakeThroughout ((Q.voting (t - 2) : Int) + (Q.delta : Int))
          ((Q.voting (t - 1) : Int))) \ S.adv ((Q.voting t : Int))).card

/-- The model: everything Majorum assumes of an execution. -/
def Model {Pr : Protocol Node Msg NodeState Ev} {S : Schedule Node}
    (x : Exec Pr S) : Prop :=
  S.MonotoneCorruption ∧ S.AwakeHonest ∧ S.CorruptionBounded Q.f ∧
    S.GlobalAwakeTime Q.gat Finset.univ ∧ Q.Compliant S ∧
    SynchronizedClocks x ∧ Synchrony Q.gst Q.delta x ∧
    Relay Q.gst Q.delta x ∧
    TimeMonotone x ∧ ClocksSound x ∧ TimeDiverges x ∧ Diligent x

end Params

end Majorum

/-! ## TOB-SVD -/

namespace TobSvd

/-- Parameters of the `(Tb, Ts, ρ)`-sleepy model. -/
structure Params where
  /-- Synchronous delay bound. -/
  delta : Time
  /-- Backward-simulation window: Byzantine validators are counted `Tb` ahead. -/
  Tb : Time
  /-- Stabilization period: honest validators must be awake throughout `Ts`. -/
  Ts : Time
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
def counted (S : Schedule Node) (t : Int) : Finset Node :=
  S.awakeThroughout (t - (Q.Ts : Int)) t ∪ S.adv (t + (Q.Tb : Int))

/-- Condition (1): `|B_{t+Tb}| < ρ · |H_{t−Ts,t} ∪ B_{t+Tb}|` for every `t ≥ 0`. -/
def Compliant (S : Schedule Node) : Prop :=
  ∀ t : Int, 0 ≤ t →
    ((S.adv (t + (Q.Tb : Int))).card : ℚ) < Q.rho * ((Q.counted S t).card : ℚ)

/-- The model. `Synchrony 0` is the synchronous network: TOB-SVD assumes a delay
    bound Δ from the start, with no GST. -/
def Model {Pr : Protocol Node Msg NodeState Ev} {S : Schedule Node}
    (x : Exec Pr S) : Prop :=
  S.MonotoneCorruption ∧ S.AwakeHonest ∧ Q.Compliant S ∧
    SynchronizedClocks x ∧ Synchrony 0 Q.delta x ∧
    Relay 0 Q.delta x ∧
    TimeMonotone x ∧ ClocksSound x ∧ TimeDiverges x ∧ Diligent x

end Params

end TobSvd

end Framework.StsMultisetLog.Models
