import the framework's flat multiset-log flavour

/-!
# Majorum's assumptions, à la carte

Majorum does **not** prove its theorems under one set of assumptions, so there is no single
`Model` predicate here. Accountable safety is the extreme case: Theorem 5, arXiv:2601.03862v1 and
its lemmas
open with `Assume $f \in [0,n]$`, explicitly overriding the paper's standing `f < n/3`, and
the section preamble calls the finalized chain "always Accountably Safe". Handing it a synchrony
assumption and a corruption bound would turn the paper's strongest claim into a much weaker
one.

So the assumptions are named groups, and each theorem in `Theorems.lean` cites exactly the
ones the paper gives it. This is what `the framework's flat multiset-log flavour.Execution` is arranged for — its
predicates are à la carte precisely so that a paper's model is whichever conjunction it
assumes. `the framework's flat multiset-log flavour.Models.Majorum.Params.Model` is a *different* thing: the
convenience conjunction used to check that the framework can express Majorum's model at
all.

## Self-contained

Nothing here imports `the framework's flat multiset-log flavour.Models`. That module exists to show the framework can
*express* Majorum's model; this one states the parameters Majorum's *claims* are made over,
and they should be free to diverge. It also fixes a concrete problem: the framework's
`Params` carries `fBound : 3 * f < n` as a field, so merely taking one assumes `f < n/3` —
which Theorem 5 does not, being proved for `f ∈ [0,n]`. Here that bound is a conjunct of
`Resilience`, so a theorem that does not assume it does not mention it.
-/

set_option autoImplicit false

namespace Majorum

open the framework's flat multiset-log flavour

variable {Node Msg NodeState Ev : Type} [Fintype Node] [DecidableEq Node] [DecidableEq Msg]
  {Pr : Protocol Node Msg NodeState Ev} {S : Schedule Node}

/-- Majorum's parameters, from the model section.

    Local to this directory rather than reused from `the framework's flat multiset-log flavour.Models.Majorum.Params`.
    Two reasons. The framework's bundle exists to demonstrate that the framework *can*
    express Majorum's model; these are the parameters its *claims* are stated over, and the
    two should be free to diverge. And the framework's carries `fBound : 3 * f < n` as a
    field, which makes Theorem 5 unstateable, since the paper proves it for `f ∈ [0,n]`. Here
    the bound lives in `Resilience`, so a theorem that does not assume it simply does not
    take it. -/
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
  /-- Slots are `4Δ` rounds, so `Δ` must be positive. -/
  deltaPos : 0 < delta

namespace Params

variable (Q : Params)

/-- Slots are `4Δ` rounds. -/
def slotLength : Time := 4 * Q.delta

/-- `proposing(t) = 4Δt`, the first round of slot `t`. Slots are `Int` here, unlike the
    framework's `Nat` version: subtraction then never truncates, which is what lets
    `Sleepiness` below range over every slot with no re-indexing. -/
def proposing (t : Int) : Int := (Q.slotLength : Int) * t

/-- `voting(t) = 4Δt + Δ`. -/
def voting (t : Int) : Int := (Q.slotLength : Int) * t + (Q.delta : Int)

end Params

/-- What makes `x` an execution of this system at all, as opposed to a network or adversary
    assumption: corruption is monotone, the awake are the ones who act, clocks agree with
    real time and never read the future, time diverges, and every awake validator acts at
    every round.

    Assumed by every theorem below. Whether accountable safety needs even this is an open
    question worth answering rather than assuming — see `Theorems.lean`. -/
def Wellformed (x : Exec Pr S) : Prop :=
  S.MonotoneCorruption ∧ S.AwakeHonest ∧
    SynchronizedClocks x ∧ TimeMonotone x ∧ ClocksSound x ∧ TimeDiverges x ∧ Diligent x

/-- Partial synchrony after GST, and honest gossip. Majorum makes relay part of the model —
    "once an adversarial message is received by an honest validator, it is also gossiped by
    it" — so it belongs here rather than in the protocol. -/
def Network (Q : Params) (x : Exec Pr S) : Prop :=
  Synchrony Q.gst Q.delta x ∧ Relay Q.gst Q.delta x

/-- The synchronous case, `GST = 0`, which the dynamic-availability analysis assumes
    (arXiv:2601.03862v1, the FFG analysis preamble: "throughout this part of the analysis, we
    assume `GST = 0`"). Note it is *not* `Network` at `Q.gst = 0`: the parameter is fixed by
    `Q`, so this says the bound holds from the start regardless of what `Q.gst` is. -/
def Synchronous (Q : Params) (x : Exec Pr S) : Prop :=
  Synchrony 0 Q.delta x ∧ Relay 0 Q.delta x

/-- The validators **active** at slot `t`, in Majorum's sense.

    The paper's `H_r` is the set of validators *active* at round `r`, which is not the set
    awake at `r`: a validator that has woken but not finished the joining protocol is awake
        and not yet active. The joining protocol (`arXiv:2601.03862v1, "Joining Protocol"`) says a
    validator waking in
    `(voting(t-2)+Δ, voting(t-1)+Δ]` "sends nothing until round `voting(t)`, when it becomes
    active". So to be active at `voting(t)` a validator must have woken by `voting(t-1)+Δ`
    and stayed awake since:

        Active t = awakeThroughout (voting(t-1) + Δ) (voting t)

    Written with `voting t - 3Δ` for the lower end, since `voting(t-1) + Δ = voting t - 4Δ +
    Δ`. That is not cosmetic: it is `Int` subtraction, so there is no `Nat` truncation and no
    `1 ≤ t` guard.

    Caveat at `t = 0`, where the window reaches back to `-2Δ`. The schedule is total on `ℤ`,
    so this is well defined but does not implement the paper's `H_i := ∅` convention for
        `i < 0` (`arXiv:2601.03862v1, the `H_i := ∅ if i < 0` convention`); it is *weaker* than
    that convention, which would make `Active 0`
    empty. Nothing below depends on `Active 0`, since `Sleepiness` starts its constraint at
    slot 1. -/
def Active (Q : Params) (S : Schedule Node) (t : Int) : Finset Node :=
  S.awakeThroughout (Q.voting t - 3 * (Q.delta : Int)) (Q.voting t)

/-- **Constraint (1)** (`Constraint (1), arXiv:2601.03862v1 p.4`), the sleepiness bound:

        |H_{voting(t-1)} \ A_{voting t}| > |A_{voting t}|   for every slot t after GST

    "The number of validators active at round `voting(t-1)` and not corrupted by
    `voting(t)` must exceed the sum of adversarial validators at `voting(t)`." Its purpose
        (`arXiv:2601.03862v1, the paragraph after Constraint (1)`) is to bound how many honest
    validators the adversary may corrupt after
    slot `t-1`'s voting phase but before those votes are tallied.

    Two differences from `the framework's flat multiset-log flavour.Models.Majorum.Params.Compliant`, which this
    supersedes — nothing here calls it:

    1. **`Active` is named.** `Compliant` inlined the same window, so it read as though the
       joining protocol were part of the sleepiness bound. It is not: `H` is the active set,
       the joining protocol is what determines it, and the constraint is a statement about
       `H`. Separating them makes the constraint the paper's one line again.
    2. **Every slot, no `2 ≤ t` guard.** Slots are `Int`, so `t - 1` does not truncate and
       the constraint reads at slot `t` exactly as the paper writes it. `Compliant` needed
       the guard because `t - 2` truncates in `Nat`.

    The paper's `H_i := ∅` convention for `i < 0` is not implemented, so at slot `0` and
    below `Active` reads the schedule at negative rounds instead of being empty. That makes
    the constraint *harder* to satisfy there, not vacuous — the opposite failure to the one
    worth fearing. -/
def Sleepiness (Q : Params) (S : Schedule Node) : Prop :=
  ∀ t : Int, (Q.gst : Int) ≤ Q.proposing t →
    (S.adv (Q.voting t)).card < (Active Q S (t - 1) \ S.adv (Q.voting t)).card

/-- Every validator is awake from GAT on. Needed by liveness, which is stated after
    `max(GST, GAT)`. -/
def GlobalAwake (Q : Params) (S : Schedule Node) : Prop :=
  S.GlobalAwakeTime Q.gat Finset.univ

/-- The corruption budget is respected, **and** `f < n/3`. Both belong here rather than in
    `Params`: Theorem 5 assumes neither, and a structure field would force it to. -/
def Resilience (Q : Params) (S : Schedule Node) : Prop :=
  S.CorruptionBounded Q.f ∧ 3 * Q.f < Q.n

end Majorum
