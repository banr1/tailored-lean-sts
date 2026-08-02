import the framework's flat multiset-log flavour

/-!
# Majorum's assumptions, à la carte

Majorum does **not** prove its theorems under one set of assumptions, so there is no single
`Model` predicate here. Accountable safety is the extreme case: the paper's source line 983 and `:1026`
open with `Assume $f \in [0,n]$`, explicitly overriding the paper's standing `f < n/3`, and
`:1298` calls the finalized chain "always Accountably Safe". Handing it a synchrony
assumption and a corruption bound would turn the paper's strongest claim into a much weaker
one.

So the assumptions are named groups, and each theorem in `Theorems.lean` cites exactly the
ones the paper gives it. This is what `the framework's flat multiset-log flavour.Execution` is arranged for — its
predicates are à la carte precisely so that a paper's model is whichever conjunction it
assumes. `the framework's flat multiset-log flavour.Models.Majorum.Params.Model` is a *different* thing: the
convenience conjunction used to check that the framework can express Majorum's model at
all.

## One parameter bundle does not fit all seven

`Models.Majorum.Params` carries `fBound : 3 * f < n` as a **field**, so any statement taking
a `Params` has assumed `f < n/3` before it says anything. That is right for six of the seven
theorems and wrong for accountable safety — which therefore takes no `Params` at all, and
needs none, since it mentions no round, slot or delay. If a future statement needs Majorum's
timing vocabulary *without* the corruption bound, `Params` will have to be split.
-/

set_option autoImplicit false

namespace Majorum

open the framework's flat multiset-log flavour the framework's flat multiset-log flavour.Models

variable {Node Msg NodeState Ev : Type} [Fintype Node] [DecidableEq Node] [DecidableEq Msg]
  {Pr : Protocol Node Msg NodeState Ev} {S : Schedule Node}

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
def Network (Q : Majorum.Params) (x : Exec Pr S) : Prop :=
  Synchrony Q.gst Q.delta x ∧ Relay Q.gst Q.delta x

/-- The synchronous case, `GST = 0`, which the dynamic-availability analysis assumes
    (the paper's source line 1045, "throughout this part of the analysis, we assume `GST = 0`"). Note it
    is *not* `Network` at `Q.gst = 0`: the parameter is fixed by `Q`, so this says the bound
    holds from the start regardless of what `Q.gst` is. -/
def Synchronous (Q : Majorum.Params) (x : Exec Pr S) : Prop :=
  Synchrony 0 Q.delta x ∧ Relay 0 Q.delta x

/-- Constraint (1), the sleepiness bound: in each slot after GST the adversary is smaller
    than the honest validators awake throughout the preceding slot. -/
def Sleepiness (Q : Majorum.Params) (S : Schedule Node) : Prop :=
  Q.Compliant S

/-- Every validator is awake from GAT on. Needed by liveness, which is stated after
    `max(GST, GAT)`. -/
def GlobalAwake (Q : Majorum.Params) (S : Schedule Node) : Prop :=
  S.GlobalAwakeTime Q.gat Finset.univ

/-- The corruption budget is respected. `f < n/3` itself is `Q.fBound`, a field of `Params`
    — see the module docstring for why that is a problem for exactly one theorem. -/
def Resilience (Q : Majorum.Params) (S : Schedule Node) : Prop :=
  S.CorruptionBounded Q.f

end Majorum
