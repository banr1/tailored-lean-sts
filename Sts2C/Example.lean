import Mathlib.Tactic.NormNum
import Framework.Sts2C.Models

/-!
# A worked example

The smallest thing that exercises the whole framework: a toy protocol, a
schedule, and the *same* protocol placed under both Majorum's and TOB-SVD's
models. It exists to show what a specialization has to supply — and, since it
compiles, that the parameterisation actually fits together.

Read it as the answer to "how do I use this?":

1. pick `Node`, `Msg`, `NodeState` and write a `Protocol` (`init` and `step`);
2. pick a `Schedule` — who is corrupted, who is awake, at each time;
3. `system`/`Exec` then give you the transition system and its executions;
4. state which model's assumptions you are working under.
-/

set_option autoImplicit false

namespace Framework.Sts2C.Example

/-! ## 1. A protocol -/

/-- Four validators. -/
abbrev Node := Fin 4

/-- One message: a validator announces a number. -/
inductive Msg where
  /-- "I am validator `k`." -/
  | announce (k : Nat)
  deriving DecidableEq

/-- What a validator remembers: the numbers it has heard announced. No "have I
    spoken?" flag is needed — `Step.clock` ticks each active validator exactly
    once per round, so a `tick` reaction cannot be run twice for the same round. -/
structure St where
  /-- The numbers it has heard announced. -/
  heard : Finset Nat
  deriving DecidableEq

/-- The number carried by a signed message. -/
def announced (m : SignedMsg Node Msg) : Nat :=
  match m.msg with
  | .announce k => k

/-- Announce your own index at round 0, and record each announcement as it arrives.

    Written as a **function**, then lifted into `Protocol.step`, which is a relation
    so that honest behaviour *may* be nondeterministic. A deterministic protocol like
    this one lifts with `res = reaction …`, which keeps it computable — the `decide`
    checks below run on this function. -/
def reaction (p : Node) (r : Time) (_view : View Node Msg) (s : St) :
    Event Node Msg Empty → NodeStepResult St Msg
  | .tick =>
      if r = 0 then { state := s, send := {Msg.announce p.val} }
      else { state := s, send := ∅ }
  | .recv m => { state := { s with heard := insert (announced m) s.heard }, send := ∅ }
  | .wake => { state := s, send := ∅ }
  | .custom ev => ev.elim

/-- `Ev := Empty` because this protocol has no events of its own — a protocol with
    timers would put them there and constrain them via `enabled`. -/
def proto : Protocol Node Msg St Empty where
  init _ := { heard := ∅ }
  step p r view s e res := res = reaction p r view s e
  total _ _ _ _ _ := ⟨_, rfl⟩
  enabled _ _ ev := ev.elim

/-- It really runs: validator 2 announces itself when ticked at round 0. -/
example : (reaction 2 0 ∅ (proto.init 2) .tick).send = {Msg.announce 2} := by
  decide

/-- And stays quiet at later rounds. -/
example : (reaction 2 1 ∅ (proto.init 2) .tick).send = ∅ := by decide

/-- And it reacts to an *arrival*, which is what `recv` carrying the message
    buys: the reaction needs no scan of the view. -/
example :
    (reaction 2 1 ∅ (proto.init 2) (.recv ⟨1, .announce 1⟩)).state.heard
      = {1} := by decide

/-! ## 2. Schedules — what the adversary does

A schedule fixes, per round, who is corrupted and who is awake. That is *all* the
adversary controls: whether a just-woken validator delays participating is its
own program's business, so nothing here corresponds to being "active".

The `Int` index is why the below-zero convention belongs to the schedule: here we
say "awake at every time, including negative", which is TOB-SVD's convention;
Majorum instead wants `∅` before round 0. -/

/-- Nobody is ever corrupted and nobody ever sleeps. -/
def noFaults : Schedule Node where
  adv := fun _ => ∅
  awake := fun _ => Finset.univ

/-- Validator 3 sleeps until round 10. -/
def threeSleeps : Schedule Node where
  adv := fun _ => ∅
  awake := fun r => if r < 10 then {0, 1, 2} else Finset.univ

/-- While asleep it is owed nothing… -/
example : threeSleeps.awake 5 = {0, 1, 2} := by decide

/-- …and from the round it wakes, `Synchrony` obliges it to hold everything sent
    Δ ago — which is exactly "on waking it receives all messages it should have
    received while asleep". A protocol that must then delay *sending* implements
    that itself, starting from the `wake` event. -/
example : threeSleeps.awake 10 = Finset.univ := by decide

/-! ## 3 & 4. The system, its executions, and a model

The same `proto` under both models — the parameterisation earning its keep. -/

/-- TOB-SVD: synchronous, Δ = 1, no backward-simulation window, ρ = 1/2. -/
def tob : Models.TobSvd.Params where
  delta := 1
  Tb := 0
  Ts := 0
  rho := 1 / 2
  rhoLe := by norm_num

/-- Executions of `proto` under a schedule with no faults or sleep. -/
abbrev TobExec := Exec proto noFaults

/-- What it means for one of them to satisfy TOB-SVD's model. -/
def TobCompliant (x : TobExec) : Prop := tob.Model x

/-- Majorum: `n = 4`, `f = 1`, Δ = 1, and (for simplicity) GST = GAT = 0. -/
def maj : Models.Majorum.Params where
  n := 4
  f := 1
  delta := 1
  gst := 0
  gat := 0
  fBound := by decide
  deltaPos := by decide

/-- Executions of the *same* protocol, to be read under Majorum's model. The
    execution type no longer mentions the model at all — participation moved into
    the schedule — so the two models differ purely in what they *assume*. -/
abbrev MajExec := Exec proto noFaults

/-- What it means for one of them to satisfy Majorum's model. -/
def MajCompliant (x : MajExec) : Prop := maj.Model x

/-- A property one would eventually prove, stated with the framework's
    vocabulary: under TOB-SVD's model, every active validator has heard every
    honest announcement. Left unproved on purpose — the framework carries no
    proofs while its structure is still moving. -/
def EveryoneHeardEveryone (x : TobExec) : Prop :=
  TobCompliant x →
    ∀ (i : Nat) (p q : Node), 1 ≤ x[i].time →
      x.Awake i p →
      (⟨q, .announce q.val⟩ : SignedMsg Node Msg) ∈ x[i].sent →
      q.val ∈ x[i][p].st.heard

end Framework.Sts2C.Example
