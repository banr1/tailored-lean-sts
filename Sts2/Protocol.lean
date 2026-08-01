import Mathlib.Data.Set.Image
import Framework.Sts2.System
import Framework.Sts2.Schedule

/-!
# Protocols and the system they induce

A protocol reacts to **events**, and to nothing else. The framework generates
exactly the events it knows about — `tick` (this validator's clock advanced),
`recv m` (a message was delivered, and is already in the view), `wake` (it just
came back from sleep) — while every other trigger goes through `custom`, whose
type `Ev` is the protocol's own, gated by `Protocol.enabled`.

## Time is deliberately weak

Two separations, so that a property need assume only the time discipline it
actually depends on:

* **Time passing and validators acting are different transitions.**
  `Step.advance` moves real time; `Step.tick p` is one validator reacting. So a
  proof about the message history alone never has to reason about the clock — under
  the earlier design, where advancing the round also ran every awake validator,
  that was impossible. It also makes "time passes while nobody acts" expressible,
  which asynchrony needs.
* **Each validator reads its own clock**, `Config.clock p`, and that is the round
  handed to `step`. `Config.time` is *real* time, read only by the environment: the
  schedule, the network bound, GST. So clocks being synchronized is an
  **assumption** (`Execution.Synchronized`) rather than a fact of the model, and
  monotonicity is free, since `Step.tick` only increments.

The guard `c.clock p < c.time` on `Step.tick` stops a clock running ahead of real
time and gives exactly one tick per validator per round, so a `tick` reaction still
need not be idempotent.

Two consequences worth knowing. A round is no longer simultaneous: tick reactions
interleave, so one validator may see another's message from the same round — which
is strictly more general, and since delivery was always its own transition, rounds
were never really lock-step. And a validator asleep across several rounds wakes with
a *stale* clock, which it can only advance one tick at a time; `Synchronized` is
what rules that out where a model wants it.

Who is awake and who is corrupted come from the `Schedule`: the adversary's fixed
choices over an execution, not transitions. Timing assumptions are likewise
predicates on executions (`Framework.Sts2.Execution`), so different models impose
different ones over the same step relation.

## Iterations of this interface

1. `Event = start | recv | timeout` with an `EventEnabled` predicate — a fiction of
   generality: it fixed the vocabulary and let `start` fire repeatedly.
2. No events; `step` read only the accumulated view — per-arrival reactions and
   arrival order became inexpressible.
3. Framework events plus a protocol-supplied `Ev`, with advancing the round *being*
   the tick of every awake validator — which welded time to acting.
4. Current: as (3), but time and acting are separate transitions and clocks are
   per-validator.
-/

set_option autoImplicit false

namespace Framework.Sts2

variable {V Msg State Ev : Type}

/-- What a protocol reacts to. `Ev` is the protocol's own event type; use `Empty`
    if it has none. -/
inductive Event (V Msg Ev : Type) where
  /-- This validator's clock advanced. -/
  | tick
  /-- A message was delivered; it is already in the view. -/
  | recv (m : SignedMsg V Msg)
  /-- This validator has just woken from sleep. A protocol whose correctness
      depends on delaying participation after waking — Majorum's joining protocol
      — implements that itself, starting here. -/
  | wake
  /-- A protocol-specific event — a timer firing, say. -/
  | custom (ev : Ev)

/-- The result of one reaction: the new state and the messages sent (broadcast;
    the network decides who receives them and when). -/
structure Effect (State Msg : Type) where
  /-- State afterwards. -/
  state : State
  /-- Messages sent, each signed by the reacting validator. -/
  send : Finset Msg

/-- A protocol. -/
structure Protocol (V Msg State Ev : Type) where
  /-- Initial state of each validator. -/
  init : V → State
  /-- `step p r view s e` — how `p` reacts to `e`, where `r` is **`p`'s own clock
      reading**, not real time. -/
  step : V → Round → View V Msg → State → Event V Msg Ev → Effect State Msg
  /-- When a protocol-specific event may fire, also against the local clock. -/
  enabled : Round → State → Ev → Prop

/-- A global configuration. -/
structure Config (V Msg State : Type) where
  /-- Real time. Read by the environment — schedule, network bound, GST — and
      never handed to a protocol. -/
  time : Round
  /-- Each validator's own clock reading. Advanced only by `Step.tick`. -/
  clock : V → Round
  /-- Each validator's protocol state. -/
  st : V → State
  /-- Each validator's view: everything delivered to it so far. -/
  view : V → View V Msg
  /-- Every message ever signed. Monotone. -/
  sent : Set (SignedMsg V Msg)

variable [DecidableEq V] [DecidableEq Msg]

/-- File a delivered message into `p`'s view, without reacting to it. -/
def receive (p : V) (m : SignedMsg V Msg) (c : Config V Msg State) :
    Config V Msg State :=
  { c with view := fun q => if q = p then insert m (c.view q) else c.view q }

/-- Run `p`'s reaction to `e` against its own clock: install the new state, and add
    what it sent to the network signed by `p`.

    Sends are *not* filtered here. A just-woken Majorum validator "receives all
    queued messages and resumes execution, but sends nothing until round
    `voting(t)`" — and it achieves that by returning `send := ∅` from its own
    `step`. -/
def react (Pr : Protocol V Msg State Ev) (p : V) (e : Event V Msg Ev)
    (c : Config V Msg State) : Config V Msg State :=
  { c with
      st := fun q =>
        if q = p then (Pr.step p (c.clock p) (c.view p) (c.st p) e).state
        else c.st q
      sent := c.sent ∪
        (SignedMsg.mk p ''
          ((Pr.step p (c.clock p) (c.view p) (c.st p) e).send : Set Msg)) }

/-- Transition labels. -/
inductive Action (V Msg Ev : Type) where
  /-- Real time advances; no validator acts. -/
  | advance
  /-- `p`'s clock catches up by one, and `p` reacts. -/
  | tick (p : V)
  /-- `m` is delivered to `p`, which reacts to it. -/
  | deliver (p : V) (m : SignedMsg V Msg)
  /-- `p` wakes up. -/
  | wake (p : V)
  /-- A protocol-specific event fires at `p`. -/
  | custom (p : V) (ev : Ev)
  /-- An adversarial validator signs an arbitrary message. -/
  | adversarial (p : V) (m : Msg)

/-- The step relation. *When* messages must be delivered, and whether clocks agree
    with real time, are properties of the model, imposed on executions. -/
inductive Step (V Msg State Ev : Type) [DecidableEq V] [DecidableEq Msg]
    (Pr : Protocol V Msg State Ev) (S : Schedule V) :
    Action V Msg Ev → Config V Msg State → Config V Msg State → Prop where
  /-- Real time advances, on its own. Always enabled, so no configuration is
      stuck. -/
  | advance {c : Config V Msg State} :
      Step V Msg State Ev Pr S .advance c { c with time := c.time + 1 }
  /-- An awake validator whose clock is behind real time advances it by one and
      reacts. -/
  | tick {c : Config V Msg State} {p : V} :
      p ∈ S.awake (c.time : Int) → c.clock p < c.time →
      Step V Msg State Ev Pr S (.tick p) c
        (react Pr p .tick
          { c with clock := fun q => if q = p then c.clock q + 1 else c.clock q })
  /-- Any sent message may be delivered to any awake validator, at any time.
      Delivery to a sleeping validator is simply not a transition, which is how
      messages get queued: they stay in `sent` until it wakes. The message is filed
      before the reaction runs, so `step` sees it in the view too. -/
  | deliver {c : Config V Msg State} {p : V} {m : SignedMsg V Msg} :
      m ∈ c.sent → p ∈ S.awake (c.time : Int) →
      Step V Msg State Ev Pr S (.deliver p m) c
        (react Pr p (.recv m) (receive p m c))
  /-- `p` has just woken: awake now, asleep in the previous round. The framework
      reports this because a protocol cannot start a joining procedure it is not
      told about. -/
  | wake {c : Config V Msg State} {p : V} :
      p ∈ S.awake (c.time : Int) → p ∉ S.awake ((c.time : Int) - 1) →
      Step V Msg State Ev Pr S (.wake p) c (react Pr p .wake c)
  /-- A protocol-specific event fires, if the protocol allows it at the
      validator's own clock reading. -/
  | custom {c : Config V Msg State} {p : V} {ev : Ev} :
      p ∈ S.awake (c.time : Int) → Pr.enabled (c.clock p) (c.st p) ev →
      Step V Msg State Ev Pr S (.custom p ev) c (react Pr p (.custom ev) c)
  /-- An adversarial validator signs anything. -/
  | adversarial {c : Config V Msg State} {p : V} {m : Msg} :
      p ∈ S.adv (c.time : Int) →
      Step V Msg State Ev Pr S (.adversarial p m) c
        { c with sent := insert ⟨p, m⟩ c.sent }

/-- Initial configurations. -/
def Init (Pr : Protocol V Msg State Ev) (c : Config V Msg State) : Prop :=
  c.time = 0 ∧ (∀ p, c.clock p = 0) ∧ (∀ p, c.st p = Pr.init p) ∧
    (∀ p, c.view p = ∅) ∧ c.sent = ∅

/-- The protocol as a transition system. -/
def system (V Msg State Ev : Type) [DecidableEq V] [DecidableEq Msg]
    (Pr : Protocol V Msg State Ev) (S : Schedule V) :
    System (Config V Msg State) (Action V Msg Ev) where
  Init := Init Pr
  Step := Step V Msg State Ev Pr S

end Framework.Sts2
