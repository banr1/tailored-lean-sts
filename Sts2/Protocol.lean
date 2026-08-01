import Mathlib.Data.Set.Image
import Common.System
import Framework.Sts2.Schedule

/-!
# Protocols and the system they induce

A protocol reacts to **events**, and to nothing else. The framework generates
exactly the two events it actually knows about:

* `tick` — the round advanced;
* `recv m` — a message was delivered (and is already in the view when `step`
  runs, so a protocol can work from either the arrival or the accumulated view);

and every other trigger a protocol wants — timers, view changes, client input —
goes through `custom`, whose type `Ev` is the protocol's own; `Protocol.enabled`
says when one may fire, so a timer is a `custom` event enabled once the round
reaches its deadline.

Advancing the round *is* delivering `tick` to every active validator — one
transition (`Step.clock`), not two, so the clock and the notifications cannot
drift apart.

This is the third iteration of this interface. The first fixed the vocabulary at
`start | recv | timeout`, which was a fiction of generality. The second dropped
events entirely and let `step` read only the view, which made per-arrival
reactions and arrival order inexpressible. This version keeps the framework's own
events and makes the rest a parameter.

Who is awake, who is active, who is corrupted, and when, all come from the
`Schedule` — those
are not transitions, because in both papers they are the adversary's fixed
choices over an execution. Timing assumptions are likewise not step guards but
predicates on executions (`Framework.Sts2.Execution`), so that different models
can impose different ones over the same step relation.
-/

set_option autoImplicit false

namespace Framework.Sts2

open Common (System)

variable {V Msg State Ev : Type}

/-- What a protocol reacts to. `Ev` is the protocol's own event type; use `Empty`
    if it has none. -/
inductive Event (V Msg Ev : Type) where
  /-- The round advanced. -/
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
  /-- `step p r view s e` — how `p` reacts to `e` at round `r` with view `view`. -/
  step : V → Round → View V Msg → State → Event V Msg Ev → Effect State Msg
  /-- When a protocol-specific event may fire. A timer is `fun r s ev => …` with
      a condition on `r`; `fun _ _ _ => True` leaves them unconstrained. -/
  enabled : Round → State → Ev → Prop

/-- A global configuration. -/
structure Config (V Msg State : Type) where
  /-- The current round. Clocks are synchronized in both papers, so a single
      global round is faithful. -/
  now : Round
  /-- Each validator's protocol state. -/
  st : V → State
  /-- Each validator's view: everything delivered to it so far. -/
  view : V → View V Msg
  /-- Every message ever signed. Monotone; timing is read off the execution. -/
  sent : Set (SignedMsg V Msg)

variable [DecidableEq V] [DecidableEq Msg]

/-- File a delivered message into `p`'s view, without reacting to it. -/
def receive (p : V) (m : SignedMsg V Msg) (c : Config V Msg State) :
    Config V Msg State :=
  { c with view := fun q => if q = p then insert m (c.view q) else c.view q }

/-- Run `p`'s reaction to `e`: install its new state and add what it sent to the
    network, signed by `p`.

    Sends are *not* filtered here. A just-woken Majorum validator "receives all
    queued messages and resumes execution, but sends nothing until round
    `voting(t)`" — and it achieves that by returning `send := ∅` from its own
    `step`, not by the framework gagging it. -/
def react (Pr : Protocol V Msg State Ev) (p : V) (e : Event V Msg Ev)
    (c : Config V Msg State) : Config V Msg State :=
  { c with
      st := fun q => if q = p then (Pr.step p c.now (c.view p) (c.st p) e).state
                     else c.st q
      sent := c.sent ∪
        (SignedMsg.mk p '' ((Pr.step p c.now (c.view p) (c.st p) e).send : Set Msg)) }

/-- Advance the round, letting every active validator react to `.tick`.

    One transition rather than two — a separate "advance the clock" and "notify a
    validator" cannot be kept in correspondence: nothing would stop a validator
    being ticked twice in a round, or not at all. Here exactly one tick per
    active validator per round holds by construction, so a `tick` reaction need
    not be idempotent and no fairness assumption is needed to force it.

    All reactions read the *old* configuration, so the round is simultaneous: no
    validator sees another's reaction to the same tick. Their messages become
    deliverable from the next round on.

    Every awake validator is ticked; a validator asleep at `c.now` is not. -/
def tickAll (Pr : Protocol V Msg State Ev) (S : Schedule V)
    (c : Config V Msg State) : Config V Msg State where
  now := c.now + 1
  view := c.view
  st := fun q =>
    if q ∈ S.awake (c.now : Int)
    then (Pr.step q c.now (c.view q) (c.st q) .tick).state
    else c.st q
  sent := c.sent ∪
    { sm | ∃ q ∈ S.awake (c.now : Int),
        ∃ msg ∈ (Pr.step q c.now (c.view q) (c.st q) .tick).send, sm = ⟨q, msg⟩ }

/-- Transition labels. -/
inductive Action (V Msg Ev : Type) where
  /-- `m` is delivered to `p`, which reacts to it. -/
  | deliver (p : V) (m : SignedMsg V Msg)
  /-- A protocol-specific event fires at `p`. -/
  | custom (p : V) (ev : Ev)
  /-- `p` wakes up. -/
  | wake (p : V)
  /-- The round advances, and every active validator reacts to it. -/
  | clock
  /-- An adversarial validator signs an arbitrary message. -/
  | adversarial (p : V) (m : Msg)

/-- The step relation. *When* messages must be delivered is not here — that is a
    property of the model, imposed on executions. -/
inductive Step (V Msg State Ev : Type) [DecidableEq V] [DecidableEq Msg]
    (Pr : Protocol V Msg State Ev) (S : Schedule V) :
    Action V Msg Ev → Config V Msg State → Config V Msg State → Prop where
  /-- Any sent message may be delivered to any **active** validator, at any
      time. Delivery to a sleeping validator is simply not a transition, which is
      how messages get queued: they stay in `sent` until it wakes. The message is
      filed before the reaction runs, so `step` sees it in the view too. -/
  | deliver {c : Config V Msg State} {p : V} {m : SignedMsg V Msg} :
      m ∈ c.sent → p ∈ S.awake (c.now : Int) →
      Step V Msg State Ev Pr S (.deliver p m) c
        (react Pr p (.recv m) (receive p m c))
  /-- A protocol-specific event fires, if the protocol allows it here. -/
  | custom {c : Config V Msg State} {p : V} {ev : Ev} :
      p ∈ S.awake (c.now : Int) → Pr.enabled c.now (c.st p) ev →
      Step V Msg State Ev Pr S (.custom p ev) c (react Pr p (.custom ev) c)
  /-- `p` has just woken: awake now, asleep in the previous round. The framework
      reports this because a protocol cannot start a joining procedure it is not
      told about. -/
  | wake {c : Config V Msg State} {p : V} :
      p ∈ S.awake (c.now : Int) → p ∉ S.awake ((c.now : Int) - 1) →
      Step V Msg State Ev Pr S (.wake p) c (react Pr p .wake c)
  /-- Time advances, and every awake validator reacts to the new round. -/
  | clock {c : Config V Msg State} :
      Step V Msg State Ev Pr S .clock c (tickAll Pr S c)
  /-- An adversarial validator signs anything. -/
  | adversarial {c : Config V Msg State} {p : V} {m : Msg} :
      p ∈ S.adv (c.now : Int) →
      Step V Msg State Ev Pr S (.adversarial p m) c
        { c with sent := insert ⟨p, m⟩ c.sent }

/-- Initial configurations. -/
def Init (Pr : Protocol V Msg State Ev) (c : Config V Msg State) : Prop :=
  c.now = 0 ∧ (∀ p, c.st p = Pr.init p) ∧ (∀ p, c.view p = ∅) ∧ c.sent = ∅

/-- The protocol as a transition system. -/
def system (V Msg State Ev : Type) [DecidableEq V] [DecidableEq Msg]
    (Pr : Protocol V Msg State Ev) (S : Schedule V) :
    System (Config V Msg State) (Action V Msg Ev) where
  Init := Init Pr
  Step := Step V Msg State Ev Pr S

end Framework.Sts2
