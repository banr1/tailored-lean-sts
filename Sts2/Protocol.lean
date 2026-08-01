import Mathlib.Data.Set.Image
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
* **Each validator reads its own clock**, `c[p].clock`, and that is the round
  handed to `step`. `Config.time` is *real* time, read only by the environment: the
  schedule, the network bound, GST. So clocks being synchronized is an
  **assumption** (`Execution.Synchronized`) rather than a fact of the model, and
  monotonicity is free, since `Step.tick` only increments.

The guard `c[p].clock < c.time` on `tick` stops a clock running ahead of real
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

universe u v

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

/-- Everything tracked per validator: one record rather than several parallel
    maps, so an action names the one field it changes and adding per-validator
    state touches one place. -/
structure Local (V Msg State : Type) where
  /-- This validator's own clock reading. Advanced only by a `tick`. -/
  clock : Round
  /-- Its protocol state. -/
  st : State
  /-- Its view: everything delivered to it so far. -/
  view : View V Msg

/-- A global configuration. -/
structure Config (V Msg State : Type) where
  /-- Real time. Read by the environment — schedule, network bound, GST — and
      never handed to a protocol. -/
  time : Round
  /-- Each validator's local record. -/
  nodes : V → Local V Msg State
  /-- Every message ever signed. Monotone. -/
  sent : Set (SignedMsg V Msg)

/-- `c[p]` is `p`'s local record, so `c[p].clock`, `c[p].view` and `c[p].st` read
    its parts. Indexing is total, hence the trivial side-condition. -/
instance : GetElem (Config V Msg State) V (Local V Msg State) (fun _ _ => True) where
  getElem c p _ := c.nodes p

variable [DecidableEq V] [DecidableEq Msg]

/-- Change one validator's local record, leaving everything else alone. Every
    per-validator update goes through this. -/
def Config.update (c : Config V Msg State) (p : V)
    (f : Local V Msg State → Local V Msg State) : Config V Msg State :=
  { c with nodes := fun q => if q = p then f (c.nodes q) else c.nodes q }

/-- File a delivered message into `p`'s view, without reacting to it. -/
def receive (p : V) (m : SignedMsg V Msg) (c : Config V Msg State) :
    Config V Msg State :=
  c.update p fun l => { l with view := insert m l.view }

/-- Run `p`'s reaction to `e` against its own clock: install the new state, and add
    what it sent to the network signed by `p`.

    Sends are *not* filtered here. A just-woken Majorum validator "receives all
    queued messages and resumes execution, but sends nothing until round
    `voting(t)`" — and it achieves that by returning `send := ∅` from its own
    `step`. -/
def react (Pr : Protocol V Msg State Ev) (p : V) (e : Event V Msg Ev)
    (c : Config V Msg State) : Config V Msg State :=
  { c.update p (fun l => { l with st := (Pr.step p l.clock l.view l.st e).state })
      with sent := c.sent ∪
        (SignedMsg.mk p ''
          ((Pr.step p c[p].clock c[p].view c[p].st e).send : Set Msg)) }

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

/-- What one action does: when it may occur, and how it may change the
    configuration.

    The two halves sit **together, per action**, so they cannot be mismatched: there
    is no way to write an enabling condition belonging to one action beside the
    effect of another, and no way to add an action and forget one half.

    `Effect` is a *relation*, not a function, so a nondeterministic action is
    expressible — the successor need not be determined by the configuration. All six
    current actions happen to be deterministic, because every choice is carried in
    the action itself (`deliver p m` names the message, `custom p ev` the event), but
    nothing here requires that.

    `feasible` is the price of making enabling conditions syntactic: it says the
    condition does not promise more than the effect can deliver. Event-B calls this
    the *feasibility* proof obligation (FIS) and generates it for exactly this
    reason; TLA+ avoids it by defining `ENABLED A` as "some successor satisfies `A`",
    at the cost of enabledness never being explicit. Discharging it at the definition
    site is what keeps `Execution.Enabled` honest — the alternative, an enabling
    predicate passed alongside an action, has nothing tying the two together. -/
structure ActionSpec (V Msg State : Type) where
  /-- When the action may occur. -/
  Enabled : Config V Msg State → Prop
  /-- How it may change the configuration. -/
  Effect : Config V Msg State → Config V Msg State → Prop
  /-- Being enabled really does permit a step (Event-B's FIS). -/
  feasible : ∀ c, Enabled c → ∃ c', Effect c c'

/-- Each action's enabling condition and effect. -/
def spec (Pr : Protocol V Msg State Ev) (S : Schedule V) :
    Action V Msg Ev → ActionSpec V Msg State
  -- Real time advances on its own. Always enabled, so no configuration is stuck.
  | .advance => {
      Enabled _ := True
      Effect c c' := c' = { c with time := c.time + 1 }
      feasible _ _ := ⟨_, rfl⟩ }
  -- An awake validator whose clock is behind advances it by one and reacts. The
  -- guard gives exactly one tick per validator per round.
  | .tick p => {
      Enabled c := p ∈ S.awake (c.time : Int) ∧ c[p].clock < c.time
      Effect c c' := c' = react Pr p .tick
        (c.update p fun l => { l with clock := l.clock + 1 })
      feasible _ _ := ⟨_, rfl⟩ }
  -- Any sent message may be delivered to any awake validator, at any time.
  -- Delivery to a sleeping validator is simply not enabled, which is how messages
  -- get queued: they stay in `sent` until it wakes. The message is filed before the
  -- reaction runs, so `step` sees it in the view too.
  | .deliver p m => {
      Enabled c := m ∈ c.sent ∧ p ∈ S.awake (c.time : Int)
      Effect c c' := c' = react Pr p (.recv m) (receive p m c)
      feasible _ _ := ⟨_, rfl⟩ }
  -- Awake now, asleep in the previous round. Reported because a protocol cannot
  -- start a joining procedure it is not told about.
  | .wake p => {
      Enabled c := p ∈ S.awake (c.time : Int) ∧ p ∉ S.awake ((c.time : Int) - 1)
      Effect c c' := c' = react Pr p .wake c
      feasible _ _ := ⟨_, rfl⟩ }
  -- A protocol-specific event, if the protocol allows it at the validator's own
  -- clock reading.
  | .custom p ev => {
      Enabled c := p ∈ S.awake (c.time : Int) ∧ Pr.enabled c[p].clock c[p].st ev
      Effect c c' := c' = react Pr p (.custom ev) c
      feasible _ _ := ⟨_, rfl⟩ }
  -- An adversarial validator signs anything.
  | .adversarial p m => {
      Enabled c := p ∈ S.adv (c.time : Int)
      Effect c c' := c' = { c with sent := insert ⟨p, m⟩ c.sent }
      feasible _ _ := ⟨_, rfl⟩ }

/-- The step relation: enabled, and then the effect. *When* messages must be
    delivered, and whether clocks agree with real time, are properties of the model,
    imposed on executions rather than here. -/
def Step (Pr : Protocol V Msg State Ev) (S : Schedule V) (a : Action V Msg Ev)
    (c c' : Config V Msg State) : Prop :=
  (spec Pr S a).Enabled c ∧ (spec Pr S a).Effect c c'

/-- Initial configurations. -/
def Init (Pr : Protocol V Msg State Ev) (c : Config V Msg State) : Prop :=
  c.time = 0 ∧ (∀ p, c.nodes p = { clock := 0, st := Pr.init p, view := ∅ }) ∧
    c.sent = ∅

/-- A labelled transition system: initial states, and a labelled step relation
    that may be nondeterministic and partial.

    The framework's own, so that `Framework/` depends on nothing outside itself.
    Only the structure is here — no reachability or inductive-invariant machinery,
    since the framework carries no proofs while its shape is being iterated on.
    `Common/System.lean` has that machinery for the `Sts` attempt; when proofs
    return, **build it here rather than importing `Common`**, because liveness needs
    statements over `Execution` that a state-based invariant cannot express. -/
structure System (State : Type u) (Label : Type v) where
  /-- States the system may start in. -/
  Init : State → Prop
  /-- Labelled transition relation. -/
  Step : Label → State → State → Prop

/-- The protocol as a transition system. -/
def system (V Msg State Ev : Type) [DecidableEq V] [DecidableEq Msg]
    (Pr : Protocol V Msg State Ev) (S : Schedule V) :
    System (Config V Msg State) (Action V Msg Ev) where
  Init := Init Pr
  Step := Step Pr S

end Framework.Sts2
