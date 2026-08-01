import Mathlib.Data.Set.Image
import Framework.Sts2D.Schedule

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
predicates on executions (`Framework.Sts2D.Execution`), so different models impose
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

namespace Framework.Sts2D

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
  /-- `step p r view s e eff` — `eff` is *a* reaction `p` may have to `e`, where `r`
      is **`p`'s own clock reading**, not real time.

      A relation, not a function, so honest behaviour may be underspecified: which
      payload a leader proposes, which of several equally valid chains it follows,
      anything a specification leaves open. A protocol that is in fact deterministic
      lifts its function with `step p r v s e eff := eff = f p r v s e`, which keeps
      it computable — see the examples. -/
  step : V → Round → View V Msg → State → Event V Msg Ev → Effect State Msg → Prop
  /-- Some reaction is always available: a protocol may not get stuck. This is what
      discharges each action's `feasible`, so it is the protocol-side counterpart of
      Event-B's FIS. -/
  total : ∀ p r view s e, ∃ eff, step p r view s e eff
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

/-- Apply a reaction: install `p`'s new state and add what it sent to the network,
    signed by `p`.

    Sends are *not* filtered here. A just-woken Majorum validator "receives all
    queued messages and resumes execution, but sends nothing until round
    `voting(t)`" — and it achieves that by choosing `send := ∅` in its own `step`. -/
def install (p : V) (eff : Effect State Msg) (c : Config V Msg State) :
    Config V Msg State :=
  { c.update p (fun l => { l with st := eff.state })
      with sent := c.sent ∪ (SignedMsg.mk p '' (eff.send : Set Msg)) }

/-- `Reacts Pr p e pre c'` — `c'` is a configuration `p` may reach by reacting to `e`
    in `pre`. Existential over the permitted reactions, which is where honest
    nondeterminism lives. -/
def Reacts (Pr : Protocol V Msg State Ev) (p : V) (e : Event V Msg Ev)
    (pre c' : Config V Msg State) : Prop :=
  ∃ eff, Pr.step p pre[p].clock pre[p].view pre[p].st e eff ∧ c' = install p eff pre

omit [DecidableEq Msg] in
/-- Reacting is always possible, from `Protocol.total`. Every action whose effect is
    a reaction discharges its `feasible` with this. -/
theorem reacts_total (Pr : Protocol V Msg State Ev) (p : V) (e : Event V Msg Ev)
    (pre : Config V Msg State) : ∃ c', Reacts Pr p e pre c' := by
  obtain ⟨eff, he⟩ := Pr.total p pre[p].clock pre[p].view pre[p].st e
  exact ⟨_, eff, he, rfl⟩

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

/-- `p`'s clock advanced by one. -/
def bumped (p : V) (c : Config V Msg State) : Config V Msg State :=
  c.update p fun l => { l with clock := l.clock + 1 }

/-- Everything about one action, in one record: when it may occur, what it may choose,
    which choices the protocol permits, and what a choice does.

    `Choice` is the action's own nondeterminism. `Unit` for actions with none;
    `Effect State Msg` for the ones that run the protocol, so an underspecified
    protocol is expressible. Keeping it per action is what lets `Apply` be a
    **function** rather than a relation on the successor — and that is what makes the
    step relation below cheap to reason about, since the successor is then an
    expression in the constructor's binders and `cases` rewrites it for you.

    `feasible` is Event-B's FIS obligation: being enabled really does leave a choice
    available. -/
structure ActionSpec (V Msg State : Type) where
  /-- What this action chooses, if anything. -/
  Choice : Type
  /-- When it may occur — the environment's condition. -/
  Enabled : Config V Msg State → Prop
  /-- Which choices the protocol permits here. -/
  Permits : Config V Msg State → Choice → Prop
  /-- What a permitted choice does. -/
  Apply : Choice → Config V Msg State → Config V Msg State
  /-- Enabled leaves a choice available. -/
  feasible : ∀ c, Enabled c → ∃ ch, Permits c ch

/-- Each action's specification. Guard and effect sit side by side, per action, and
    each exists in exactly one place. -/
def spec (Pr : Protocol V Msg State Ev) (S : Schedule V) :
    Action V Msg Ev → ActionSpec V Msg State
  -- Real time advances on its own. Always enabled, so no configuration is stuck.
  | .advance => {
      Choice := Unit
      Enabled _ := True
      Permits _ _ := True
      Apply _ c := { c with time := c.time + 1 }
      feasible _ _ := ⟨(), trivial⟩ }
  -- An awake validator whose clock is behind advances it by one and reacts.
  | .tick p => {
      Choice := Effect State Msg
      Enabled c := p ∈ S.awake (c.time : Int) ∧ c[p].clock < c.time
      Permits c eff :=
        Pr.step p (bumped p c)[p].clock (bumped p c)[p].view (bumped p c)[p].st .tick eff
      Apply eff c := install p eff (bumped p c)
      feasible c _ := Pr.total p (bumped p c)[p].clock (bumped p c)[p].view
        (bumped p c)[p].st .tick }
  -- Any sent message may be delivered to any awake validator, at any time. Delivery to
  -- a sleeping validator is simply not enabled, which is how messages get queued.
  | .deliver p m => {
      Choice := Effect State Msg
      Enabled c := m ∈ c.sent ∧ p ∈ S.awake (c.time : Int)
      Permits c eff := Pr.step p (receive p m c)[p].clock (receive p m c)[p].view
        (receive p m c)[p].st (.recv m) eff
      Apply eff c := install p eff (receive p m c)
      feasible c _ := Pr.total p (receive p m c)[p].clock (receive p m c)[p].view
        (receive p m c)[p].st (.recv m) }
  -- Awake now, asleep in the previous round.
  | .wake p => {
      Choice := Effect State Msg
      Enabled c := p ∈ S.awake (c.time : Int) ∧ p ∉ S.awake ((c.time : Int) - 1)
      Permits c eff := Pr.step p c[p].clock c[p].view c[p].st .wake eff
      Apply eff c := install p eff c
      feasible c _ := Pr.total p c[p].clock c[p].view c[p].st .wake }
  -- A protocol-specific event, if the protocol allows it at the validator's own clock.
  | .custom p ev => {
      Choice := Effect State Msg
      Enabled c := p ∈ S.awake (c.time : Int) ∧ Pr.enabled c[p].clock c[p].st ev
      Permits c eff := Pr.step p c[p].clock c[p].view c[p].st (.custom ev) eff
      Apply eff c := install p eff c
      feasible c _ := Pr.total p c[p].clock c[p].view c[p].st (.custom ev) }
  -- An adversarial validator signs anything.
  | .adversarial p m => {
      Choice := Unit
      Enabled c := p ∈ S.adv (c.time : Int)
      Permits _ _ := True
      Apply _ c := { c with sent := insert ⟨p, m⟩ c.sent }
      feasible _ _ := ⟨(), trivial⟩ }

/-- The step relation: **one constructor per action**, each citing that action's spec.

    Two properties, both wanted. `cases` on a `Step` splits by action immediately —
    giving six named goals with the action refined in each — rather than leaving `a`
    abstract for a second `cases`. And the successor is `Apply ch c`, an expression in
    the constructor's binders, so `cases` also rewrites it: no existential is written
    and no `subst` is needed.

    The conditions are not duplicated: each constructor cites `Enabled`/`Permits` from
    the table above, so adding an action means adding a `spec` arm and a constructor
    that names it. -/
inductive Step (Pr : Protocol V Msg State Ev) (S : Schedule V) :
    Action V Msg Ev → Config V Msg State → Config V Msg State → Prop where
  | advance {c : Config V Msg State} :
      (spec Pr S .advance).Enabled c →
      Step Pr S .advance c ((spec Pr S .advance).Apply () c)
  | tick {c : Config V Msg State} {p : V} (eff : Effect State Msg) :
      (spec Pr S (.tick p)).Enabled c → (spec Pr S (.tick p)).Permits c eff →
      Step Pr S (.tick p) c ((spec Pr S (.tick p)).Apply eff c)
  | deliver {c : Config V Msg State} {p : V} {m : SignedMsg V Msg}
      (eff : Effect State Msg) :
      (spec Pr S (.deliver p m)).Enabled c → (spec Pr S (.deliver p m)).Permits c eff →
      Step Pr S (.deliver p m) c ((spec Pr S (.deliver p m)).Apply eff c)
  | wake {c : Config V Msg State} {p : V} (eff : Effect State Msg) :
      (spec Pr S (.wake p)).Enabled c → (spec Pr S (.wake p)).Permits c eff →
      Step Pr S (.wake p) c ((spec Pr S (.wake p)).Apply eff c)
  | custom {c : Config V Msg State} {p : V} {ev : Ev} (eff : Effect State Msg) :
      (spec Pr S (.custom p ev)).Enabled c → (spec Pr S (.custom p ev)).Permits c eff →
      Step Pr S (.custom p ev) c ((spec Pr S (.custom p ev)).Apply eff c)
  | adversarial {c : Config V Msg State} {p : V} {m : Msg} :
      (spec Pr S (.adversarial p m)).Enabled c →
      Step Pr S (.adversarial p m) c ((spec Pr S (.adversarial p m)).Apply () c)

/-- A step is possible exactly when the action is enabled.

    The forward direction is uniform — every constructor carries its `Enabled` — and
    the backward direction gets a choice from `feasible`, then names the constructor
    for the action at hand. -/
theorem enabled_iff (Pr : Protocol V Msg State Ev) (S : Schedule V)
    (a : Action V Msg Ev) (c : Config V Msg State) :
    (∃ c', Step Pr S a c c') ↔ (spec Pr S a).Enabled c := by
  constructor
  · intro ⟨_, h⟩; cases h <;> assumption
  · intro hg
    obtain ⟨ch, hp⟩ := (spec Pr S a).feasible c hg
    cases a with
    | advance => exact ⟨_, .advance hg⟩
    | tick p => exact ⟨_, .tick ch hg hp⟩
    | deliver p m => exact ⟨_, .deliver ch hg hp⟩
    | wake p => exact ⟨_, .wake ch hg hp⟩
    | custom p ev => exact ⟨_, .custom ch hg hp⟩
    | adversarial p m => exact ⟨_, .adversarial hg⟩

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

end Framework.Sts2D
