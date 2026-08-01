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

variable {V Msg NodeState Ev : Type}

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

/-- What one node's step produces: its new state, and the messages it sends
    (broadcast — the network decides who receives them and when).

    Named for what it is rather than `Effect`, which in this file means an *action's*
    effect on the whole configuration (`ActionSpec.Effect`). The two live at different
    levels and sharing a name was confusing. -/
structure NodeStepResult (NodeState Msg : Type) where
  /-- The node's state afterwards. -/
  state : NodeState
  /-- Messages sent, each signed by the reacting validator. -/
  send : Finset Msg

/-- A protocol. -/
structure Protocol (V Msg NodeState Ev : Type) where
  /-- Initial state of each validator. -/
  init : V → NodeState
  /-- `step p r view s e eff` — `eff` is *a* reaction `p` may have to `e`, where `r`
      is **`p`'s own clock reading**, not real time.

      A relation, not a function, so honest behaviour may be underspecified: which
      payload a leader proposes, which of several equally valid chains it follows,
      anything a specification leaves open. A protocol that is in fact deterministic
      lifts its function with `step p r v s e eff := eff = f p r v s e`, which keeps
      it computable — see the examples. -/
  step : V → Round → View V Msg → NodeState → Event V Msg Ev → NodeStepResult NodeState Msg → Prop
  /-- Some reaction is always available: a protocol may not get stuck. This is what
      discharges each action's `feasible`, so it is the protocol-side counterpart of
      Event-B's FIS. -/
  total : ∀ p r view s e, ∃ eff, step p r view s e eff
  /-- When a protocol-specific event may fire, also against the local clock. -/
  enabled : Round → NodeState → Ev → Prop

/-- Everything tracked per validator: one record rather than several parallel
    maps, so an action names the one field it changes and adding per-validator
    state touches one place. -/
structure Local (V Msg NodeState : Type) where
  /-- This validator's own clock reading. Advanced only by a `tick`. -/
  clock : Round
  /-- Its protocol state. -/
  st : NodeState
  /-- Its view: everything delivered to it so far. -/
  view : View V Msg

/-- A global configuration. -/
structure Config (V Msg NodeState : Type) where
  /-- Real time. Read by the environment — schedule, network bound, GST — and
      never handed to a protocol. -/
  time : Round
  /-- Each validator's local record. -/
  nodes : V → Local V Msg NodeState
  /-- Every message ever signed. Monotone. -/
  sent : Set (SignedMsg V Msg)

/-- `c[p]` is `p`'s local record, so `c[p].clock`, `c[p].view` and `c[p].st` read
    its parts. Indexing is total, hence the trivial side-condition. -/
instance : GetElem (Config V Msg NodeState) V (Local V Msg NodeState) (fun _ _ => True) where
  getElem c p _ := c.nodes p

/-- Indexing is just the `nodes` map; `simp` needs telling. -/
@[simp] theorem getElem_nodes (c : Config V Msg NodeState) (p : V) : c[p] = c.nodes p := rfl

variable [DecidableEq V] [DecidableEq Msg]

/-- Change one validator's local record, leaving everything else alone. Every
    per-validator update goes through this. -/
def Config.update (c : Config V Msg NodeState) (p : V)
    (f : Local V Msg NodeState → Local V Msg NodeState) : Config V Msg NodeState :=
  { c with nodes := fun q => if q = p then f (c.nodes q) else c.nodes q }

/-- File a delivered message into `p`'s view, without reacting to it. -/
def receive (p : V) (m : SignedMsg V Msg) (c : Config V Msg NodeState) :
    Config V Msg NodeState :=
  c.update p fun l => { l with view := insert m l.view }

/-- Apply a reaction: install `p`'s new state and add what it sent to the network,
    signed by `p`.

    Sends are *not* filtered here. A just-woken Majorum validator "receives all
    queued messages and resumes execution, but sends nothing until round
    `voting(t)`" — and it achieves that by choosing `send := ∅` in its own `step`. -/
def install (p : V) (eff : NodeStepResult NodeState Msg) (c : Config V Msg NodeState) :
    Config V Msg NodeState :=
  { c.update p (fun l => { l with st := eff.state })
      with sent := c.sent ∪ (SignedMsg.mk p '' (eff.send : Set Msg)) }

/-- `p`'s clock advanced by one. -/
def bumped (p : V) (c : Config V Msg NodeState) : Config V Msg NodeState :=
  c.update p fun l => { l with clock := l.clock + 1 }

/-- `Reacts Pr p e pre c'` — `c'` is a configuration `p` may reach by reacting to `e`
    in `pre`. Existential over the permitted reactions, which is where honest
    nondeterminism lives. -/
def Reacts (Pr : Protocol V Msg NodeState Ev) (p : V) (e : Event V Msg Ev)
    (pre c' : Config V Msg NodeState) : Prop :=
  ∃ eff, Pr.step p pre[p].clock pre[p].view pre[p].st e eff ∧ c' = install p eff pre

omit [DecidableEq Msg] in
/-- Reacting is always possible, from `Protocol.total`. Every action whose effect is
    a reaction discharges its `feasible` with this. -/
theorem reacts_total (Pr : Protocol V Msg NodeState Ev) (p : V) (e : Event V Msg Ev)
    (pre : Config V Msg NodeState) : ∃ c', Reacts Pr p e pre c' := by
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
structure ActionSpec (V Msg NodeState : Type) where
  /-- When the action may occur. -/
  Enabled : Config V Msg NodeState → Prop
  /-- How it may change the configuration. -/
  Effect : Config V Msg NodeState → Config V Msg NodeState → Prop
  /-- Being enabled really does permit a step (Event-B's FIS). -/
  feasible : ∀ c, Enabled c → ∃ c', Effect c c'

/-- Each action's enabling condition and effect. -/
def spec (Pr : Protocol V Msg NodeState Ev) (S : Schedule V) :
    Action V Msg Ev → ActionSpec V Msg NodeState
  -- Real time advances on its own. Always enabled, so no configuration is stuck.
  | .advance => {
      Enabled _ := True
      Effect c c' := c' = { c with time := c.time + 1 }
      feasible _ _ := ⟨_, rfl⟩ }
  -- An awake validator whose clock is behind advances it by one and reacts. The
  -- guard gives exactly one tick per validator per round.
  | .tick p => {
      Enabled c := p ∈ S.awake (c.time : Int) ∧ c[p].clock < c.time
      Effect c c' := Reacts Pr p .tick (bumped p c) c'
      feasible _ _ := reacts_total Pr p .tick _ }
  -- Any sent message may be delivered to any awake validator, at any time.
  -- Delivery to a sleeping validator is simply not enabled, which is how messages
  -- get queued: they stay in `sent` until it wakes. The message is filed before the
  -- reaction runs, so `step` sees it in the view too.
  | .deliver p m => {
      Enabled c := m ∈ c.sent ∧ p ∈ S.awake (c.time : Int)
      Effect c c' := Reacts Pr p (.recv m) (receive p m c) c'
      feasible _ _ := reacts_total Pr p (.recv m) _ }
  -- Awake now, asleep in the previous round. Reported because a protocol cannot
  -- start a joining procedure it is not told about.
  | .wake p => {
      Enabled c := p ∈ S.awake (c.time : Int) ∧ p ∉ S.awake ((c.time : Int) - 1)
      Effect c c' := Reacts Pr p .wake c c'
      feasible _ _ := reacts_total Pr p .wake _ }
  -- A protocol-specific event, if the protocol allows it at the validator's own
  -- clock reading.
  | .custom p ev => {
      Enabled c := p ∈ S.awake (c.time : Int) ∧ Pr.enabled c[p].clock c[p].st ev
      Effect c c' := Reacts Pr p (.custom ev) c c'
      feasible _ _ := reacts_total Pr p (.custom ev) _ }
  -- An adversarial validator signs anything.
  | .adversarial p m => {
      Enabled c := p ∈ S.adv (c.time : Int)
      Effect c c' := c' = { c with sent := insert ⟨p, m⟩ c.sent }
      feasible _ _ := ⟨_, rfl⟩ }

/-- The step relation: enabled, and then the effect. *When* messages must be
    delivered, and whether clocks agree with real time, are properties of the model,
    imposed on executions rather than here. -/
def Step (Pr : Protocol V Msg NodeState Ev) (S : Schedule V) (a : Action V Msg Ev)
    (c c' : Config V Msg NodeState) : Prop :=
  (spec Pr S a).Enabled c ∧ (spec Pr S a).Effect c c'

/-- Case analysis on a step, one case per action, with the successor already computed.

    `Step` is a `def` — a conjunction — so `cases` cannot split it by action; every proof
    would otherwise open with `obtain ⟨-, eff, -, h⟩; subst h` in each case. This does
    that once. Each case receives the action's enabling condition, the effect the
    protocol permitted, and a goal whose successor is the concrete configuration rather
    than an unknown constrained by an equation.

    It is the non-inductive equivalent of `cases` on an inductive step relation, and it
    is derived from `spec`, so it cannot drift from the step relation. -/
theorem Step.elim {Pr : Protocol V Msg NodeState Ev} {S : Schedule V}
    {motive : Action V Msg Ev → Config V Msg NodeState → Config V Msg NodeState → Prop}
    {a : Action V Msg Ev} {c c' : Config V Msg NodeState} (h : Step Pr S a c c')
    (advance : ∀ d : Config V Msg NodeState,
      motive .advance d { d with time := d.time + 1 })
    (tick : ∀ (d : Config V Msg NodeState) (p : V) (eff : NodeStepResult NodeState Msg),
      (spec Pr S (.tick p)).Enabled d →
      Pr.step p (bumped p d)[p].clock (bumped p d)[p].view (bumped p d)[p].st .tick eff →
      motive (.tick p) d (install p eff (bumped p d)))
    (deliver : ∀ (d : Config V Msg NodeState) (p : V) (m : SignedMsg V Msg)
        (eff : NodeStepResult NodeState Msg),
      (spec Pr S (.deliver p m)).Enabled d →
      Pr.step p (receive p m d)[p].clock (receive p m d)[p].view (receive p m d)[p].st
        (.recv m) eff →
      motive (.deliver p m) d (install p eff (receive p m d)))
    (wake : ∀ (d : Config V Msg NodeState) (p : V) (eff : NodeStepResult NodeState Msg),
      (spec Pr S (.wake p)).Enabled d →
      Pr.step p d[p].clock d[p].view d[p].st .wake eff →
      motive (.wake p) d (install p eff d))
    (custom : ∀ (d : Config V Msg NodeState) (p : V) (ev : Ev) (eff : NodeStepResult NodeState Msg),
      (spec Pr S (.custom p ev)).Enabled d →
      Pr.step p d[p].clock d[p].view d[p].st (.custom ev) eff →
      motive (.custom p ev) d (install p eff d))
    (adversarial : ∀ (d : Config V Msg NodeState) (p : V) (m : Msg),
      (spec Pr S (.adversarial p m)).Enabled d →
      motive (.adversarial p m) d { d with sent := insert ⟨p, m⟩ d.sent }) :
    motive a c c' := by
  cases a with
  | advance => obtain ⟨-, rfl⟩ := h; exact advance c
  | tick p => obtain ⟨he, eff, hp, rfl⟩ := h; exact tick c p eff he hp
  | deliver p m => obtain ⟨he, eff, hp, rfl⟩ := h; exact deliver c p m eff he hp
  | wake p => obtain ⟨he, eff, hp, rfl⟩ := h; exact wake c p eff he hp
  | custom p ev => obtain ⟨he, eff, hp, rfl⟩ := h; exact custom c p ev eff he hp
  | adversarial p m => obtain ⟨he, rfl⟩ := h; exact adversarial c p m he

/-! ### Two invariants, proved through the eliminator

Not needed by the framework, but they are what the eliminator is for: each case arrives
with its successor already concrete, so the proof is one line per action with no
destructuring. -/

/-- The network never forgets. -/
theorem sent_mono {Pr : Protocol V Msg NodeState Ev} {S : Schedule V} {a : Action V Msg Ev}
    {c c' : Config V Msg NodeState} (h : Step Pr S a c c') : c.sent ⊆ c'.sent := by
  refine h.elim (motive := fun _ d d' => d.sent ⊆ d'.sent) ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun _ _ hx => hx
  · exact fun _ _ _ _ _ _ hx => Or.inl hx
  · exact fun _ _ _ _ _ _ _ hx => Or.inl hx
  · exact fun _ _ _ _ _ _ hx => Or.inl hx
  · exact fun _ _ _ _ _ _ _ hx => Or.inl hx
  · exact fun _ _ _ _ _ hx => Or.inr hx

omit [DecidableEq Msg] in
/-- Installing a reaction leaves every clock alone: only `st` and `sent` change.

    Stated over `.nodes` rather than `[…]` because `getElem_nodes` is itself a `simp`
    lemma and fires first; a version phrased with `[…]` would never match. -/
@[simp] theorem install_clock (q : V) (eff : NodeStepResult NodeState Msg)
    (d : Config V Msg NodeState) (p : V) :
    ((install q eff d).nodes p).clock = (d.nodes p).clock := by
  by_cases hpq : p = q <;> simp [install, Config.update, hpq]

/-- Filing a delivered message leaves every clock alone. -/
@[simp] theorem receive_clock (q : V) (m : SignedMsg V Msg)
    (d : Config V Msg NodeState) (p : V) :
    ((receive q m d).nodes p).clock = (d.nodes p).clock := by
  by_cases hpq : p = q <;> simp [receive, Config.update, hpq]

/-! ### What the helpers do to each field

The API any invariant proof needs: for `install`, `receive` and `bumped`, what happens to
each field of each validator. Phrased over `.nodes` for the reason given above. -/

omit [DecidableEq Msg] in
@[simp] theorem install_view (q : V) (eff : NodeStepResult NodeState Msg) (d : Config V Msg NodeState)
    (p : V) : ((install q eff d).nodes p).view = (d.nodes p).view := by
  by_cases hpq : p = q <;> simp [install, Config.update, hpq]

omit [DecidableEq Msg] in
@[simp] theorem install_sent (q : V) (eff : NodeStepResult NodeState Msg) (d : Config V Msg NodeState) :
    (install q eff d).sent = d.sent ∪ (SignedMsg.mk q '' (eff.send : Set Msg)) := rfl

@[simp] theorem receive_view_self (q : V) (m : SignedMsg V Msg)
    (d : Config V Msg NodeState) :
    ((receive q m d).nodes q).view = insert m ((d.nodes q).view) := by
  simp [receive, Config.update]

@[simp] theorem receive_view_other (q : V) (m : SignedMsg V Msg)
    (d : Config V Msg NodeState) (p : V) (h : p ≠ q) :
    ((receive q m d).nodes p).view = (d.nodes p).view := by
  simp [receive, Config.update, h]

@[simp] theorem receive_sent (q : V) (m : SignedMsg V Msg) (d : Config V Msg NodeState) :
    (receive q m d).sent = d.sent := rfl

omit [DecidableEq Msg] in
@[simp] theorem bumped_view (q : V) (d : Config V Msg NodeState) (p : V) :
    ((bumped q d).nodes p).view = (d.nodes p).view := by
  by_cases hpq : p = q <;> simp [bumped, Config.update, hpq]

omit [DecidableEq Msg] in
@[simp] theorem bumped_sent (q : V) (d : Config V Msg NodeState) :
    (bumped q d).sent = d.sent := rfl

/-- Clocks never go backwards. -/
theorem clock_mono {Pr : Protocol V Msg NodeState Ev} {S : Schedule V} {a : Action V Msg Ev}
    {c c' : Config V Msg NodeState} (h : Step Pr S a c c') (p : V) :
    c[p].clock ≤ c'[p].clock := by
  refine h.elim (motive := fun _ d d' => d[p].clock ≤ d'[p].clock) ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun _ => le_refl _
  · intro d q eff _ _
    by_cases hpq : p = q <;> simp [bumped, Config.update, hpq]
  · exact fun _ _ _ _ _ _ => by simp
  · exact fun _ _ _ _ _ => by simp
  · exact fun _ _ _ _ _ _ => by simp
  · exact fun _ _ _ _ => le_refl _

/-- Initial configurations. -/
def Init (Pr : Protocol V Msg NodeState Ev) (c : Config V Msg NodeState) : Prop :=
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
structure System (Carrier : Type u) (Label : Type v) where
  /-- The states the system may start in. -/
  Init : Carrier → Prop
  /-- Labelled transition relation. -/
  Step : Label → Carrier → Carrier → Prop

/-- The protocol as a transition system. -/
def system (V Msg NodeState Ev : Type) [DecidableEq V] [DecidableEq Msg]
    (Pr : Protocol V Msg NodeState Ev) (S : Schedule V) :
    System (Config V Msg NodeState) (Action V Msg Ev) where
  Init := Init Pr
  Step := Step Pr S

end Framework.Sts2
