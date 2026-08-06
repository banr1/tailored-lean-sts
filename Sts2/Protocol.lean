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

The condition `c[p].clock < c.time` on `tick` stops a clock running ahead of real
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

variable {Node Msg NodeState Ev : Type}

/-- What a protocol reacts to. `Ev` is the protocol's own event type; use `Empty`
    if it has none. -/
inductive Event (Node Msg Ev : Type) where
  /-- This validator's clock advanced. -/
  | tick
  /-- A message was delivered; it is already in the view. -/
  | recv (m : SignedMsg Node Msg)
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
structure Protocol (Node Msg NodeState Ev : Type) where
  /-- Initial state of each validator. -/
  init : Node → NodeState
  /-- `step p r view s e res` — `res` is *a* reaction `p` may have to `e`, where `r`
      is **`p`'s own clock reading**, not real time.

      A relation, not a function, so honest behaviour may be underspecified: which
      payload a leader proposes, which of several equally valid chains it follows,
      anything a specification leaves open. A protocol that is in fact deterministic
      lifts its function with `step p r v s e res := res = f p r v s e`, which keeps
      it computable — see the examples. -/
  step : Node → Time → View Node Msg → NodeState → Event Node Msg Ev → NodeStepResult NodeState Msg → Prop
  /-- Some reaction is always available: a protocol may not get stuck. This is what
      discharges each action's `feasible`, so it is the protocol-side counterpart of
      Event-B's FIS. -/
  total : ∀ p r view s e, ∃ res, step p r view s e res
  /-- When a protocol-specific event may fire, also against the local clock. -/
  enabled : Time → NodeState → Ev → Prop

/-- Everything tracked per validator: one record rather than several parallel
    maps, so an action names the one field it changes and adding per-validator
    state touches one place. -/
structure Local (Node Msg NodeState : Type) where
  /-- This validator's own clock reading. Advanced only by a `tick`. -/
  clock : Time
  /-- Its protocol state. -/
  st : NodeState
  /-- Its view: everything delivered to it so far. -/
  view : View Node Msg

/-- A global configuration. -/
structure Config (Node Msg NodeState : Type) where
  /-- Real time. Read by the environment — schedule, network bound, GST — and
      never handed to a protocol. -/
  time : Time
  /-- Each validator's local record. -/
  nodes : Node → Local Node Msg NodeState
  /-- Every message ever signed. Monotone. -/
  sent : Set (SignedMsg Node Msg)

/-- `c[p]` is `p`'s local record, so `c[p].clock`, `c[p].view` and `c[p].st` read
    its parts. Indexing is total, hence the trivial side-condition. -/
instance : GetElem (Config Node Msg NodeState) Node (Local Node Msg NodeState) (fun _ _ => True) where
  getElem c p _ := c.nodes p

/-- Indexing is the `nodes` map.

    Oriented *towards* the brackets, because brackets are this framework's normal form:
    they are how `Execution`'s statements read, and how the field lemmas below are phrased.
    A `c.nodes q` exposed by unfolding a definition is rewritten to `c[q]`, so the two
    spellings cannot drift apart in a goal. -/
@[simp] theorem nodes_apply (c : Config Node Msg NodeState) (q : Node) : c.nodes q = c[q] := rfl

variable [DecidableEq Node] [DecidableEq Msg]

/-- Give `p` the record `r`, leaving every other validator's alone.

    The **only** place the `fun q => if p = q then … else c[q]` pattern is written: the
    setters below are each one call to this with the field they change, so a new setter
    cannot get the map update subtly wrong. Takes the new record rather than a function of
    the old one — a function-shaped update only yields lemmas mentioning an opaque
    `f c[p]`, whereas a value gives the unconditional read-back below. -/
def Config.setNode (c : Config Node Msg NodeState) (p : Node) (r : Local Node Msg NodeState) :
    Config Node Msg NodeState :=
  { c with nodes := fun q => if p = q then r else c[q] }

omit [DecidableEq Msg] in
/-- How a `setNode` reads back. The single source of the `if` that every field lemma
    below splits. -/
@[simp] theorem Config.setNode_apply (c : Config Node Msg NodeState) (p : Node)
    (r : Local Node Msg NodeState) (q : Node) :
    (c.setNode p r)[q] = if p = q then r else c[q] := rfl

/-! The three writes below each name the one field they change, and each is a single
`setNode` with that field replaced — none of them is layered on another, so they read the
same way and each has the same shape of read-back lemma. An earlier version had
`applyNodeStepResult` go through a `Config.setNodeState`, which cost an extra hop in every
proof about it and made it the odd one out. -/

/-- File a delivered message into `p`'s view, without reacting to it. -/
def receive (p : Node) (m : SignedMsg Node Msg) (c : Config Node Msg NodeState) :
    Config Node Msg NodeState :=
  c.setNode p { c[p] with view := insert m c[p].view }

/-- Apply a reaction: store `p`'s new state and add what it sent to the network,
    signed by `p`.

    Sends are *not* filtered here. A just-woken Majorum validator "receives all
    queued messages and resumes execution, but sends nothing until round
    `voting(t)`" — and it achieves that by choosing `send := ∅` in its own `step`. -/
def applyNodeStepResult (p : Node) (res : NodeStepResult NodeState Msg) (c : Config Node Msg NodeState) :
    Config Node Msg NodeState :=
  { c.setNode p { c[p] with st := res.state }
      with sent := c.sent ∪ (SignedMsg.mk p '' (res.send : Set Msg)) }

/-- `p`'s clock now reads `t`. The framework says nothing about which `t` — see
    `Framework.Sts2.Execution` for the assumptions that pin it down. -/
def setClock (p : Node) (t : Time) (c : Config Node Msg NodeState) :
    Config Node Msg NodeState :=
  c.setNode p { c[p] with clock := t }

/-- `Reacts Pr p e pre c'` — `c'` is a configuration `p` may reach by reacting to `e`
    in `pre`. Existential over the permitted reactions, which is where honest
    nondeterminism lives. -/
def Reacts (Pr : Protocol Node Msg NodeState Ev) (p : Node) (e : Event Node Msg Ev)
    (pre c' : Config Node Msg NodeState) : Prop :=
  ∃ res, Pr.step p pre[p].clock pre[p].view pre[p].st e res ∧ c' = applyNodeStepResult p res pre

omit [DecidableEq Msg] in
/-- Reacting is always possible, from `Protocol.total`. Every action whose effect is
    a reaction discharges its `feasible` with this. -/
theorem reacts_total (Pr : Protocol Node Msg NodeState Ev) (p : Node) (e : Event Node Msg Ev)
    (pre : Config Node Msg NodeState) : ∃ c', Reacts Pr p e pre c' := by
  obtain ⟨res, he⟩ := Pr.total p pre[p].clock pre[p].view pre[p].st e
  exact ⟨_, res, he, rfl⟩

/-- Transition labels. -/
inductive Action (Node Msg Ev : Type) where
  /-- Real time becomes `t`; no validator acts. -/
  | advance (t : Time)
  /-- `p`'s clock comes to read `t`, and `p` reacts at that reading. -/
  | tick (p : Node) (t : Time)
  /-- `m` is delivered to `p`, which reacts to it. -/
  | deliver (p : Node) (m : SignedMsg Node Msg)
  /-- `p` wakes up. -/
  | wake (p : Node)
  /-- A protocol-specific event fires at `p`. -/
  | custom (p : Node) (ev : Ev)
  /-- An adversarial validator signs an arbitrary message. -/
  | adversarial (p : Node) (m : Msg)

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
structure ActionSpec (Node Msg NodeState : Type) where
  /-- When the action may occur. -/
  Enabled : Config Node Msg NodeState → Prop
  /-- How it may change the configuration. -/
  Effect : Config Node Msg NodeState → Config Node Msg NodeState → Prop
  /-- Being enabled really does permit a step (Event-B's FIS). -/
  feasible : ∀ c, Enabled c → ∃ c', Effect c c'

/-- Each action's enabling condition and effect. -/
def spec (Pr : Protocol Node Msg NodeState Ev) (S : Schedule Node) :
    Action Node Msg Ev → ActionSpec Node Msg NodeState
  -- Time becomes `t`. Unconstrained: the framework does not say whether time moves
  -- forwards, by how much, or at all. `Execution.TimeMonotone` and friends are where
  -- that gets decided, so a property assumes only the discipline it needs.
  | .advance t => {
      Enabled _ := True
      Effect c c' := c' = { c with time := t }
      feasible _ _ := ⟨_, rfl⟩ }
  -- `p`'s clock comes to read `t`, and `p` reacts at that reading. Also unconstrained:
  -- nothing here relates `t` to real time. `Execution.ClocksSound` forbids reading the
  -- future, `Synchronized` pins the clock to real time, `ClocksMonotone` forbids going
  -- backwards — each an assumption, none a fact of the model.
  | .tick p t => {
      Enabled c := p ∈ S.awake (c.time : Int)
      Effect c c' := Reacts Pr p .tick (setClock p t c) c'
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
def Step (Pr : Protocol Node Msg NodeState Ev) (S : Schedule Node) (a : Action Node Msg Ev)
    (c c' : Config Node Msg NodeState) : Prop :=
  (spec Pr S a).Enabled c ∧ (spec Pr S a).Effect c c'

/-- Case analysis on a step, one case per action, with the successor already computed.

    `Step` is a `def` — a conjunction — so `cases` cannot split it by action; every proof
    would otherwise open with `obtain ⟨-, res, -, h⟩; subst h` in each case. This does
    that once. Each case receives the action's enabling condition, the effect the
    protocol permitted, and a goal whose successor is the concrete configuration rather
    than an unknown constrained by an equation.

    It is the non-inductive equivalent of `cases` on an inductive step relation, and it
    is derived from `spec`, so it cannot drift from the step relation. -/
theorem Step.elim {Pr : Protocol Node Msg NodeState Ev} {S : Schedule Node}
    {motive : Action Node Msg Ev → Config Node Msg NodeState → Config Node Msg NodeState → Prop}
    {a : Action Node Msg Ev} {c c' : Config Node Msg NodeState} (h : Step Pr S a c c')
    (advance : ∀ (d : Config Node Msg NodeState) (t : Time),
      motive (.advance t) d { d with time := t })
    (tick : ∀ (d : Config Node Msg NodeState) (p : Node) (t : Time)
        (res : NodeStepResult NodeState Msg),
      (spec Pr S (.tick p t)).Enabled d →
      Pr.step p (setClock p t d)[p].clock (setClock p t d)[p].view (setClock p t d)[p].st
        .tick res →
      motive (.tick p t) d (applyNodeStepResult p res (setClock p t d)))
    (deliver : ∀ (d : Config Node Msg NodeState) (p : Node) (m : SignedMsg Node Msg)
        (res : NodeStepResult NodeState Msg),
      (spec Pr S (.deliver p m)).Enabled d →
      Pr.step p (receive p m d)[p].clock (receive p m d)[p].view (receive p m d)[p].st
        (.recv m) res →
      motive (.deliver p m) d (applyNodeStepResult p res (receive p m d)))
    (wake : ∀ (d : Config Node Msg NodeState) (p : Node) (res : NodeStepResult NodeState Msg),
      (spec Pr S (.wake p)).Enabled d →
      Pr.step p d[p].clock d[p].view d[p].st .wake res →
      motive (.wake p) d (applyNodeStepResult p res d))
    (custom : ∀ (d : Config Node Msg NodeState) (p : Node) (ev : Ev) (res : NodeStepResult NodeState Msg),
      (spec Pr S (.custom p ev)).Enabled d →
      Pr.step p d[p].clock d[p].view d[p].st (.custom ev) res →
      motive (.custom p ev) d (applyNodeStepResult p res d))
    (adversarial : ∀ (d : Config Node Msg NodeState) (p : Node) (m : Msg),
      (spec Pr S (.adversarial p m)).Enabled d →
      motive (.adversarial p m) d { d with sent := insert ⟨p, m⟩ d.sent }) :
    motive a c c' := by
  cases a with
  | advance t => obtain ⟨-, rfl⟩ := h; exact advance c t
  | tick p t => obtain ⟨he, res, hp, rfl⟩ := h; exact tick c p t res he hp
  | deliver p m => obtain ⟨he, res, hp, rfl⟩ := h; exact deliver c p m res he hp
  | wake p => obtain ⟨he, res, hp, rfl⟩ := h; exact wake c p res he hp
  | custom p ev => obtain ⟨he, res, hp, rfl⟩ := h; exact custom c p ev res he hp
  | adversarial p m => obtain ⟨he, rfl⟩ := h; exact adversarial c p m he

/-! ### Two invariants, proved through the eliminator

Not needed by the framework, but they are what the eliminator is for: each case arrives
with its successor already concrete, so the proof is one line per action with no
destructuring. -/

/-- The network never forgets. -/
theorem sent_mono {Pr : Protocol Node Msg NodeState Ev} {S : Schedule Node} {a : Action Node Msg Ev}
    {c c' : Config Node Msg NodeState} (h : Step Pr S a c c') : c.sent ⊆ c'.sent := by
  refine h.elim (motive := fun _ d d' => d.sent ⊆ d'.sent) ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun _ _ _ hx => hx
  · exact fun _ _ _ _ _ _ _ hx => Or.inl hx
  · exact fun _ _ _ _ _ _ _ hx => Or.inl hx
  · exact fun _ _ _ _ _ _ hx => Or.inl hx
  · exact fun _ _ _ _ _ _ _ hx => Or.inl hx
  · exact fun _ _ _ _ _ hx => Or.inr hx

/-! ### What the helpers do to each field

Two layers. First a read-back lemma per definition, saying what `c[p]` is after it — these
are what make brackets work as the normal form, since `simp` cannot otherwise reduce a
bracket applied to a literal record. Then the per-field consequences, which are what
invariant proofs actually cite.

`Config.setNode_apply` sits above both: since every setter goes through `setNode`, it is
the one lemma that turns a write into an `if`, and the read-back lemmas below are `rfl`
on top of it.

Only the second layer is `@[simp]`. The read-back lemmas are cited explicitly, because as
`simp` lemmas they fire first and expand a bracket into nested `if`s, after which the field
lemmas no longer match — the same shadowing that once made `applyNodeStepResult_clock` unusable, in the
opposite direction. -/

omit [DecidableEq Msg] in
theorem applyNodeStepResult_getElem (q : Node) (res : NodeStepResult NodeState Msg)
    (d : Config Node Msg NodeState) (p : Node) :
    (applyNodeStepResult q res d)[p] = if q = p then { d[q] with st := res.state } else d[p] :=
  rfl

theorem receive_getElem (q : Node) (m : SignedMsg Node Msg)
    (d : Config Node Msg NodeState) (p : Node) :
    (receive q m d)[p] = if q = p then { d[q] with view := insert m d[q].view } else d[p] :=
  rfl

omit [DecidableEq Msg] in
theorem setClock_getElem (q : Node) (t : Time) (d : Config Node Msg NodeState)
    (p : Node) : (setClock q t d)[p] = if q = p then { d[q] with clock := t } else d[p] := rfl

omit [DecidableEq Msg] in
@[simp] theorem applyNodeStepResult_clock (q : Node) (res : NodeStepResult NodeState Msg)
    (d : Config Node Msg NodeState) (p : Node) :
    (applyNodeStepResult q res d)[p].clock = d[p].clock := by
  by_cases hpq : q = p <;> simp [applyNodeStepResult_getElem, hpq]

omit [DecidableEq Msg] in
@[simp] theorem applyNodeStepResult_view (q : Node) (res : NodeStepResult NodeState Msg)
    (d : Config Node Msg NodeState) (p : Node) :
    (applyNodeStepResult q res d)[p].view = d[p].view := by
  by_cases hpq : q = p <;> simp [applyNodeStepResult_getElem, hpq]

omit [DecidableEq Msg] in
@[simp] theorem applyNodeStepResult_sent (q : Node) (res : NodeStepResult NodeState Msg)
    (d : Config Node Msg NodeState) :
    (applyNodeStepResult q res d).sent = d.sent ∪ (SignedMsg.mk q '' (res.send : Set Msg)) := rfl

@[simp] theorem receive_clock (q : Node) (m : SignedMsg Node Msg)
    (d : Config Node Msg NodeState) (p : Node) :
    (receive q m d)[p].clock = d[p].clock := by
  by_cases hpq : q = p <;> simp [receive_getElem, hpq]

@[simp] theorem receive_view_self (q : Node) (m : SignedMsg Node Msg)
    (d : Config Node Msg NodeState) :
    (receive q m d)[q].view = insert m d[q].view := by simp [receive_getElem]

@[simp] theorem receive_view_other (q : Node) (m : SignedMsg Node Msg)
    (d : Config Node Msg NodeState) (p : Node) (h : p ≠ q) :
    (receive q m d)[p].view = d[p].view := by simp [receive_getElem, Ne.symm h]

@[simp] theorem receive_sent (q : Node) (m : SignedMsg Node Msg)
    (d : Config Node Msg NodeState) : (receive q m d).sent = d.sent := rfl

omit [DecidableEq Msg] in
@[simp] theorem setClock_view (q : Node) (t : Time) (d : Config Node Msg NodeState)
    (p : Node) : (setClock q t d)[p].view = d[p].view := by
  by_cases hpq : q = p <;> simp [setClock_getElem, hpq]

omit [DecidableEq Msg] in
@[simp] theorem setClock_sent (q : Node) (t : Time) (d : Config Node Msg NodeState) :
    (setClock q t d).sent = d.sent := rfl

/-! `clock_mono` used to live here, proved from `tick` incrementing by one. It is gone:
a tick may now set any reading, so clock monotonicity is an *assumption*
(`Execution.ClocksMonotone`) rather than a fact of the step relation. That is the point
of weakening the spec — the old version made a scheduling decision look like a theorem. -/

/-- Initial configurations. -/
def Init (Pr : Protocol Node Msg NodeState Ev) (c : Config Node Msg NodeState) : Prop :=
  c.time = 0 ∧ (∀ p : Node, c[p] = { clock := 0, st := Pr.init p, view := ∅ }) ∧
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
def system (Node Msg NodeState Ev : Type) [DecidableEq Node] [DecidableEq Msg]
    (Pr : Protocol Node Msg NodeState Ev) (S : Schedule Node) :
    System (Config Node Msg NodeState) (Action Node Msg Ev) where
  Init := Init Pr
  Step := Step Pr S

end Framework.Sts2
