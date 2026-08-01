import Mathlib.Data.Set.Image
import Framework.Sts2C.Schedule

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
predicates on executions (`Framework.Sts2C.Execution`), so different models impose
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

namespace Framework.Sts2C

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
    `Framework.Sts2C.Execution` for the assumptions that pin it down. -/
def setClock (p : Node) (t : Time) (c : Config Node Msg NodeState) :
    Config Node Msg NodeState :=
  c.setNode p { c[p] with clock := t }

/-- Transition labels. Every label that runs a reaction **carries that reaction**.

    This is the defining choice of this attempt. Because the label names the reaction, a
    label plus a configuration determine the successor completely, so `act` below is a
    *function* and `Step` has no existential anywhere. The consequences, good and bad, are
    written up at `Step` and at `Execution.WeakFair`.

    Note the extra type parameter: labels now mention `NodeState`, so the alphabet of this
    transition system is no longer independent of the protocol's state. -/
inductive Action (Node Msg NodeState Ev : Type) where
  /-- Real time becomes `t`; no validator acts. -/
  | advance (t : Time)
  /-- `p`'s clock comes to read `t`, and `p` reacts at that reading with `res`. -/
  | tick (p : Node) (t : Time) (res : NodeStepResult NodeState Msg)
  /-- `m` is delivered to `p`, which reacts to it with `res`. -/
  | deliver (p : Node) (m : SignedMsg Node Msg) (res : NodeStepResult NodeState Msg)
  /-- `p` wakes up and reacts with `res`. -/
  | wake (p : Node) (res : NodeStepResult NodeState Msg)
  /-- A protocol-specific event fires at `p`, which reacts with `res`. -/
  | custom (p : Node) (ev : Ev) (res : NodeStepResult NodeState Msg)
  /-- An adversarial validator signs an arbitrary message. -/
  | adversarial (p : Node) (m : Msg)

/-- When a label may be taken.

    Syntactic, like `Sts2`'s `ActionSpec.Enabled`, but here it can afford to be: since the
    reaction is part of the label, `Pr.step … res` is just one more conjunct of the guard
    rather than something an existential has to find. That is the whole trick — the
    nondeterminism moved from the relation into the alphabet. -/
def enabled (Pr : Protocol Node Msg NodeState Ev) (S : Schedule Node) :
    Action Node Msg NodeState Ev → Config Node Msg NodeState → Prop
  -- Unconstrained: the framework does not say whether time moves forwards, by how much,
  -- or at all. `Execution.TimeMonotone` and friends decide that.
  | .advance _, _ => True
  -- Nothing here relates `t` to real time either; see `Execution.ClocksSound`.
  | .tick p t res, c => p ∈ S.awake (c.time : Int) ∧
      Pr.step p (setClock p t c)[p].clock (setClock p t c)[p].view (setClock p t c)[p].st
        .tick res
  -- Delivery to a sleeping validator is not enabled, which is how messages get queued.
  -- The message is filed before the reaction runs, so `step` sees it in the view too.
  | .deliver p m res, c => m ∈ c.sent ∧ p ∈ S.awake (c.time : Int) ∧
      Pr.step p (receive p m c)[p].clock (receive p m c)[p].view (receive p m c)[p].st
        (.recv m) res
  -- Awake now, asleep in the previous round.
  | .wake p res, c => p ∈ S.awake (c.time : Int) ∧ p ∉ S.awake ((c.time : Int) - 1) ∧
      Pr.step p c[p].clock c[p].view c[p].st .wake res
  -- A protocol-specific event, if the protocol allows it at the validator's own clock.
  | .custom p ev res, c => p ∈ S.awake (c.time : Int) ∧ Pr.enabled c[p].clock c[p].st ev ∧
      Pr.step p c[p].clock c[p].view c[p].st (.custom ev) res
  -- An adversarial validator signs anything.
  | .adversarial p m, c => p ∈ S.adv (c.time : Int)

/-- The configuration after taking `a`. A **function**, not a relation: this is what
    carrying the reaction in the label buys. -/
def act : Action Node Msg NodeState Ev → Config Node Msg NodeState → Config Node Msg NodeState
  | .advance t, c => { c with time := t }
  | .tick p t res, c => applyNodeStepResult p res (setClock p t c)
  | .deliver p m res, c => applyNodeStepResult p res (receive p m c)
  | .wake p res, c => applyNodeStepResult p res c
  | .custom p ev res, c => applyNodeStepResult p res c
  | .adversarial p m, c => { c with sent := insert ⟨p, m⟩ c.sent }

/-- The step relation: enabled, and then the one configuration the label produces.

    Compare the other two attempts. `Sts2` needs `ActionSpec.feasible` per action to keep a
    declared `Enabled` honest, and `Step.elim` to recover case analysis. `Sts2A` derives
    `Enabled` from the relation and pays six `iff` lemmas to get the conditions back
    syntactically. Here both problems dissolve: `Enabled` *is* syntactic, and feasibility is
    the one-line `step_act` below, because `act` is total. Case analysis is `obtain
    ⟨-, rfl⟩ := h` followed by `cases a` — one destructuring for the whole proof rather than
    one per case, since every successor is the single term `act a c`.

    The bill arrives in `Execution.lean`: a label is no longer something the *scheduler*
    chooses, since a `NodeStepResult` is chosen by the node's own program, and fairness can
    no longer be stated per label. -/
def Step (Pr : Protocol Node Msg NodeState Ev) (S : Schedule Node)
    (a : Action Node Msg NodeState Ev) (c c' : Config Node Msg NodeState) : Prop :=
  enabled Pr S a c ∧ c' = act a c

variable {Pr : Protocol Node Msg NodeState Ev} {S : Schedule Node}
    {a : Action Node Msg NodeState Ev} {c : Config Node Msg NodeState}

/-- Being enabled permits a step — Event-B's FIS, which here needs no per-action proof
    because `act` is a total function. This is `Sts2`'s six `feasible` fields and `Sts2A`'s
    six backward directions, in one line. -/
theorem step_act (h : enabled Pr S a c) : Step Pr S a c (act a c) := ⟨h, rfl⟩

/-- …and it is exactly enabledness, so nothing can promise more than the relation
    delivers. `Sts2A` gets this shape only action by action. -/
theorem enabled_iff : (∃ c', Step Pr S a c c') ↔ enabled Pr S a c :=
  ⟨fun ⟨_, he, _⟩ => he, fun h => ⟨_, step_act h⟩⟩

/-! ### One invariant, by one destructuring and `cases`

The same lemma the other two attempts prove. Here `Step` is again a conjunction, so it
opens with `obtain`, but **once** rather than once per case: the successor is `act a c` for
every label, so there is a single equation to substitute before the case split. -/

/-- The network never forgets. -/
theorem sent_mono {a : Action Node Msg NodeState Ev} {c c' : Config Node Msg NodeState}
    (h : Step Pr S a c c') : c.sent ⊆ c'.sent := by
  obtain ⟨-, rfl⟩ := h
  cases a with
  | advance t => exact fun _ hx => hx
  | tick p t res => exact fun _ hx => Or.inl hx
  | deliver p m res => exact fun _ hx => Or.inl hx
  | wake p res => exact fun _ hx => Or.inl hx
  | custom p ev res => exact fun _ hx => Or.inl hx
  | adversarial p m => exact fun _ hx => Or.inr hx

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
    System (Config Node Msg NodeState) (Action Node Msg NodeState Ev) where
  Init := Init Pr
  Step := Step Pr S

end Framework.Sts2C
