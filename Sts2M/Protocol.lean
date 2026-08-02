import Mathlib.Data.Set.Image
import Framework.Sts2M.Schedule

/-!
# Protocols and the system they induce — the specification

Definitions only. The theorems about them — what each helper does to each field, the two
eliminators, and what a `NodeStep` may and may not touch — are in
`Framework.Sts2M.Lemmas`, so that reading the model does not mean reading its proofs.

Three proofs stay here, because a *definition* needs them: `extract_applyNodeStepResult`,
`nodeStep_iff_exists` and `nodeStep_total`, the last of which discharges
`ActionSpec.feasible` inside `spec`. That obligation is why the split cannot be perfectly
clean. The two `rfl` read-backs `nodes_apply` and `Config.setNode_apply` also stay, beside
the definitions they unfold and because the proofs above need them.

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
predicates on executions (`Framework.Sts2M.Execution`), so different models impose
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

namespace Framework.Sts2M

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
  /-- Messages sent, each signed by the reacting validator.

      A multiset, to match `Config.sent`. With a `Finset` here the two types disagree: the
      log's delta can hold a message twice and a reaction cannot produce that, so
      `applyNodeStepResult` is injective but not onto the `p`-signed extensions, and
      `extract` has to deduplicate to cross the gap. Matching the types makes the two
      mutually inverse — see `applyNodeStepResult_surjective`.

      The cost is a distinction with no protocol meaning: sending `m` twice in one step now
      differs from sending it once, and since views are `Finset`s no validator can tell. That
      is the same extra distinction `Config.sent` already introduced, so the model is at least
      uniform about it. -/
  send : Multiset Msg

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
  /-- Every message ever signed, **with multiplicity**. Monotone.

      A multiset rather than a set, and that single choice is what this attempt is about:
      `∪` is lossy, so a reaction that re-sends a message already in the log leaves no trace
      and cannot be recovered from `(pre, post)`. That is what forces `NodeStep` to be an
      existential in `Sts2` — the witness genuinely is not a function of the two
      configurations. With `+` it is, and `extract` below computes it.

      The price is that multiplicity is now observable state: two executions differing only
      in how many times a message was sent are different configurations. Nothing stated in
      this framework can tell them apart, since every property is membership-based, but the
      model does distinguish more than the protocol semantics needs. It also makes `sent`
      finite by typing, which reachable configurations were anyway. -/
  sent : Multiset (SignedMsg Node Msg)

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
      with sent := c.sent + res.send.map (SignedMsg.mk p) }

/-- `p`'s clock now reads `t`. The framework says nothing about which `t` — see
    `Framework.Sts2M.Execution` for the assumptions that pin it down. -/
def setClock (p : Node) (t : Time) (c : Config Node Msg NodeState) :
    Config Node Msg NodeState :=
  c.setNode p { c[p] with clock := t }

/-- The reaction that took `pre` to `c'`, read straight out of the two configurations.

    `state` was always recoverable — it is just what `p`'s protocol state became. `send` is
    the point: because the log is a multiset, the messages this step added are exactly
    `c'.sent - pre.sent`, and every one of them was signed by `p`, so no filtering by signer
    is needed. Under `Sts2`'s `Set` log this function cannot exist: `∪` forgets a re-send, so
    two different reactions can produce the same successor. -/
def extract (p : Node) (pre c' : Config Node Msg NodeState) : NodeStepResult NodeState Msg :=
  { state := c'[p].st, send := (c'.sent - pre.sent).map SignedMsg.msg }

/-- The round trip: applying a reaction and reading it back is the identity. This is the
    lemma the whole attempt rests on. -/
@[simp] theorem extract_applyNodeStepResult (p : Node) (res : NodeStepResult NodeState Msg)
    (pre : Config Node Msg NodeState) :
    extract p pre (applyNodeStepResult p res pre) = res := by
  obtain ⟨st, snd⟩ := res
  have hsub : (applyNodeStepResult p ⟨st, snd⟩ pre).sent - pre.sent
      = snd.map (SignedMsg.mk p) := by
    ext a; simp [applyNodeStepResult]
  -- the `sent` update leaves `nodes` alone, so this is the `setNode` read-back
  have hst : (applyNodeStepResult p ⟨st, snd⟩ pre)[p].st = st := by
    show (pre.setNode p { pre[p] with st := st })[p].st = st
    simp
  simp [extract, hsub, hst, Multiset.map_map, Function.comp_def]

/-- `NodeStep Pr p e pre c'` — `c'` is the configuration `p` reaches by reacting to `e` in
    `pre`.

    **No existential.** `Sts2` has to write `∃ res, Pr.step … res ∧ c' = …` because the
    reaction is not a function of `(pre, c')`; here it is, so the same statement is two
    quantifier-free conjuncts: the protocol permits the reaction that `c'` exhibits, and `c'`
    is what applying it produces. The second conjunct is what rules out a `c'` that differs
    from `pre` in some way no reaction could have caused.

    `nodeStep_iff_exists` below proves this is `Sts2`'s relation and not a different one. -/
def NodeStep (Pr : Protocol Node Msg NodeState Ev) (p : Node) (e : Event Node Msg Ev)
    (pre c' : Config Node Msg NodeState) : Prop :=
  Pr.step p pre[p].clock pre[p].view pre[p].st e (extract p pre c') ∧
    c' = applyNodeStepResult p (extract p pre c') pre

/-- The same relation `Sts2` defines — so this attempt changes the *spelling* of the step
    relation, not the model. Only the multiset log is a real change, and it is one this
    equivalence does not paper over: it is what makes the right-hand side collapse. -/
theorem nodeStep_iff_exists (Pr : Protocol Node Msg NodeState Ev) (p : Node)
    (e : Event Node Msg Ev) (pre c' : Config Node Msg NodeState) :
    NodeStep Pr p e pre c' ↔
      ∃ res, Pr.step p pre[p].clock pre[p].view pre[p].st e res ∧
        c' = applyNodeStepResult p res pre := by
  constructor
  · rintro ⟨hstep, hc⟩
    exact ⟨extract p pre c', hstep, hc⟩
  · rintro ⟨res, hstep, rfl⟩
    exact ⟨by simpa using hstep, by simp⟩

/-- Reacting is always possible, from `Protocol.total`. Every action whose effect is
    a reaction discharges its `feasible` with this. -/
theorem nodeStep_total (Pr : Protocol Node Msg NodeState Ev) (p : Node) (e : Event Node Msg Ev)
    (pre : Config Node Msg NodeState) : ∃ c', NodeStep Pr p e pre c' := by
  obtain ⟨res, he⟩ := Pr.total p pre[p].clock pre[p].view pre[p].st e
  exact ⟨_, (nodeStep_iff_exists Pr p e pre _).2 ⟨res, he, rfl⟩⟩

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
      Effect c c' := NodeStep Pr p .tick (setClock p t c) c'
      feasible _ _ := nodeStep_total Pr p .tick _ }
  -- Any sent message may be delivered to any awake validator, at any time.
  -- Delivery to a sleeping validator is simply not enabled, which is how messages
  -- get queued: they stay in `sent` until it wakes. The message is filed before the
  -- reaction runs, so `step` sees it in the view too.
  | .deliver p m => {
      Enabled c := m ∈ c.sent ∧ p ∈ S.awake (c.time : Int)
      Effect c c' := NodeStep Pr p (.recv m) (receive p m c) c'
      feasible _ _ := nodeStep_total Pr p (.recv m) _ }
  -- Awake now, asleep in the previous round. Reported because a protocol cannot
  -- start a joining procedure it is not told about.
  | .wake p => {
      Enabled c := p ∈ S.awake (c.time : Int) ∧ p ∉ S.awake ((c.time : Int) - 1)
      Effect c c' := NodeStep Pr p .wake c c'
      feasible _ _ := nodeStep_total Pr p .wake _ }
  -- A protocol-specific event, if the protocol allows it at the validator's own
  -- clock reading.
  | .custom p ev => {
      Enabled c := p ∈ S.awake (c.time : Int) ∧ Pr.enabled c[p].clock c[p].st ev
      Effect c c' := NodeStep Pr p (.custom ev) c c'
      feasible _ _ := nodeStep_total Pr p (.custom ev) _ }
  -- An adversarial validator signs anything.
  | .adversarial p m => {
      Enabled c := p ∈ S.adv (c.time : Int)
      Effect c c' := c' = { c with sent := ⟨p, m⟩ ::ₘ c.sent }
      feasible _ _ := ⟨_, rfl⟩ }

/-- The step relation: enabled, and then the effect. *When* messages must be
    delivered, and whether clocks agree with real time, are properties of the model,
    imposed on executions rather than here. -/
def Step (Pr : Protocol Node Msg NodeState Ev) (S : Schedule Node) (a : Action Node Msg Ev)
    (c c' : Config Node Msg NodeState) : Prop :=
  (spec Pr S a).Enabled c ∧ (spec Pr S a).Effect c c'

/-- Initial configurations. -/
def Init (Pr : Protocol Node Msg NodeState Ev) (c : Config Node Msg NodeState) : Prop :=
  c.time = 0 ∧ (∀ p : Node, c[p] = { clock := 0, st := Pr.init p, view := ∅ }) ∧
    c.sent = 0

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

end Framework.Sts2M
