import StsReactionInLabel.Message
import StsReactionInLabel.Schedule
import StsReactionInLabel.Protocol
import StsReactionInLabel.Reachable
import StsReactionInLabel.Execution
import StsReactionInLabel.Models
import StsReactionInLabel.Example
import StsReactionInLabel.CustomEvents

/-!
# A framework for message-passing distributed protocols — reaction in the label (presentation C)

Formerly `Sts2C`. `Framework.StsRelationalSetLog` with **the reaction carried in the label**, and nothing else changed. Two
existentials disappear as a result:

* `StsRelationalSetLog`'s `NodeStep` is `∃ res, Pr.step … res ∧ c' = applyNodeStepResult …`. Here the reaction
  is supplied by the label, so `ActionSpec.Apply` is a *function*, `Step` is three conjuncts
  with no quantifier, and `ActionSpec.feasible` is unnecessary — a total function cannot fail
  to produce a successor. What is left of that obligation is `permits_total`, one lemma about
  the protocol.
* Weak fairness would normally break under such a label, since `x.lbl j = a` would name a
  *reaction* rather than an action, and "eventually taken" would force a validator to make
  every choice its protocol permits. It survives because the reaction is a **payload over**
  the action rather than an argument inside it: `Move = (a : Action) × Reaction a`, and
  `(x.lbl j).action = a` still says "this action occurred, whatever the node did" — with the
  payload projected away rather than existentially quantified.

That is the `Kind` technique, and it costs nothing here because `StsRelationalSetLog`'s `Action` *is* the
reaction-free alphabet: there is no second label type to invent and no erasure map to write,
since the erasure is `Sigma.fst`. The whole fairness layer is `StsRelationalSetLog`'s, one projection aside.

Generic scaffolding: nothing here is about any particular protocol. A
specialization supplies three types (validators, messages, protocol state) and
one function — what a validator does at a round, given its view.

The design target is that the network and adversary models of **Majorum** (3SF)
and the sleepiness of **TOB-SVD** are both expressible as *instances*, not as
the framework's own commitments. `Framework.StsReactionInLabel.Models` states both, so that
claim is checked by the compiler rather than asserted.

## Modules

* `Message` — rounds, signed messages, views.
* `Schedule` — the adversary's choices over an execution: time-indexed
  corruption, awakeness *and* permission to act, plus both interval operators
  (awake *somewhere* vs awake *throughout*) and the constraints a model may
  impose on them.
* `Protocol` — `System` (the framework's own, so `Framework/` depends on nothing
  outside itself), `Protocol`, `Config`, `Action` and its `Reaction` payload, `Move` their
  dependent pair, and the step relation: one `ActionSpec` per action with `Enabled` (the
  schedule), `Permits` (which reactions the protocol allows) and `Apply` (a function). A
  protocol reacts to **events**: `tick` and `recv m`, which the framework generates, plus
  `custom` events of the protocol's own type `Ev`, gated by `Protocol.enabled`.
* `Reachable` — reachability and `viewsSound`, by case analysis on the action.
* `Execution` — executions (recording the action taken at each step), the clock,
  network and fairness assumptions as predicates over them, and the security
  property definitions.
* `Models` — Majorum's and TOB-SVD's models, expressed.
* `Example` — a toy protocol placed under *both* models. Start here to see what
  a specialization has to supply.
* `CustomEvents` — a second toy protocol with two protocol-specific events (two
  timers), exercising `Event.custom` and `Protocol.enabled`, which `Example`
  leaves vacuous by taking `Ev := Empty`.

## Deliberate omissions

* **Almost no proofs.** `sent_mono` and `viewsSound`, which make the comparison with `StsRelationalSetLog`
  concrete; `permits_total` and `enabled_iff`, which are this presentation's whole
  feasibility story. What the framework *will* own once it settles: a reusable "everything a
  correct validator signed is justified by its state" schema.
* **No blocks, chains or transaction pool.** They are reusable but they commit
  to chain-based protocols; the security definitions instead abstract over an
  output type and a prefix relation.
* **Nothing probabilistic.** Majorum's `wop`/`negl` statements and VRF
  unpredictability are out of reach without a probability layer; proposer
  election has to be idealized, as a sibling formalization does for signatures.
-/
