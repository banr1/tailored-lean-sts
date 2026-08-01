import Framework.Sts2C.Message
import Framework.Sts2C.Schedule
import Framework.Sts2C.Protocol
import Framework.Sts2C.Reachable
import Framework.Sts2C.Execution
import Framework.Sts2C.Models
import Framework.Sts2C.Example
import Framework.Sts2C.CustomEvents

/-!
# A framework for message-passing distributed protocols — presentation C

`Framework.Sts2` with the **reaction carried in the label**: `Action.tick p t res` rather
than `Action.tick p t`. A label plus a configuration then determine the successor, so `act`
is a function, `Step` is `enabled ∧ c' = act a c`, and no existential appears in the step
relation at all. Enabledness is syntactic *and* needs no feasibility obligation.

It is the cheapest of the three presentations to write down, and the one to be most careful
with. The saving is real; the cost does not show up in a line count. See
`Execution.WeakFair` — fairness can no longer be stated per label, so it is indexed by a
*set* of labels, and choosing that set correctly is a fresh judgement in every fairness
statement. The existential `Sts2` writes once inside `Reacts` reappears in every statement
that names an occurrence.

There is also a modelling objection worth weighing: a label is what the *scheduler* picks —
who acts, when, which message — whereas a `NodeStepResult` is picked by the node's own
program. Carrying it in the label says the schedule chooses an honest node's internal
decision.

Generic scaffolding: nothing here is about any particular protocol. A
specialization supplies three types (validators, messages, protocol state) and
one function — what a validator does at a round, given its view.

The design target is that the network and adversary models of **Majorum** (3SF)
and the sleepiness of **TOB-SVD** are both expressible as *instances*, not as
the framework's own commitments. `Framework.Sts2C.Models` states both, so that
claim is checked by the compiler rather than asserted.

## Modules

* `Message` — rounds, signed messages, views.
* `Schedule` — the adversary's choices over an execution: time-indexed
  corruption, awakeness *and* permission to act, plus both interval operators
  (awake *somewhere* vs awake *throughout*) and the constraints a model may
  impose on them.
* `Protocol` — `System` (the framework's own, so `Framework/` depends on nothing
  outside itself), `Protocol`, `Config`, and the step relation: a reaction-carrying `Action`,
  a syntactic `enabled`, the successor *function* `act`, and `Step := enabled ∧ c' = act a c`.
  A protocol reacts to **events**: `tick` and `recv m`, which the framework generates, plus
  `custom` events of the protocol's own type `Ev`, gated by `Protocol.enabled`.
* `Reachable` — reachability and `viewsSound`, by case analysis on the label.
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

* **Almost no proofs.** `sent_mono` and `viewsSound`, to make the comparison concrete;
  `step_act`/`enabled_iff`, which are this presentation's whole feasibility story; and
  `weakFair_singleton`, which checks that set-indexed fairness generalizes the per-label
  form. What the framework *will* own once it settles: a reusable "everything a correct
  validator signed is justified by its state" schema.
* **No blocks, chains or transaction pool.** They are reusable but they commit
  to chain-based protocols; the security definitions instead abstract over an
  output type and a prefix relation.
* **Nothing probabilistic.** Majorum's `wop`/`negl` statements and VRF
  unpredictability are out of reach without a probability layer; proposer
  election has to be idealized, as a sibling formalization does for signatures.
-/
