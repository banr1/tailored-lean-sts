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
with. The saving is real; the cost does not show up in a line count. Fairness can no longer
be stated per label — `x.lbl j = a` would name a *reaction* — so it is stated at a `Kind`,
the label with the reaction erased and everything else pinned. That confines the reaction's
existential to one definition (`WeakFairKind`) and makes the dangerous mistake unavailable:
sets of labels can be widened, and widening is monotone in neither direction, whereas kinds
cannot be unioned. `weakFairKind_iff` and `diligent_iff_res` keep both claims honest.

The upshot is that this presentation needs **two** alphabets: `Kind`, which says what
happened, and `Action = (k : Kind) × Reaction k`, which determines the successor.
`Kind Node Msg Ev` is precisely `Sts2`'s `Action` — so C converges on B's alphabet for talking
about occurrences while keeping a richer one for the step relation.

`Kind` is the *primary* type and the reaction is a payload over it, rather than `Action` being
an inductive with a hand-written erasure to `Kind`. That was a deliberate second pass: a
hand-written erasure is a place to be wrong, and while `enabledKind_iff` happens to catch the
obvious errors — its forward direction demands a label of every kind — surjectivity is not the
same as being the intended map, and the protection depended on the luck of these six
signatures. As a dependent pair the erasure is `Sigma.fst`, right by definition, and
`enabledKind_iff` loses its `a.kind = k` equation entirely.

There is also a modelling objection worth weighing: a label is what the *scheduler* picks —
who acts, when, which message — whereas a `NodeStepResult` is picked by the node's own
program. Carrying it in the label says the schedule chooses an honest node's internal
decision. Two alphabets and an erasure map is arguably the honest response to that, rather
than a workaround for it.

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
  outside itself), `Protocol`, `Config`, and the step relation: `Kind` and `Reaction` with
  `Action` their dependent pair, the syntactic guards `enabled` and `enabledKind`, the
  successor *function* `act`, and `Step := enabled ∧ c' = act a c`.
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
