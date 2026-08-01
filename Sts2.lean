import Framework.Sts2.Message
import Framework.Sts2.Schedule
import Framework.Sts2.Protocol
import Framework.Sts2.Execution
import Framework.Sts2.Models
import Framework.Sts2.Example
import Framework.Sts2.CustomEvents

/-!
# A framework for message-passing distributed protocols

Generic scaffolding: nothing here is about any particular protocol. A
specialization supplies three types (validators, messages, protocol state) and
one function — what a validator does at a round, given its view.

The design target is that the network and adversary models of **Majorum** (3SF)
and the sleepiness of **TOB-SVD** are both expressible as *instances*, not as
the framework's own commitments. `Framework.Sts2.Models` states both, so that
claim is checked by the compiler rather than asserted.

## Modules

* `Message` — rounds, signed messages, views.
* `Schedule` — the adversary's choices over an execution: time-indexed
  corruption, awakeness *and* permission to act, plus both interval operators
  (awake *somewhere* vs awake *throughout*) and the constraints a model may
  impose on them.
* `Protocol` — `Protocol`, `Config`, and the step relation. A protocol reacts to
  **events**: `tick` and `recv m`, which the framework generates, plus `custom`
  events of the protocol's own type `Ev`, gated by `Protocol.enabled`.
* `Execution` — executions, and every network/participation assumption as a
  predicate over them, plus the security property definitions.
* `Models` — Majorum's and TOB-SVD's models, expressed.
* `Example` — a toy protocol placed under *both* models. Start here to see what
  a specialization has to supply.
* `CustomEvents` — a second toy protocol with two protocol-specific events (two
  timers), exercising `Event.custom` and `Protocol.enabled`, which `Example`
  leaves vacuous by taking `Ev := Empty`.

## Deliberate omissions

* **No proofs.** The structure is still being iterated on; invariants would only
  slow that down. What the framework *will* own once it settles: view soundness,
  network monotonicity, and a reusable "everything a correct validator signed is
  justified by its state" schema.
* **No blocks, chains or transaction pool.** They are reusable but they commit
  to chain-based protocols; the security definitions instead abstract over an
  output type and a prefix relation.
* **Nothing probabilistic.** Majorum's `wop`/`negl` statements and VRF
  unpredictability are out of reach without a probability layer; proposer
  election has to be idealized, as a sibling formalization does for signatures.
-/
