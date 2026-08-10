import StsStepInductive.Message
import StsStepInductive.Schedule
import StsStepInductive.Protocol
import StsStepInductive.Reachable
import StsStepInductive.Execution
import StsStepInductive.Models
import StsStepInductive.Example
import StsStepInductive.CustomEvents

/-!
# A framework for message-passing distributed protocols — inductive step (presentation A)

Formerly `Sts2A`. `Framework.StsRelationalSetLog` with **one thing changed**: `Step` is an inductive family, one
constructor per action, and `Enabled` is derived as `∃ c', Step …` rather than declared.
Everything else — `Protocol`, `Config`, the schedule, the execution predicates, both
models, both examples — is the same by construction, since this attempt began as a copy.
That is what makes it a controlled comparison; see `CONTEXT.md` for the measurements, and
the `Step` docstring in `Protocol.lean` for what the presentation does and does not buy.

Not a refactor of `StsRelationalSetLog` and not a replacement for it: per the repository's convention,
attempts coexist and are free to diverge.

Generic scaffolding: nothing here is about any particular protocol. A
specialization supplies three types (validators, messages, protocol state) and
one function — what a validator does at a round, given its view.

The design target is that the network and adversary models of **Majorum** (3SF)
and the sleepiness of **TOB-SVD** are both expressible as *instances*, not as
the framework's own commitments. `Framework.StsStepInductive.Models` states both, so that
claim is checked by the compiler rather than asserted.

## Modules

* `Message` — rounds, signed messages, views.
* `Schedule` — the adversary's choices over an execution: time-indexed
  corruption, awakeness *and* permission to act, plus both interval operators
  (awake *somewhere* vs awake *throughout*) and the constraints a model may
  impose on them.
* `Protocol` — `System` (the framework's own, so `Framework/` depends on nothing
  outside itself), `Protocol`, `Config`, and the step relation: here an `inductive Step`
  with the enabling conditions inline, `Enabled := ∃ c', Step …`, and one `iff` per action
  recovering the conditions syntactically. A protocol reacts to **events**: `tick` and
  `recv m`, which the framework generates, plus `custom` events of the protocol's own type
  `Ev`, gated by `Protocol.enabled`.
* `Reachable` — reachability and `viewsSound`, proved by plain `cases` on the step.
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

* **Almost no proofs.** Only the two that make the comparison concrete — `sent_mono` and
  `viewsSound` — plus the enabledness `iff`s that a model needs in order to check a
  fairness assumption. What the framework *will* own once it settles: a reusable
  "everything a correct validator signed is justified by its state" schema.
* **No blocks, chains or transaction pool.** They are reusable but they commit
  to chain-based protocols; the security definitions instead abstract over an
  output type and a prefix relation.
* **Nothing probabilistic.** Majorum's `wop`/`negl` statements and VRF
  unpredictability are out of reach without a probability layer; proposer
  election has to be idealized, as a sibling formalization does for signatures.
-/
