import StsMultisetLog.Spec.Message
import StsMultisetLog.Spec.Schedule
import StsMultisetLog.Spec.Protocol
import StsMultisetLog.Spec.Execution
import StsMultisetLog.Analysis.Lemmas
import StsMultisetLog.Analysis.Reachable
import StsMultisetLog.Analysis.Justified
import StsMultisetLog.Analysis.Execution
import StsMultisetLog.Examples.Models
import StsMultisetLog.Examples.Example
import StsMultisetLog.Examples.CustomEvents

/-!
# A framework for message-passing distributed protocols — multiset log

**The suggested flavour**, and the most general of the five: it is the only one carrying the
full set of proofs, and it is where new work happens, so its API is the one treated as fixed —
a rename or a retyping of anything it exports is announced, not slipped in. Its own `Example`,
`CustomEvents` and `Models` files exercise it, so `make StsMultisetLog` checks it standalone.

It is organized by role — `Spec/` states the model, `Analysis/` proves things about it,
`Examples/` demonstrates it — and every repeated binder is declared once, in a section
`variable` block, rather than written out per declaration. It reached that shape as a fork
(`Sts2MX`) of a flat version of the same framework (`Sts2M`), which it superseded and which was
removed on 2026-08-10; `CONTEXT.md` records what the two differed in and what the measurements
were.

## The multiset log

`Framework.StsRelationalSetLog` with **one type changed**: `Config.sent` is a `Multiset` rather than a
`Set`. That is enough to remove the existential from `NodeStep`, and it does so without
touching the labels, so the fairness layer is untouched — the difference from `StsReactionInLabel`, which
buys the same thing by putting the reaction in the label.

Why the type is what matters: `∪` is lossy, so a reaction that re-sends a message already in
the log leaves no trace, and two different reactions can produce the same successor. The
witness in `NodeStep` is therefore genuinely not a function of `(pre, c')`. Under `+` it is, and
`extract` computes it: the state is what `p`'s protocol state became, the messages are
`c'.sent - pre.sent`. `extract_applyNodeStepResult` is the round trip and
`nodeStep_iff_exists` proves the resulting relation is `StsRelationalSetLog`'s.

`NodeStepResult.send` is a multiset for the same reason, and the two changes belong together.
With a `Finset` there the types disagree — a log delta can hold a message twice, a reaction
cannot produce that — so `applyNodeStepResult` is injective but *not onto* the `p`-signed
extensions, and `extract` has to deduplicate to cross the gap. Matching them makes the two
mutually inverse: `applyNodeStepResult_surjective` says every `p`-signed extension is some
reaction's doing, so the model has no unreachable successors.

Two things this does not buy, both recorded at the definitions:

* **Case analysis gets no cheaper.** The successor equation `c' = applyNodeStepResult p
  (extract p pre c') pre` mentions `c'` on both sides, so `subst` cannot fire on it. `Step.elim`
  therefore converts back to the existential form — now a theorem rather than the definition —
  and every downstream proof is unchanged from `StsRelationalSetLog`.
* **It is a model change, not a spelling change.** Multiplicity becomes observable state: two
  executions differing only in how often a message was sent are now different configurations.
  Nothing stated here can tell them apart, since every property is membership-based, but the
  model distinguishes more than the protocol semantics needs. Weigh that against removing an
  existential that was, semantically, invisible — when two reactions give the same successor
  they give the same *transition*.

Generic scaffolding: nothing here is about any particular protocol. A
specialization supplies three types (validators, messages, protocol state) and
one function — what a validator does at a round, given its view.

The design target is that the network and adversary models of **Majorum** (3SF)
and the sleepiness of **TOB-SVD** are both expressible as *instances*, not as
the framework's own commitments. `Framework.StsMultisetLog.Models` states both, so that
claim is checked by the compiler rather than asserted.

## Layout

Three directories, on one rule: **`Spec/` is the model; `Analysis/` is what has been proved
about the model.** Note that the line is not `def` versus `theorem`. A definition that exists
only to be some theorem's conclusion or hypotheses — `Reachable`, `ViewsSound`, `Justified`,
`Justifies` — belongs under `Analysis/` beside the theorem it serves, and does live there. The
test is whether the model refers to it: none of those four is mentioned by `Step`, `Init`,
`Execution` or `Models`, nor by any protocol built on the framework.

`Spec/`

* `Message` — rounds, signed messages, views.
* `Schedule` — the adversary's choices over an execution: time-indexed corruption, awakeness
  *and* permission to act, plus both interval operators (awake *somewhere* vs awake
  *throughout*) and the constraints a model may impose on them.
* `Protocol` — `System` (the framework's own, so `Framework/` depends on nothing outside
  itself), `Protocol`, `Config`, and the step relation. Its binders come from section
  `variable`s; see the module's own docstring for what that constrains. A protocol reacts to **events**:
  `tick` and `recv m`, which the framework generates, plus `custom` events of the protocol's
  own type `Ev`, gated by `Protocol.enabled`.
* `Execution` — executions (recording the action taken at each step), the clock, network and
  fairness assumptions as predicates over them, and the security property definitions.
`Analysis/`

* `Lemmas` — everything proved *about* `Spec.Protocol`: the field lemmas, the two eliminators
  (`Step.elim` and `Step.elimR`), `sent_mono`, and the frame lemmas with their converse.
* `Reachable` — the reachability relation, the `ViewsSound` predicate, and `viewsSound`:
  everything in a view really was signed and sent, everywhere reachable, so no model need
  assume it.
* `Justified` — `Justified` and `Justifies` (the conclusion and the protocol's obligations),
  and the invariant itself: everything an honest validator signed is justified by its current
  state. The same invariant as `StsRelationalSetLog.Justified`, proved from the frame lemmas instead of
  `Step.elim`; the two files exist to be compared, see `CONTEXT.md`.
* `Execution` — what holds of every execution: `TimeStepwise.timeMonotone`,
  `Execution.reachable`, and `views_sound`.

`Examples/`

* `Models` — Majorum's and TOB-SVD's models assembled from the à-la-carte predicates, so
  `Example` has something to place a protocol under. **Not** the authoritative statement of
  either paper's model — the protocol directories supersede it; see its own docstring.
* `Example` — a toy protocol placed under *both* models. Start here to see what a
  specialization has to supply.
* `CustomEvents` — a second toy protocol with two protocol-specific events (two timers),
  exercising `Event.custom` and `Protocol.enabled`, which `Example` leaves vacuous by taking
  `Ev := Empty`.

### The one exception

`Spec/Protocol.lean` keeps five theorems, and they are there because a **definition** needs
them: `spec`'s `feasible` field is Event-B's FIS obligation, discharged by `nodeStep_total`,
which rests in turn on `nodeStep_iff_exists`, `extract_applyNodeStepResult` and the two `rfl`
read-backs `nodes_apply` and `Config.setNode_apply`. Moving them to `Analysis/` would make a
`Spec/` file import an `Analysis/` one, which is a worse trade than the exception. Every other
theorem in the framework lives under `Analysis/`.

## Deliberate omissions

* **Almost no proofs.** `sent_mono` and `viewsSound` as in `StsRelationalSetLog`; the three that make this
  attempt's claim — `extract_applyNodeStepResult`, `applyNodeStepResult_surjective` and
  `nodeStep_iff_exists`; and the frame lemmas (`NodeStep.time`, `.other`, `.clock`, `.view`,
  `.sent_le`, `.sent_signed`) with their converse `nodeStep_of_frame`, which say exactly what a
  reaction may and may not touch.
  What the framework *will* own once it settles: a reusable "everything a correct validator
  signed is justified by its state" schema.
* **No blocks, chains or transaction pool.** They are reusable but they commit
  to chain-based protocols; the security definitions instead abstract over an
  output type and a prefix relation.
* **Nothing probabilistic.** Majorum's `wop`/`negl` statements and VRF
  unpredictability are out of reach without a probability layer; proposer
  election has to be idealized, as a sibling formalization does for signatures.
-/
