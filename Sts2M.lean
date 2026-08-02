import Framework.Sts2M.Message
import Framework.Sts2M.Schedule
import Framework.Sts2M.Protocol
import Framework.Sts2M.Reachable
import Framework.Sts2M.Execution
import Framework.Sts2M.Models
import Framework.Sts2M.Example
import Framework.Sts2M.CustomEvents

/-!
# A framework for message-passing distributed protocols — multiset log

`Framework.Sts2` with **one type changed**: `Config.sent` is a `Multiset` rather than a
`Set`. That is enough to remove the existential from `Reacts`, and it does so without
touching the labels, so the fairness layer is untouched — the difference from `Sts2C`, which
buys the same thing by putting the reaction in the label.

Why the type is what matters: `∪` is lossy, so a reaction that re-sends a message already in
the log leaves no trace, and two different reactions can produce the same successor. The
witness in `Reacts` is therefore genuinely not a function of `(pre, c')`. Under `+` it is, and
`extract` computes it: the state is what `p`'s protocol state became, the messages are
`c'.sent - pre.sent`. `extract_applyNodeStepResult` is the round trip and
`reacts_iff_exists` proves the resulting relation is `Sts2`'s.

Two things this does not buy, both recorded at the definitions:

* **Case analysis gets no cheaper.** The successor equation `c' = applyNodeStepResult p
  (extract p pre c') pre` mentions `c'` on both sides, so `subst` cannot fire on it. `Step.elim`
  therefore converts back to the existential form — now a theorem rather than the definition —
  and every downstream proof is unchanged from `Sts2`.
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
the framework's own commitments. `Framework.Sts2M.Models` states both, so that
claim is checked by the compiler rather than asserted.

## Modules

* `Message` — rounds, signed messages, views.
* `Schedule` — the adversary's choices over an execution: time-indexed
  corruption, awakeness *and* permission to act, plus both interval operators
  (awake *somewhere* vs awake *throughout*) and the constraints a model may
  impose on them.
* `Protocol` — `System` (the framework's own, so `Framework/` depends on nothing
  outside itself), `Protocol`, `Config`, and the step relation. A protocol reacts to
  **events**: `tick` and `recv m`, which the framework generates, plus `custom`
  events of the protocol's own type `Ev`, gated by `Protocol.enabled`.
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

* **Almost no proofs.** `sent_mono` and `viewsSound` as in `Sts2`, plus the three that make
  this attempt's claim: `extract_applyNodeStepResult`, `reacts_iff_exists` and `reacts_total`.
  What the framework *will* own once it settles: a reusable "everything a correct validator
  signed is justified by its state" schema.
* **No blocks, chains or transaction pool.** They are reusable but they commit
  to chain-based protocols; the security definitions instead abstract over an
  output type and a prefix relation.
* **Nothing probabilistic.** Majorum's `wop`/`negl` statements and VRF
  unpredictability are out of reach without a probability layer; proposer
  election has to be idealized, as a sibling formalization does for signatures.
-/
