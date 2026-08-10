# sts-framework — five flavours of a protocol framework

A protocol-independent framework for message-passing distributed protocols: rounds, signed
messages, views, the adversary's schedule, `Protocol`/`Config`/`Step`, executions, and the
network and sleepiness assumptions. Protocol models are *instances* of it.

There are five flavours. Each isolates **one** design choice, and they are deliberately
independent: no flavour imports another, nothing is shared between them, and duplication is
the point — a flavour must stay free to diverge. Pick one and import it.

## The theory it rests on

A protocol model here is a **labelled state transition system**, in the standard sense: a set of
states, a predicate saying which states may be initial, and a relation saying which labelled
transitions are allowed. That is literally the interface — `System` has exactly two fields,
`Init : SystemState → Prop` and `Step : Label → SystemState → SystemState → Prop`
([Spec/Protocol.lean:413](StsMultisetLog/Spec/Protocol.lean#L413)), and `system` builds one from a
`Protocol` and a `Schedule`.

**States and labels.** A state is a whole `Config`: global time, every validator's clock, state
and view, and the log of messages sent. A label is an `Action` — which validator did what, or
what the environment did. Keeping the actor in the label is what lets a property say "a tick of
`p` happened at time `r`" rather than only "the state changed".

**Why a relation and not a function.** Two sources of nondeterminism have to survive into the
model: the adversary's, which the `Schedule` fixes up front, and the *protocol's own* — a
specification that permits several reactions must not be forced to choose. Hence `Pr.step … res`
is a relation over reactions, and a transition exists for each permitted one. The price is a
proof obligation: an action whose condition holds must actually have a successor. That is
`ActionSpec.feasible`, which is Event-B's **FIS** (feasibility) obligation, and the source says
so at the definition.

**Behaviours.** `Exec` is an infinite sequence of configurations with the label taken at each
index, so `x[i]` is a state and `x.lbl i` the action that led out of it. Everything else is a
predicate *over* executions.

**Assumptions live in the predicates, not in the model.** The step relation deliberately allows
executions no real network would produce — time that never advances, clocks that disagree,
messages that are never delivered. What rules those out are named assumptions you *choose* to
impose: `TimeMonotone`, `ClocksSound`, `SynchronizedClocks`, `Diligent`, `Synchrony gst delta`,
`Relay`, `TimeDiverges`. A theorem then states which ones it needed, which is the point — an
assumption baked into the transition relation cannot be discharged, weakened, or compared
across models.

**Fairness** is two of those predicates, in their usual forms: `WeakFair` (an action that stays
enabled is eventually taken) and `StrongFair` (an action enabled infinitely often is taken
infinitely often), stated via `Execution.Enabled`
([Spec/Execution.lean:149](StsMultisetLog/Spec/Execution.lean#L149)). Liveness properties need
them; safety properties do not.

**Safety, liveness, security.** `Safe` says nothing bad ever happens — concretely, that the
outputs of validators honest at the time are always prefix-comparable; `Live` says something good
eventually does — a transaction in the pool is output by every awake validator within `tconf`;
`Secure` is their conjunction. Those are Majorum's Definitions 1–3, and the split is the
classical one, which is why the two kinds of property need different assumptions: liveness needs
fairness, safety must not.

**Invariants come by induction over reachability.** `Reachable` is an inductive relation, and a
property of every reachable state is proved by induction over it: `viewsSound` (no view contains
a message that was never signed and sent) and the `Justified` invariant (everything an honest
validator signed is justified by its state) are both of that shape. `Execution.reachable` links
the two worlds, since every configuration of an execution is reachable.

**What is deliberately out of scope.** No probability: statements of the form "with overwhelming
probability" and unpredictable proposer election cannot be said here, so proposer choice is
idealized and signatures are perfect. No blocks or chains either — the security definitions
abstract over an output type and a prefix relation instead.

### Background reading

- Lamport, *Specifying Systems* — the standard treatment of specifying systems as initial
  predicate plus next-state relation, and of fairness as `WF`/`SF`. Free PDF:
  <https://lamport.azurewebsites.net/tla/book.html>
- Lamport, *The Temporal Logic of Actions* (1994) — where that formulation comes from:
  <https://lamport.azurewebsites.net/pubs/pubs.html#lamport-actions>
- Alpern and Schneider, *Defining Liveness* (1985) — the safety/liveness classification the
  `Safe`/`Live` split follows: <https://doi.org/10.1016/0020-0190(85)90056-0>
- Abrial, *Modeling in Event-B* — where the FIS obligation that `feasible` discharges is
  defined: <https://doi.org/10.1017/CBO9781139195881>; method wiki at
  <http://wiki.event-b.org/index.php/Main_Page>
- Baier and Katoen, *Principles of Model Checking* (MIT Press, 2008) — transition systems,
  fairness, and the linear-time properties, as a textbook.
- Mathlib documentation, for `Multiset`, `Set` and `Finset` as used by the message log:
  <https://leanprover-community.github.io/mathlib4_docs/>

The two protocol models the framework was built to express, and whose disagreements forced the
parameterisation, are Majorum (a.k.a. 3SF) and TOB-SVD, D'Amato, Saltini, Tran and Zanolini,
ICDCS 2025 — <https://arxiv.org/abs/2310.11331>. `Examples/Models` states both, with the caveat
recorded in its own docstring.

## The five flavours

What every flavour gives you, identically. You supply three types — validators (`Node`), messages
(`Msg`), protocol state (`NodeState`) — a type `Ev` of protocol-specific events, and a `Protocol`
with four fields: `init` (each validator's starting state), `step p clock view s e res` (`res` is
*a* reaction `p` may have to event `e`, given its clock reading, view and state), `total` (every
event has at least one reaction) and `enabled` (when a `custom` event may fire). A reaction is a
`NodeStepResult`: the new state, and the messages sent. The four events a protocol reacts to are
`tick`, `recv m`, `wake` and `custom ev`.

The framework supplies the rest: `Config` (global `time`, each validator's `Local` record of
clock, state and view, and the log of messages `sent`), `Schedule` (who is corrupt, awake, and
permitted to act, at each time), the six transition labels `advance`, `tick`, `deliver`, `wake`,
`custom`, `adversarial`, the relation `Step` between configurations, `Init`, `system`, `Exec` for
executions, the network and fairness assumptions as predicates over executions, and the two
models in `Models`.

So each flavour below is a complete framework in its own right. What differs between them is
**how `Step` is written down**, and what that costs every proof built on it — expand a row for
the whole story.

| Flavour | What it is | Role |
| --- | --- | --- |
| `StsMultisetLog` | A framework whose message log is a <code>Multiset</code>, so a step's reaction is a <i>function</i> of the step rather than something quantified over. Organized by role: <code>Spec/</code> states the model, <code>Analysis/</code> proves things about it, <code>Examples/</code> demonstrates it. <details><summary>Full description</summary><p><b>Why a multiset.</b> With a <code>Set</code> log, <code>∪</code> is lossy: a reaction that re-sends a message already in the log leaves no trace, and two different reactions can produce the very same successor configuration. So <i>what did <code>p</code> do?</i> is genuinely not a function of <code>(pre, c')</code>, and the step relation has to quantify over the reaction. Under <code>+</code> it <i>is</i> a function, and <code>extract</code> computes it — the new state is what <code>p</code>'s state became, the messages are <code>c'.sent - pre.sent</code>. <code>extract_applyNodeStepResult</code> is the round trip, and <code>applyNodeStepResult_surjective</code> says every <code>p</code>-signed extension of the log is some reaction's doing, so the model admits no unreachable successors.</p><p><b>What that costs.</b> Multiplicity becomes observable state: two executions differing only in how often a message was sent are now different configurations. Nothing stated here can tell them apart — every property is membership-based — but the model does distinguish more than the protocol semantics needs. And case analysis gets no cheaper: the successor equation mentions <code>c'</code> on both sides, so <code>subst</code> cannot fire, and <code>Step.elim</code> converts back to the existential form, now a theorem rather than the definition. Two forms of the step relation therefore coexist, and a proof must pick the eliminator that matches — <code>Step.elim</code> for the existential form, <code>Step.elimR</code> for the frame-lemma form.</p><p><b>What it proves.</b> Under <code>Analysis/</code>: the frame lemmas (<code>Lemmas</code>), reachability and view soundness (<code>Reachable</code>, <code>Execution</code>), and "everything an honest validator signed is justified by its state" (<code>Justified</code>). <code>Spec/Protocol.lean</code> keeps five theorems as a documented exception — three substantive (<code>extract_applyNodeStepResult</code>, <code>nodeStep_iff_exists</code>, <code>nodeStep_total</code>) and two <code>rfl</code> read-backs — because <code>spec</code>'s <code>feasible</code> field is a <i>definition</i> that needs them.</p><p><b>Binders come from section variables.</b> Every repeated binder is declared once per section instead of at each declaration. Two traps if you edit there: <code>Action</code> must be declared above the block, or <code>Step</code>'s signature becomes <code>(Pr) (S) (c) (c') (a)</code> and <code>system</code> loses <code>Step := Step Pr S</code>; and <code>Config.setNode</code> takes <code>(p) (r) (c)</code>, so that <code>receive</code>, <code>applyNodeStepResult</code> and <code>setClock</code> keep their deliberate configuration-last order.</p></details> | **suggested**, and the most general |
| `StsStepInductive` | A framework whose step relation is an <code>inductive</code> family — one constructor per action, enabling conditions inline — with enabledness <i>derived</i> as <code>∃ c', Step …</code> instead of declared. <details><summary>Full description</summary><p><b>What the shape buys.</b> There is no <code>feasible</code> obligation for the protocol author to discharge: a constructor that exists <i>is</i> the witness that an enabled action has a successor. Six <code>iff</code> lemmas (<code>enabled_advance</code>, <code>enabled_tick</code>, …) recover each action's condition syntactically for whoever needs to read it back.</p><p><b>The measured result: a wash.</b> 531 code lines against the baseline's 533, with the step layer 72 lines against 84. The two shared proofs come out the same length, and <code>viewsSound</code> is marginally <i>longer</i> under <code>cases</code>, because the constructor patterns spread over more lines than <code>Step.elim</code>'s single <code>intro</code>. The miniature experiment that predicted a large win for this shape — 18 statement lines against 39 — did not survive the move to six real actions.</p><p><b>Why it is kept.</b> It answers "is an inductive step cheaper?" with "no, and not more expensive either", which is why the choice between presentations had to be made on other grounds.</p></details> | one design choice changed |
| `StsReactionInLabel` | A framework whose labels carry the reaction as a payload over the action, <code>Move = (a : Action) × Reaction a</code>, so the step relation is quantifier-free and the effect is a total function. <details><summary>Full description</summary><p><b>What disappears.</b> The baseline's <code>NodeStep</code> is <code>∃ res, Pr.step … res ∧ c' = …</code>. Here the label supplies the reaction, so <code>ActionSpec.Apply</code> is a <i>function</i>, <code>Step</code> is three conjuncts with no quantifier, and <code>feasible</code> is unnecessary — a total function cannot fail to produce a successor. All that survives of that obligation is <code>permits_total</code>, one lemma about the protocol instead of six about actions.</p><p><b>Why fairness still works.</b> Carrying a reaction in the label would normally wreck weak fairness: <code>x.lbl j = a</code> would name a <i>reaction</i>, so "eventually taken" would force a validator to make every choice its protocol permits. It survives because the payload sits <i>over</i> the action — <code>(x.lbl i).action = a</code> still says "this action occurred, whatever the validator did", with the payload projected away by <code>Sigma.fst</code> rather than existentially quantified. The whole fairness layer carries over from the baseline with one projection inserted.</p><p><b>What it cost to find.</b> Three rewrites. The first two invented a separate reaction-free label type and an erasure map into it, and rediscovered painfully that the baseline's <code>Action</code> already <i>is</i> the reaction-free alphabet, so the erasure is just <code>Sigma.fst</code> and there is nothing to invent.</p></details> | one design choice changed |
| `StsConditionSplit` | A framework that states each action's enabling condition once and has the step <i>cite</i> it, keeping three spellings of the step side by side with theorems proving they agree. <details><summary>Full description</summary><p><b>The three spellings.</b> <code>Step</code>'s constructors appeal to <code>(spec Pr S a).Enabled</code> and <code>.Permits</code>; <code>StepGuard</code>'s cite the separate <code>guard</code> function; <code>StepInline</code> spells the conditions out. <code>step_iff_guard</code>, <code>stepGuard_iff_inline</code> and <code>enabled_iff</code> prove all three agree. Having them adjacent and provably equal is the point of the flavour.</p><p><b>The measured result.</b> In the miniature experiment this looked cheap: the same 9 proof tactics as the inductive presentation, for 15 extra statement lines. At six real actions the correspondence lemma alone was 30 lines and every condition was written twice, so adding an action edited three places. Rewriting the constructors to <i>cite</i> <code>guard</code> removed that duplication — conditions live in one place, adding an action edits two, and <code>enabled_iff_guard</code>'s forward direction collapses to <code>cases h &lt;;&gt; assumption</code>. Final standing: 70 statement lines / 2 edit sites / ~9 tactics, against the baseline's 48 / 1 / ~20.</p><p><b>Two caveats when reading it.</b> It carries <b>no proofs</b> — deliberately, since its structure was still moving while it was being compared — and two of its helpers keep their own names because their semantics differ from the recommended flavour's same-role helpers: <code>Config.update</code> takes a function where <code>Config.setNode</code> takes a record, and <code>bumped</code> advances a clock by one where <code>setClock</code> assigns it.</p></details> | one design choice changed |
| `StsRelationalSetLog` | The original framework, and the baseline the other four each vary by one choice: a <code>Set</code> message log, and a step relation that declares its enabling condition and quantifies over the reaction. <details><summary>Full description</summary><p><b>How a step is written.</b> Each action's specification is an <code>ActionSpec</code> record with a declared <code>Enabled</code> condition, a <i>relational</i> <code>Effect</code>, and <code>feasible</code> — the obligation that an enabled action has at least one successor. <code>NodeStep</code> says what a reaction does existentially: <code>∃ res, Pr.step … res ∧ c' = applyNodeStepResult …</code>.</p><p><b>What the shape buys.</b> Enabling conditions are syntactic: <code>Enabled</code> is a field you can read, not something to be recovered from the step relation, so <code>Execution.Enabled</code> in the fairness layer means what it says. <code>Step.elim</code> gives case analysis one <code>intro</code> per case.</p><p><b>What it costs.</b> <code>feasible</code> is real work for the protocol author — six obligations, one per action — and the existential in <code>NodeStep</code> shows up in every proof that has to say what a validator did.</p></details> | the original, kept for comparison |

**Which one to pick.** `StsMultisetLog` unless you have a reason to want otherwise. It is the
most general of the five and the most developed — it carries the full set of proofs, and it is
where new work goes, so its API is the one treated as fixed.

The other four each change exactly one design decision, and they are kept because that
comparison is the evidence for the choice: the A/C/M measurements ended in a tie on proof
effort, and M was picked on other grounds, all recorded in [CONTEXT.md](CONTEXT.md). So they
answer "why not that design instead?", and reaching for one is reasonable if you want the design
it isolates. None of them is abandoned code — every flavour keeps its own `make` target and its
`sorry`/`admit` check, and all five compile.

## How they differ, in detail

One block per flavour, quoted from the source. `StsRelationalSetLog` is the baseline; read the
other four against it. Three liberties are taken for width: explicit binders are elided with
`…`, implicit ones are shown without their types (`{c}` for `{c : Config Node Msg NodeState}`),
and `| …` stands for constructors of the same kind as the one above. Nothing else is paraphrased —
every other line is as it is in the file.

### `StsRelationalSetLog` — the baseline

A step is a declared condition and a relational effect. For a reacting action that effect
is `NodeStep`, and it quantifies over what the validator did.
Source: [`Protocol.lean:299`](StsRelationalSetLog/Protocol.lean#L299), [`:197`](StsRelationalSetLog/Protocol.lean#L197).

```lean
def Step … (a : Action Node Msg Ev) (c c' : Config Node Msg NodeState) : Prop :=
  (spec Pr S a).Enabled c ∧ (spec Pr S a).Effect c c'

def NodeStep … (p : Node) (e : Event Node Msg Ev) (pre c' : Config …) : Prop :=
  ∃ res, Pr.step p pre[p].clock pre[p].view pre[p].st e res ∧
    c' = applyNodeStepResult p res pre
```

### `StsMultisetLog` — the suggested one

`Step` is the baseline's, verbatim. The change is one level down: because the log is a
`Multiset`, `extract` recovers the reaction from `(pre, c')`, so nothing is quantified.
These read shorter than the others because the binders come from section `variable`s.
Source: [`Spec/Protocol.lean:396`](StsMultisetLog/Spec/Protocol.lean#L396), [`:299`](StsMultisetLog/Spec/Protocol.lean#L299).

```lean
def Step : Prop :=
  (spec Pr S a).Enabled c ∧ (spec Pr S a).Effect c c'

def NodeStep : Prop :=
  Pr.step p pre[p].clock pre[p].view pre[p].st e (extract p pre c') ∧
    c' = applyNodeStepResult p (extract p pre c') pre
```

### `StsStepInductive` — presentation A

One constructor per action, each carrying its own enabling condition, and enabledness
derived from the relation rather than declared beside it.
Source: [`Protocol.lean:230`](StsStepInductive/Protocol.lean#L230), [`:284`](StsStepInductive/Protocol.lean#L284).

```lean
inductive Step (Pr : Protocol …) (S : Schedule Node) :
    Action … → Config … → Config … → Prop where
  | advance {c} (t : Time) :
      Step Pr S (.advance t) c { c with time := t }
  | tick {c} {p} {t} (res : NodeStepResult NodeState Msg) :
      p ∈ S.awake (c.time : Int) →
      Pr.step p (setClock p t c)[p].clock … .tick res →
      Step Pr S (.tick p t) c (applyNodeStepResult p res (setClock p t c))
  | …

def Enabled … (a : Action Node Msg Ev) (c : Config …) : Prop :=
  ∃ c', Step Pr S a c c'
```

### `StsReactionInLabel` — presentation C

The label carries the reaction as a payload over the action, so the effect is a total
function and the step relation has no quantifier at all.
Source: [`Protocol.lean:220`](StsReactionInLabel/Protocol.lean#L220), [`:233`](StsReactionInLabel/Protocol.lean#L233), [`:317`](StsReactionInLabel/Protocol.lean#L317).

```lean
def Reaction (NodeState Msg : Type) : Action Node Msg Ev → Type
  | .advance _ => Unit
  | .tick _ _ => NodeStepResult NodeState Msg
  | …

abbrev Move (Node Msg NodeState Ev : Type) :=
  (a : Action Node Msg Ev) × Reaction NodeState Msg a

def Step … (l : Move Node Msg NodeState Ev) (c c' : Config …) : Prop :=
  (spec Pr S l.action).Enabled c ∧ (spec Pr S l.action).Permits l.2 c ∧
    c' = (spec Pr S l.action).Apply l.2 c
```

### `StsConditionSplit` — presentation D

Conditions live in one place and the constructors cite them. Three spellings are kept
adjacent, with `step_iff_guard`, `stepGuard_iff_inline` and `enabled_iff` proving they
agree. Its two own helpers stay its own: `Config.update` takes a function where
`StsMultisetLog`'s `setNode` takes a record, and `bumped` advances a clock by one where `setClock`
assigns it.
Source: [`Protocol.lean:279`](StsConditionSplit/Protocol.lean#L279), [`:321`](StsConditionSplit/Protocol.lean#L321), [`:331`](StsConditionSplit/Protocol.lean#L331), [`:383`](StsConditionSplit/Protocol.lean#L383).

```lean
inductive Step (Pr : Protocol Node Msg NodeState Ev) (S : Schedule Node) : … where
  | tick {c} {p : Node} (eff : NodeStepResult NodeState Msg) :
      (spec Pr S (.tick p)).Enabled c → (spec Pr S (.tick p)).Permits c eff →
      Step Pr S (.tick p) c ((spec Pr S (.tick p)).Apply eff c)
  | …

def guard (Pr : Protocol Node Msg NodeState Ev) (S : Schedule Node) :
    Action Node Msg Ev → Config Node Msg NodeState → Prop
  | .advance, _ => True
  | .tick p, c => p ∈ S.awake (c.time : Int) ∧ c[p].clock < c.time
  | …

inductive StepGuard … where   -- conditions cited from `guard`, effects inline
inductive StepInline … where  -- both inlined
```

What follows from those spellings, and does not show in them: `StsStepInductive` and
`StsReactionInLabel` have no `feasible` obligation — a constructor is its own witness in the
first, a total `Apply` cannot fail in the second, which leaves `permits_total`, one lemma about
the protocol instead of six about actions. `StsRelationalSetLog`, `StsConditionSplit` and
`StsMultisetLog` each keep `feasible`. And `StsMultisetLog` pays for its recovered reaction by
carrying two forms of the relation, `Step.elim` and `Step.elimR`, because the successor equation
mentions `c'` on both sides and `subst` cannot fire on it.

The rest of each flavour's shape, which is where the fifth difference — layout — lives:

| Flavour | Layout | Proofs it carries | Vocabulary | Size |
| --- | --- | --- | --- | --- |
| `StsRelationalSetLog` | flat, 9 files | `Reachable`, `Justified` | `Node`/`Time` | 1568 lines |
| `StsStepInductive` | flat, 8 files | `Reachable` | `Node`/`Time` | 1449 lines |
| `StsReactionInLabel` | flat, 8 files | `Reachable` | `Node`/`Time` | 1482 lines |
| `StsConditionSplit` | flat, 7 files | none — deliberately, the structure was still moving | `Node`/`Time` | 1340 lines |
| `StsMultisetLog` | `Spec/`, `Analysis/`, `Examples/`; 11 files | `Reachable`, `Justified`, `Lemmas`, `Execution`, all under `Analysis/` | `Node`/`Time` | 2025 lines |

All five express the same two models — Majorum (3SF) and TOB-SVD — in their `Models` file, and
all five carry the same two worked examples (`Example`, `CustomEvents`). That is what makes the
comparison controlled: only what is shown above varies.

## Names

The flavours were renamed on 2026-08-10, from letters to what they do. The letters survive in
[CONTEXT.md](CONTEXT.md), where the measured comparison of step presentations calls them A, B,
C and D, so the mapping is worth keeping to hand:

| Now | Was | In the comparison |
| --- | --- | --- |
| `StsMultisetLog` | `Sts2MX`, briefly `StsMultisetLogLayered` | — (a fork of M) |
| `StsStepInductive` | `Sts2A` | A |
| `StsReactionInLabel` | `Sts2C` | C |
| `StsConditionSplit` | `Sts2D` | D |
| `StsRelationalSetLog` | `Sts2Orig` (upstream `Sts2`) | B |

`Sts2M` — the flat multiset-log flavour, "the fourth option" in that comparison — was **removed**
on 2026-08-10, and the fork that superseded it took its name. So `StsMultisetLog` today is the
layered flavour, not the one the older entries in [CONTEXT.md](CONTEXT.md) call `Sts2M`.

Namespaces moved with the directories, so they are `Framework.StsMultisetLog` and so on. No
alias or deprecated re-export was left behind: the old names are gone, and anything written
against them has to be updated.

## Using it

Module roots are the flavour names, so imports read `import StsMultisetLog` or
`import StsMultisetLog.Spec.Protocol`. Namespaces are `Framework.<Flavour>`, so
`open Framework.StsMultisetLog` is how you bring the vocabulary into scope.

    make                 # list targets
    make cache           # fetch prebuilt Mathlib artifacts
    make StsMultisetLog          # sorry/admit check + build of one flavour

**The two pins move together.** `lean-toolchain` is `leanprover/lean4:v4.32.2` and
`lakefile.toml` requires Mathlib `v4.32.2`; they have to agree, and bumping one means bumping the
other. Note how Lake behaves if this package is *required* somewhere: it joins that build graph,
which resolves a single rev per dependency name and uses a single toolchain, so whatever
requires it must be pinned to the same two versions.

## Provenance

This repository was created on 2026-08-10, when the framework was split out into a package of
its own, carrying its history with it: 51 commits, from "Promote the framework to a top-level
Framework/ directory" onwards — `git log` has them. Paths were
flattened in the same pass (`Framework/Sts2MX/…` → `Sts2MX/…`, since renamed again as above),
so entries in `CONTEXT.md` written before that date name both the old paths and the old
flavour names.
