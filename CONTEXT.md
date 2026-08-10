# Framework — context log

Durable notes for this repository: six flavours of a protocol-independent framework for
message-passing distributed protocols, each isolating one design choice.

Extracted on 2026-08-10 from the repository this framework grew up in, whose root `CONTEXT.md`
these entries came from — the framework's history travelled with them (51 commits, `git log` from
"Promote the framework to a top-level Framework/ directory" on). Entries below predate the
extraction, so they say `Framework/Sts2M/` where the path is now flat, and they use the
flavours' **old names** throughout.

## How to read the old names

The flavours were renamed on 2026-08-10 (see the entry at the end). Every entry below was
written before that and is left exactly as it was — rewriting the record would falsify it — so
read it through this table:

| Written as | Now | In the four-presentation comparison |
| --- | --- | --- |
| `Sts2`, `Sts2Orig` | `StsRelationalSetLog` | B, the baseline |
| `Sts2A` | `StsStepInductive` | A |
| `Sts2C` | `StsReactionInLabel` | C |
| `Sts2D` | `StsConditionSplit` | D |
| `Sts2M` | **removed** 2026-08-10 | the fourth option |
| `Sts2MX` | `StsMultisetLog` | — (a fork of M) |

Mind the reuse of the name: `StsMultisetLog` today is `Sts2MX`, the fork. The flavour these
entries call `Sts2M` no longer exists — see the last entry in this file — so an entry describing
`Sts2M`'s files or layout describes something that is gone, while an entry describing its *step
layer* still describes what `StsMultisetLog` does, since the fork inherited it verbatim.

Namespaces followed the directories, so `Framework.Sts2M` is now
`Framework.StsMultisetLog`, and `Framework.Sts2` — `Sts2Orig`'s namespace, which never took
the `Orig` suffix — is now `Framework.StsRelationalSetLog`. Identifiers that merely *end* in an
old flavour name are consumer model names, not flavours, and are **not** part of this mapping.

What to write here and when is in [CLAUDE.md](CLAUDE.md).

## Lean/Mathlib gotchas

Copied with the extraction because they are about Lean rather than about any one repository; the
repository this was extracted from keeps its own copy.

- **`abbrev View := Nat` hides arithmetic from `omega`.** Measured on Lean
  4.32.2: `example (v w : View) (h : v < w) : v + 1 ≤ w := by omega` fails with
  "no usable constraints found" — being reducible is not enough. Use
  `scoped notation "View" => Nat`, which expands at parse time. A sibling
  formalization hit the same thing on 4.29.1, so this is not toolchain-specific.
  A protocol model's types file keeps that `example` as a regression check.
- `Set.not_mem_empty` does not exist in Mathlib v4.32.2 (the `not_mem` →
  `notMem` renaming). Prefer `simp` over naming such lemmas.
- **A named `Prop` helper loses decidability unless it is reducible.** `def P … : Prop := a ∧
  b` makes every `Decidable (P …)` goal fail, even when each conjunct is decidable, because
  instance search does not unfold a plain `def`. Use `abbrev` or `@[reducible] def`. The error
  names the *instance*, not the definition, which sent one diagnosis badly astray
  (2026-08-03): it was read as "the model must use a `Bool` condition" when the fix was one
  keyword in the proof file.
- **`simp only [defName] at h` can poison a hypothesis's type arguments.** Reducing
  `(protocol C Q).step …` with `simp only [protocol] at hres` also unfolds `protocol C Q`
  inside the *implicit type arguments* of every term in `hres` (the `Exec`/`GetElem`
  instances mention `Pr`); a later `subst` splices those into the goal, which is then defeq
  to the clean spelling but never again syntactically matches it — `rw` fails with a
  pattern that is visibly present. Fix: per-case definitional `Iff.rfl` lemmas
  (`protocol_step_tick`/`_recv`/`_wake`) and `rw` with those, which rewrite exactly the
  proposition (2026-08-03, found in `Lemma2.lean`).
- **Scripted span replacement silently eats adjacent declarations.** Replacing everything
  between two anchors deleted `ThmDynamicAvailabilityGA` unnoticed on 2026-08-02, because the
  span reached further than intended and the file still compiled. Distinct from the earlier
  hazard of a `str.replace` that silently *matches nothing*: this one silently matches too
  much. Count declarations before and after, or anchor on the end of the intended span.

## The framework attempts

#### Framework.Sts2 — the generic framework (2026-08-01)

Lives at `Framework/Sts2/`, namespace `Framework.Sts2`. It began inside
a protocol's own framework subdirectory under an instruction to keep the work inside `Sts2`,
was promoted to the top level once settled — it belongs to no single protocol —
and then placed in a per-attempt subdirectory, so a future framework attempt sits
beside it rather than replacing it.

**Requirement, in the user's words**: the framework must *allow expressing* the
network and adversarial model of **Majorum** (a.k.a. 3SF) and *allow expressing*
sleepiness as in **TOB-SVD**. Not "Majorum's model with TOB-SVD's sleep bolted
on" — both must be instances of one parameterisation.

Sources, both available locally (no need to fetch):

- Majorum = 3SF. The paper's own source, §Model and §Adversary.
  The paper's macro file defines `\protocol` as `Majorum`, and the citing paper's source
  cites it as `damato2026majorum` — **the protocol was renamed; same paper**.
  Older versions of the paper live beside it.
- TOB-SVD: the paper's PDF, and
  arXiv:2310.11331 §3.1/§3.3. D'Amato, Saltini, Tran, Zanolini, ICDCS 2025.

**What the two models disagree about** — this is what forced the parameterisation:

| | Majorum | TOB-SVD |
| --- | --- | --- |
| network | partial synchrony, GST then Δ | synchronous, Δ throughout (`GST = 0`) |
| interval awakeness | `H_{r,r'} = ⋃ H_i`, awake *at some point* | `H_{t₁,t₂} = ⋂ H_t`, awake *throughout* |
| joining | awake ≠ active; joining protocol delays sending | awake = active |
| compliance | `\|H_{voting(t−1)} \ A_{voting(t)}\| > \|A_{voting(t)}\|` | `\|B_{t+Tb}\| < ρ·\|H_{t−Ts,t} ∪ B_{t+Tb}\|` |
| below zero | `H_i := ∅` for `i < 0` | `H_t := V`, `B_t := ∅` for `t < 0` |
| extras | GAT, slots of `4Δ`, gossip window on proposals | `Tb` backward-simulation window, `Ts` stabilization |

Design consequences, each driven by a specific requirement:

- **Schedules are indexed by `Int`, not `Round`.** Both papers query negative
  times with *different* conventions, so the convention belongs to the schedule
  the model supplies, not to the framework.
- **Both interval operators are provided** (`awakeSomewhere`, `awakeThroughout`)
  and neither is privileged. `awakeThroughout` uses `Finset.inf`, which needs
  `[Fintype V]` for its `⊤ = univ`; that is why validators are a `Fintype`.
- **The schedule is `adv` + `awake`, and nothing else.** Three earlier designs all
  tried to put "who may act" into the model and all were wrong, for the same
  reason: **joining is behaviour of honest validators running Majorum**, so it is
  protocol code, not adversary structure. The attempts were (1) `Participation`,
  computing `active` from `awake` — needed to invert `voting`, i.e. division by the
  variable `4Δ`; (2) an `active` field constrained by a `Joining` predicate — put
  protocol code in the model; (3) a `Protocol.participating` field or a `joined`
  parameter — made the framework know a protocol-specific concept, or made a
  model-level assumption depend on an unchecked parameter.
- **Resolution**: the framework reports *waking* (`Event.wake`, fired on an
  asleep→awake transition) and nothing more. A protocol that must delay
  participating implements that itself and returns `send := ∅` meanwhile; `react`
  does not filter sends. `Synchrony`/`Relay` owe delivery to the **awake**, so a
  joining validator still receives its backlog.
- **Majorum's Constraint (1) is still expressible over the schedule alone**, because
  its joining rule is *deterministic in the wake schedule*: active at `voting(t−1)`
  ⟺ awake continuously since `voting(t−2)+Δ`. So `Compliant` uses
  `awakeThroughout` and needs no protocol handle. The residual obligation is a
  *correspondence*: whatever Majorum protocol we write must actually stay silent
  that long, or the assumption and the protocol disagree. That is a lemma about the
  protocol, to be discharged where the protocol lives.
- `Compliant` requires `2 ≤ t` (so `t - 2` is genuine subtraction, not `Nat`
  truncation) and by `gst ≤ proposing t` — "every slot after GST" means the slot
  *starts* after GST, which the earlier `voting t` condition got wrong in the
  liveness-favouring direction.
- **There is no framework `Active` predicate.** `Live` therefore quantifies over
  *awake* validators, which is stronger than the paper's "active in round `r`"; a
  protocol whose joining delay matters will want to weaken it with its own
  participation predicate.
- **Sleep needs no dedicated machinery.** `Synchrony` quantifies only over
  *active* validators, so a sleeping validator incurs no delivery obligation and,
  the moment it becomes active, already owes everything sent Δ ago — which *is*
  TOB-SVD's "upon waking, validators immediately receive all messages they should
  have received while asleep" and Majorum's queue-until-wake. An earlier design
  with in-flight message sets and deadline-conditioned ticks was dropped as
  unnecessary.
- **The event interface went through three iterations** (2026-08-01), worth
  recording so it is not re-litigated:
  1. `Event = start | recv | timeout` with an `EventEnabled` predicate. Rejected:
     it fixed the event vocabulary, hardcoded reliable broadcast, and let `start`
     fire repeatedly.
  2. No events at all — `step : V → Round → View → State → Effect`, reading only
     the accumulated view. Rejected because per-arrival reactions and arrival
     order became inexpressible (TOB-SVD §3.3 handles messages as they arrive,
     and its "accept up to two LOG messages per validator" is order-sensitive).
  3. **Current**: `Event = tick | recv m | custom ev`, where the framework
     generates exactly the two events it knows about and `Ev` is the protocol's
     own type, gated by `Protocol.enabled`. Timers are `custom` events enabled by
     a condition on the round.
  Note `recv m` carries the message *and* the view already contains it when
  `step` runs, so a protocol may work from either.
- **`Step.deliver` requires the recipient to be active.** Delivery to a sleeping
  validator is simply not a transition, which is how queueing is modelled: the
  message stays in `sent` until the validator wakes.
- **`clock` and `tick` were merged** (they were redundant: two transitions that
  nothing kept in correspondence, so a validator could be ticked twice in a round
  or never). `Step.clock` now advances the round *and* runs each active
  validator's `.tick` reaction, reading the old configuration so the round is
  simultaneous. Consequences: exactly one tick per active validator per round
  holds by construction, a `tick` reaction need not be idempotent, and the
  `Diligent` fairness predicate was **deleted** — `TimeDiverges` is the only
  progress assumption left.
- **Sleep/wake and corruption are not transitions.** They are the adversary's
  fixed choices over an execution, so they live in the `Schedule` parameter. The
  step relation has only `act`, `deliver`, `tick`, `adversarial`.
- **The step relation now says *nothing* about how time progresses** (2026-08-02). This
  replaces the earlier design, and it fixed two real defects in it:
  - `advance` incremented time by one and `tick` incremented a node's clock by one, so a
    node that slept through rounds 3–7 had to tick five times to catch up, **re-reacting at
    each stale round** — replaying history, where both papers have a waking validator rejoin
    at the current time.
  - Worse, `Synchronized` (`awake → clock = time`) was then **unsatisfiable together with
    sleep**: at the index where a node wakes, its clock is still the pre-sleep value and no
    catch-up tick has run yet. Since both `Model` bundles assumed it, they admitted only
    executions in which no node ever slept through a time advance — the sleepy model was
    silently neutralised, and any liveness result would really have been about static
    participation.
  - Fix: actions carry the target time — `advance t` sets time to `t`, `tick p t` sets `p`'s
    clock to `t` — with **no** relation between them in the spec. One tick now brings a node
    fully up to date.
  - Everything one might want to believe about time became an opt-in assumption in
    `Execution.lean`: `TimeMonotone`, `ClocksMonotone`, `ClocksSound` (no reading the
    future), `Synchronized`, `TimeDiverges`, and `Diligent` (every awake node is ticked at
    every value of time — the property that makes a node act at each round, which the old
    design hid inside `tick`).
  - Casualty: `clock_mono` was a *theorem* and is now the assumption `ClocksMonotone`. That
    is the point — the old version made a scheduling decision look like a fact.
- **Time is deliberately weak, so a property assumes only the discipline it needs**
  (2026-08-01). Two separations, made after noting that accountable safety should
  hold with no reference to the clock at all, and other properties assuming only
  monotone clocks:
  - `Step.advance` (real time moves, nobody acts) is separate from `Step.tick p`
    (one validator reacts). Previously advancing the round *was* ticking every awake
    validator, so a message-only proof still had to handle sends from the clock step,
    and "time passes while nobody acts" — which asynchrony needs — was inexpressible.
  - `Config.time` is real time, read only by the environment (schedule, Δ, GST);
    `Config.clock p` is what each validator believes, and *that* is the round handed
    to `Protocol.step`. So synchronized clocks became the assumption
    `Execution.Synchronized` (both papers assume it) rather than a fact of the model,
    and monotonicity is free because `tick` only increments.
  - `Step.tick`'s condition `clock p < time` keeps a clock from running ahead and
    preserves one tick per validator per round, so tick reactions still need not be
    idempotent.
  - Costs: rounds are no longer simultaneous (tick reactions interleave, so a
    validator may see another's message from the same round — strictly more general);
    and a validator asleep for several rounds wakes with a stale clock it can only
    advance one tick at a time, which is why `Synchronized` is restricted to awake
    validators. A model wanting waking validators to know the time immediately needs
    a `tick` that jumps rather than increments.
  - The three resulting property classes are documented in `Execution.lean`:
    timeless (accountable safety), monotone-clock (free), synchronized (liveness).
- **Executions record step labels again, and fairness is stated on them**
  (2026-08-01). Labels were dropped when advancing the round *was* ticking every
  awake validator, because ticking was then structural; splitting `advance` from
  `tick` made fairness necessary, and fairness is about which transitions occur.
  `WeakFair` is the textbook shape (continuously enabled ⇒ eventually taken), with
  `TickFair`, `AdvanceFair`, `DeliverFair`, `CustomFair` as instances; `TickFair` and
  `AdvanceFair` are in both `Model` bundles, the other two are à la carte.
  The label-free alternative — defining occurrence as
  `Sys.Step a x[i] x[i+1]` — was rejected: it says an action *explains* the
  transition, not that it was taken, so two actions with the same effect are
  indistinguishable (a no-op `tick` and a no-op `custom`) and nothing can be
  counted. Counting is what a bound like "at most `k` adversarial steps" needs.
- **`Step` is `ActionSpec`-based, not an inductive** (2026-08-01). Each action has one
  record holding `Enabled`, `Effect` **and** `feasible`, and `Step Pr S a c c' :=
  (spec Pr S a).Enabled c ∧ (spec Pr S a).Effect c c'`. Motivation: `WeakFair` used to
  take the enabling condition as a *separate parameter*, with nothing tying it to the
  action — a wrong one silently made the assumption either vacuous or unsatisfiable,
  and an unsatisfiable assumption makes every theorem under it vacuously true.
  `Execution.Enabled` now reads the condition off the action's own spec.
  - Grouping per action (rather than two top-level functions each matching on
    `Action`) means the two halves cannot be mismatched and an added action cannot be
    missing one.
  - `Effect` is a **relation**, so nondeterministic actions stay expressible even
    though all six current ones are deterministic — every choice is carried in the
    action itself (`deliver p m`, `custom p ev`).
  - `feasible : ∀ c, Enabled c → ∃ c', Effect c c'` is **Event-B's FIS obligation**,
    the price of syntactic enabling conditions; TLA+ instead *defines* `ENABLED A` as
    "some successor satisfies `A`" and so never needs it, at the cost of enabledness
    never being explicit. All six discharge it with `fun _ _ => ⟨_, rfl⟩` because
    their effects are equations; a genuinely nondeterministic effect would make it
    real work, which is the point.
  - Bonus: determinism of the six is now immediate, so a `honest_step_unique`-style
    lemma is free if wanted.
- **Naming pass over `Sts2`** (2026-08-02), in the order the confusions surfaced:
  `V` → `Node` (the validator type), `Effect` → `NodeStepResult` (it was colliding with
  `ActionSpec.Effect`, an action's effect on the *configuration*), and `Round` → `Time`.
  Note what the last one does *not* fix: `Config.time` (true) and `Local.clock` (a node's
  belief) are both `Time`, so nothing at the type level stops one being passed where the
  other belongs. The discipline is that only the environment reads `Config.time`, and only
  `Local.clock` is ever handed to `Protocol.step` — recorded in `Message.lean`'s docstring.
- **`State` renamed to `NodeState`** (2026-08-02) — it is one validator's protocol
  state, not the transition system's. `System`'s own parameter, which *is* the system's
  state space, is now `Carrier`, so the two no longer share a name in one file.
- **The reachability case, finally tested** (2026-08-02). `Framework/Sts2/Reachable.lean`
  adds `Reachable` and proves `viewsSound` — "everything in a validator's view was signed
  and sent" — through `Step.elim`: 31 lines, 27 tactic invocations, six action cases, no
  strengthening needed. Findings:
  - **It works, and the eliminator holds up.** The one idiom it needs that `cases` on an
    inductive would not: the induction hypothesis reaches the cases by making the motive
    an *implication*, `fun _ d d' => ViewsSound d → ViewsSound d'`, and applying the
    eliminator's result to `ih`.
  - **The real cost was not the presentation.** It was needing a small API of
    field lemmas — what `applyNodeStepResult`, `receive` and `setClock` do to `clock`, `view` and
    `sent` — which any presentation would have required. Nine such lemmas now live in
    `Protocol.lean`, and with them each action case is two or three lines.
  - **`Execution.ViewsSound` is deleted as an assumption**: with `Execution.reachable`
    (every configuration in an execution is reachable, by induction on the index) it is a
    *theorem*, `views_sound`. Both `Model` bundles lost a conjunct — a real strengthening
    of both models, and the concrete payoff of doing the exercise.
  - Watch the `[…]` vs `.nodes` split: a case that receives
    `hm : m ∈ (applyNodeStepResult …)[p].view` needs `simp at hm` before the hypothesis
    will apply — so cases are tactic blocks, not one-line terms. (Which side the lemmas
    are phrased over flipped later; see the bracket-normal-form entry below.)
- **`Step.elim` closes the presentation question** (2026-08-02). `Sts2`'s `Step` is a
  `def` (a conjunction), so `cases` cannot split it per action and every proof paid
  `obtain ⟨-, res, -, h⟩; subst h` per case — the whole measured ~2× against the
  inductive forms. `Step.elim` is a hand-written eliminator that does this **once**: each
  case receives the action's enabling condition, the permitted effect, and a goal whose
  successor is already concrete. Two sample invariants (`sent_mono`, `clock_mono`) are
  proved through it and read one line per action, matching the inductive's ergonomics
  with no second relation and nothing that can drift.
  Wrinkles found while writing it, all recorded in the source:
  - **The motive must be given explicitly** (`h.elim (motive := fun _ d d' => …)`);
    higher-order unification will not guess it. That is the one ergonomic loss against
    `cases` on a genuine inductive.
  - **`abbrev Round := Nat` hid arithmetic from `omega`** — the *same* trap already
    recorded for `View`. `Round` is now `scoped notation`, in both `Sts2` and `Sts2D`.
  - Simp-lemma **shadowing** decides how the field lemmas must be phrased: whichever
    lemma normalises `c[p]`/`c.nodes p` fires first, and helper lemmas phrased on the
    other side then never match. Originally `getElem_nodes` (`c[p] = c.nodes p`) was the
    `simp` lemma, forcing `.nodes`; the orientation was reversed on 2026-08-02 — see
    below.
- **Measured comparison of four `Step` presentations** (2026-08-01), on a shared
  miniature model — same data types, same two lemmas (`sent` monotone, clocks
  monotone), only the presentation varying. Tactic counts for the two proofs
  together:
  | presentation | statement lines | proof tactics |
  | --- | --- | --- |
  | A: inductive `Step`, `Enabled := ∃ c'` | 18 | 9 |
  | B: condition + relational effect (current) | 39 | 20 |
  | D: A plus `guard` and a proved `Enabled ↔ guard` | 18 + 15 | 9 |
  C (effect carried in the label) was estimated at ≈14 tactics with a wrecked fairness
  spelling; it was **built in full on 2026-08-02**, see below.
  **Then repeated on the real six actions**, where the picture changes: `Sts2` (B) is
  48 statement lines and edits in **one** place per new action; `Sts2D` (D) is 65 and
  edits in **three** (constructor, `guard`, correspondence proof), because each
  enabling condition is written twice. The miniature's "D costs 15 lines" was
  misleading — with six actions the correspondence lemma alone is 30 lines.
  Both lived in the repo as parallel attempts for a while; **`Framework/Sts2D/` was
  untracked on 2026-08-02** (removed from git, left on disk and gitignored) once
  `Step.elim` gave `Sts2` the same case-analysis ergonomics. Keeping it tracked would
  have meant ~900 lines drifting as `Sts2` evolves, for a comparison already recorded
  here. It is still built by `lake build Framework` if the files are present locally.
  **`Sts2D` was then improved**: its constructors *cite* `guard` instead of inlining
  the conditions, so the duplication that was D's main cost is gone — conditions live
  in one place, adding an action edits two (`guard` + constructor), and
  `enabled_iff_guard`'s forward direction collapses to `cases h <;> assumption`. That
  makes the live comparison `Sts2` 48 lines / 1 edit site / ~20 tactics versus `Sts2D`
  70 lines / 2 edit sites / ~9 tactics.
  **Option A was then built in full, as `Framework/Sts2A/`** (2026-08-02), on the user's
  request: a copy of `Sts2` with only the step layer swapped — `inductive Step` with the
  enabling conditions inline, `Enabled Pr S a c := ∃ c', Step Pr S a c c'`. Result: **a
  wash.** 531 code lines against `Sts2`'s 533; the step layer is 72 lines against 84; the
  two shared proofs (`sent_mono`, `viewsSound`) are the same length, `viewsSound` marginally
  *longer* under `cases` because the constructor patterns spread over more lines than
  `Step.elim`'s single `intro`.
  The reason the miniature's "A costs 18 lines, B costs 39" did not survive scale: A needs
  the enabling conditions **syntactically** after all, because a model has to check a
  fairness assumption against a schedule, and `∃ c', Step …` cannot be checked. So A grows
  six `enabled_*` iff lemmas — 41 code lines, against the 36 that B spends on `Step.elim`.
  The costs are near-identical and opposite: **B pays to recover case analysis, A pays to
  recover syntactic enabledness.** Neither presentation is cheaper; they differ in which
  obligation is discharged where. A's version is arguably safer in one respect — its
  `enabled_*` are `iff`s, so nothing can promise more than the relation delivers, whereas B
  needs `ActionSpec.feasible` to guarantee that — and B's is safer in another, in that its
  conditions are addressable by name without a proof step. `A`'s backward directions are
  exactly where `Protocol.total` earns its place.
  **Option C was then built, as `Framework/Sts2C/`** (2026-08-02) — three times, and the
  rewrites are the finding. Final form: **`Sts2` with the reaction carried in the label as a
  *payload over* the action**, `Reaction : Action → Type` (`Unit` for `advance` and
  `adversarial`) and `Move := (a : Action Node Msg Ev) × Reaction NodeState Msg a`.
  `ActionSpec` becomes indexed by the action with three fields — `Enabled` (schedule, verbatim
  from `Sts2`), `Permits` (which reactions the protocol allows), `Apply` (a *function*) — and
  two existentials vanish: `Reacts`'s `∃ res` from the step relation, and `feasible`, since a
  total `Apply` cannot fail to produce a successor. What is left of feasibility is
  `permits_total`, one lemma about the protocol that does not mention the schedule.
  **Sizes: C 536 code lines against B's 533 and A's 531, with `Execution.lean` identical at 69
  to B's.** The fairness layer carries over from `Sts2` with one projection inserted
  (`(x.lbl j).action = a` for `x.lbl j = a`).
  Why the rewrites, and what each taught:
  - **v1 put `res` inside the label's constructors** (`Action.tick p t res`) and stated
    fairness per label. Wrong: `x.lbl j = a` then names a *reaction*, so weak fairness forces a
    validator to eventually make every choice its protocol permits. Measured 493 lines and
    looked like the cheapest of the three — it was cheapest only because the fairness layer had
    not been written honestly yet.
  - **v2 indexed fairness by sets of labels**, `WeakFair (P : Action → Prop)`. Correct but it
    leaves the granularity choice open at every site, and widening a set is monotone in
    **neither** direction. Both counterexamples, worth keeping because the asymmetry is easy to
    get backwards: with `a` enabled at even steps and `b` at odd steps neither singleton
    assumption bites while `WF {a,b}` does, so `WF{a} ∧ WF{b}` does not give `WF{a,b}`; and
    with both enabled forever, taking only `b` satisfies `WF {a,b}` but not `WF{a}`. Concretely
    "`p` ticks to reading `r` if it can" is the useful assumption, and widening it to "to *some*
    reading" is satisfied by ticking to `0` forever, with nothing in the statement looking
    wrong.
  - **v2 then added a `Kind` type** — the label with the reaction erased — plus a hand-written
    `Action.kind`, which fixed the granularity hazard (kinds cannot be unioned) but not the
    existential: `∃ a, a.kind = k ∧ enabled a c` merely quantified it once instead of
    everywhere. Removing it needed `enabledKind`, the condition without the reaction conjunct —
    **which is `Sts2`'s `ActionSpec.Enabled` verbatim**, so the conditions were then written twice.
    Peak cost: 585 lines.
  - **The hand-written erasure is a liability.** Tested: a shifted map
    (`.tick p t _ ↦ .tick p (t+1)`) *is* caught, because `enabledKind_iff`'s forward direction
    must exhibit a label of every kind and nothing maps to `.tick p 0`. But that only forces
    surjectivity onto each kind, which is not the same as being the intended map, and it holds
    only because no two `Kind` constructors share a signature and `Nat` has no cheap total
    involution — luck of these six signatures. Hence the dependent pair, where the erasure is
    `Sigma.fst` and right by definition.
  - **v3 restarted from `Sts2`**, which dissolves the rest: `Sts2`'s `Action` *is* the
    reaction-free alphabet, so there is no `Kind` type to invent, no erasure to write, no
    second condition to duplicate, and no fairness layer to redesign. The two-alphabet structure
    that v2 discovered painfully is what `Sts2` already had.
  **A fourth option, `Framework/Sts2M/`** (2026-08-02, the user's suggestion): make
  `Config.sent` a **multiset** and the reaction becomes recoverable from `(pre, c')`, so
  `Reacts`'s existential goes with no change to the labels and none to the fairness layer.
  The mechanism is that `∪` is lossy — a reaction re-sending a message already in the log
  leaves no trace, so two reactions can share a successor and the witness genuinely is not a
  function of the two configurations. `+` is cancellative, so
  `extract p pre c' := ⟨c'[p].st, ((c'.sent - pre.sent).map SignedMsg.msg).toFinset⟩` inverts
  it; `extract_applyNodeStepResult` is the round trip and `reacts_iff_exists` proves the
  relation is `Sts2`'s. 567 code lines against 533, all of the difference in `Protocol.lean`.
  Two findings, both negative and both worth keeping:
  - **Removing the existential did not make case analysis cheaper.** The successor equation
    is now `c' = applyNodeStepResult p (extract p pre c') pre`, with `c'` on *both sides*, so
    `subst` cannot fire — the very thing the existential form allowed, since there `res` was a
    fresh binder. `Step.elim` has to convert back through `reacts_iff_exists`, and every
    downstream proof is byte-identical to `Sts2`'s. A quantifier-free definition is not
    automatically a more usable one.
  - **It is a model change, not a spelling change.** Multiplicity becomes observable state.
    Nothing currently stated can see it — every property is membership-based — but the model
    now distinguishes executions the protocol semantics does not, and `sent` becomes finite by
    typing. Set against that: when two reactions give the same successor they give the same
    *transition*, so the ambiguity the existential expressed was semantically invisible. This
    is the one option that fixes a proof-engineering problem by changing the model.
  - **`NodeStepResult.send` had to become a multiset too** (2026-08-02). Leaving it a `Finset`
    makes the types disagree: a log delta can hold a message twice, a reaction cannot produce
    that, so `applyNodeStepResult p · pre` is injective but **not onto** the `p`-signed
    extensions and `extract` must deduplicate. Consequences of the mismatch, found by trying to
    replace the successor equation with frame conditions: the six natural frame conditions
    (time, other nodes, `p`'s clock and view, log only grows, additions signed by `p`) are then
    *insufficient* — verified with a counterexample whose delta holds one message twice — and a
    seventh, `Nodup`, is needed. With both multisets the six suffice, `extract` loses its
    `toFinset`, the round-trip proof shortens, and `applyNodeStepResult_surjective` states that
    reactions and reachable successors correspond exactly. Cost: sending `m` twice in one step
    now differs from sending it once, which no validator can observe since views are `Finset`s.
  - **Frame conditions were considered and rejected** as a replacement for the successor
    equation `c' = applyNodeStepResult p (extract p pre c') pre`. Beyond the sufficiency gap
    above, the general objection is the frame problem: `applyNodeStepResult` leaves a field
    alone by *not mentioning it*, whereas a frame relation leaves it alone only if someone
    remembers a conjunct. `Config` and `Local` have both gained fields in this project, and
    each such change would silently widen a frame-based `Reacts`. Event-B generates frame
    conditions mechanically for exactly this reason. Measured how much the equation carries:
    dropping it leaves a relation that is **definitionally** invariant under changing
    `Config.time`, and blind to every other node's state.
    The frame conditions are instead stated **as theorems** — `Reacts.time`, `.other`,
    `.clock`, `.view`, `.sent_le`, `.sent_signed` — plus `reacts_of_frame` for the converse,
    so the characterisation is complete and checked rather than assumed, and a new `Config`
    field still cannot slip through. `reacts_of_frame` is the payoff of the multiset `send`:
    with a `Finset` there it would be false. Sts2M is now 630 code lines against 533.
  **`Sts2M` splits specification from proofs** (2026-08-02): `Protocol.lean` keeps the
  definitions (131 code lines) and the new `Lemmas.lean` takes everything proved about them
  (197) — field lemmas, `applyNodeStepResult_surjective`, both eliminators, `sent_mono`, the
  frame lemmas. The split **cannot be perfectly clean**, and the reason is worth knowing:
  `ActionSpec.feasible` is a proof obligation *inside a definition*, so `spec` needs
  `nodeStep_total`, which needs `nodeStep_iff_exists`, which needs
  `extract_applyNodeStepResult`. Those three stay in `Protocol.lean`, along with the two
  one-line `rfl` read-backs (`nodes_apply`, `Config.setNode_apply`) that their proofs use.
  An attempt without `feasible` — `Sts2A` derives enabledness, `Sts2C` makes `Apply` total —
  would split cleanly; that is a small point in favour of not carrying the obligation in the
  structure.
  **The discriminating experiment was then run** (2026-08-02): the same parameterised
  invariant — "everything a validator in `H` signed is justified by its current state", with
  the protocol owing `mono`, `sends` and `honest` — written against both `Sts2` and `Sts2M`.
  It is the schema this framework will eventually owe, and it is deeper than `viewsSound`:
  the induction hypothesis is used twice per action, once for a signer whose state just moved
  and once for a signer whose state did not. Statement, obligations and the two `setClock` /
  `receive` helpers came out **byte-identical**; only the proofs differ. Result, in code lines:
  | | `justified_reacts` | driver | file |
  | --- | --- | --- | --- |
  | `Sts2`, via `Step.elim` | 27 (21 tactics) | 24 | 82 |
  | `Sts2M`, via `Step.elimR` | 26 (19 tactics) | 24 | 81 |
  | `Sts2M`, via `Step.elim` + `reacts_iff_exists` | — | 30 | — |
  | `Sts2M`, hand-rolled `cases a` | — | 30 | — |
  **A tie.** The first measurement had `Sts2M`'s driver at 30 and blamed the attempt; that was
  an artifact of reusing `Sts2`'s eliminator, whose reacting cases bind a reaction and give a
  *concrete* successor — the existential shape — so every case converted. **`Step.elimR`**
  (added 2026-08-02) leaves the successor abstract and hands over the `Reacts` instead; four
  of its six cases are then a bare `exact`, it is 28 code lines against `Step.elim`'s 48, and
  the driver drops to 24. Correct comparison: 81 against 82, i.e. no difference.
  The projected benefit still did not materialise — the frame lemmas did not make the proof
  *shorter*, they made it possible to write without substituting. What did change, in both
  directions:
  - *`Sts2M` gains on the acting node's state.* `(extract p pre c').state` is **definitionally**
    `c'[p].st`, so the goal matches after `rw [hs]`; `Sts2` needs a `have hst` through
    `applyNodeStepResult_getElem`.
  - *`Sts2M` loses on the log.* Splitting "was this message already there?" is `rcases hm with
    hold | hnew` on a `Set` union, but on a multiset needs `count_pos` / `count_sub` /
    `count_eq_zero_of_notMem` — about seven lines against two, twice over.
  - *`Sts2M` carries two forms of `Reacts`, and every proof must pick the matching
    eliminator.* Computed (as defined) and existential (`reacts_iff_exists`); `Step.elimR`
    serves the first, `Step.elim` the second, and going through the wrong one costs a
    conversion per reacting case. Both are wanted: `sent_mono` needs `Step.elim`'s concrete
    successor, `justified` needs `elimR`'s abstract one. That is a real standing cost —
    two eliminators to maintain, and a choice at every proof — but it is a *maintenance* cost,
    not the line-count penalty first reported. `Sts2` has one form and one eliminator.
  **The proofs tie**, so the choice was not made on proof effort. `Sts2M` is the better
  *specification* — the only attempt that says what a step may not touch and proves that
  characterisation complete — and its costs are precisely: a model change (observable
  multiplicity), two eliminators to keep (`Step.elim` and `Step.elimR`, one per form of
  `Reacts`), and multiset membership splitting where a `Set` union gives `rcases` for free.
  My reading was that those costs buy nothing measured, so `Sts2` should stay the target.
  **The user chose `Sts2M` (2026-08-02) and it is now the development target.** The costs
  above are therefore accepted, not overlooked; the thing to watch is whether the frame lemmas
  start earning their place in proofs that reason about a successor they cannot name.
  Conclusion of the whole exercise: **all four land within ~6% on size — the first three
  within ~1% — and they differ in which obligation is discharged where.** B puts it at the definition site
  (`feasible`, once per action) and pays `Step.elim` for case analysis. A derives `Enabled`
  from the relation and pays six `iff` lemmas to get the conditions back syntactically. C makes
  the successor a function and pays a `Reaction` type plus dependent pattern matching. None is
  cheaper; the earlier claim that C was cheapest was an artifact of an unwritten fairness
  layer. On that basis `Sts2` looked like the one to keep, its obligations being the ones a
  compiler checks — **superseded**: the target is `Framework/Sts2M`, see the entry above.
  Not yet measured, and the thing that will dominate: bigger inductive-invariant proofs
  over reachability — `viewsSound` is one case-analysis deep and may be too small to
  separate them. The B overhead is also recoverable by
  *derived* per-action inversion lemmas, which would not duplicate the conditions the
  way D does.
  - B's factor of ~2 is mechanical: `Step` is `guard ∧ (c' = …)`, so every case opens
    `obtain ⟨-, res, -, h2⟩ := h; subst h2`, whereas `cases h` on an inductive
    destructures *and* substitutes the successor at once, and `res` is a constructor
    binder rather than an existential to open.
  - B's overhead is constant per case, so it scales as #actions × #lemmas; the fix
    would be per-action inversion lemmas, which is exactly what D does instead.
  - D's correspondence is **one** lemma with a case per action, not one per action —
    cheaper than first assumed. What D loses is the per-action grouping of `guard` with
    effect, since `guard` becomes its own match.
- **Honest behaviour may be nondeterministic** (2026-08-01). `Protocol.step` is a
  *relation* `… → Effect State Msg → Prop`, not a function, so a specification may
  leave choices open — which payload a leader proposes, which of several valid chains
  it follows. Adjacent pieces: `applyNodeStepResult` applies a `NodeStepResult`, `Reacts` is the
  existential over permitted effects, and `Protocol.total` ("some reaction is always
  available") is what `reacts_total` uses to discharge each action's `feasible`. It is
  the protocol-side counterpart of Event-B's FIS.
  Cost worth knowing: **the model stops being computable by default**, which is what
  the `decide` checks in the examples rely on. The mitigation, used in both examples,
  is for a deterministic protocol to define a `reaction` *function* and lift it with
  `step p t view s e res := res = reaction p t view s e`; `total` is then `⟨_, rfl⟩`
  and the `decide` checks run against the function.
- **Per-validator updates are field-specific setters, not one record-level update**
  (2026-08-02), arrived at in two steps. First `Config.update` (which took a function of
  the old record) became a value-taking setter — a function-shaped update can only yield
  lemmas mentioning an opaque `f (c.nodes q)`, whereas a value gives a usable unconditional
  read-back lemma. Then the record-level setter became a state-only one, so the name says
  what changes; `receive` and `setClock` write `view` and `clock`. Benefit: no caller can
  silently clobber a field it did not mean to touch, which a whole-record setter invites.
  The `if p = q` those three shared is now factored into **`Config.setNode c p r`** (write
  one validator's record, keep the rest), so each write is one line and the pattern is
  written once (2026-08-02). Still value-shaped, not `f c[p]`, for the reason above. Two
  consequences: `Config.setNode_apply` is the single lemma turning a write into an `if`, and
  the per-write read-back lemmas now name the new record at the **target** index
  (`{ d[q] with … }`, q being the written validator) rather than at the reader's — the old
  spelling was `rfl` only because the record was built inside the branch.
  The state-only setter (`Config.setNodeState`) is then **gone**: with `setNode` factored
  out it was a one-line wrapper used once, and `applyNodeStepResult` going through it made
  that the only write layered on another — an extra hop in every proof about it, and its
  read-back lemma had a different shape from `receive`'s and `setClock`'s. All three now
  read `c.setNode p { c[p] with <field> := … }` and all three read-back lemmas are the
  same `if`. This also disposes of `setNodeState_apply`, whose entire job had been to let
  `simp` see through that hop.
- **`c[p]` is the normal form for reading a validator's record** (2026-08-02), reversing
  the earlier orientation. `nodes_apply : c.nodes q = c[q]` is the `simp` lemma; the old
  `getElem_nodes` (which normalised the other way) is gone. Three rules follow, each
  learned by breaking the build:
  - **`simp` cannot reduce a bracket applied to a literal record** — that step needs
    `.nodes`, now the non-normal side. So every helper needs an explicit read-back lemma
    saying what `c[p]` is afterwards: `applyNodeStepResult_getElem`, `receive_getElem`,
    `setClock_getElem`.
  - **Those read-back lemmas must *not* be `@[simp]`.** As simp lemmas they fire first
    and expand a bracket into nested `if`s, after which the per-field lemmas
    (`applyNodeStepResult_view` and friends) no longer match — the same shadowing that
    forced `.nodes` originally, now in the opposite direction. Per-field lemmas are
    `simp`; read-back lemmas are cited by name.
  - **Statements must pick the same side as the goals they feed.** `Init` was phrased over
    `.nodes` and could not be rewritten into a bracketed goal: the two are defeq but not
    syntactically equal, so neither `rw` nor `simp` bridges them. `Init` is now bracketed.
  Also: `GetElem` index types need annotating (`∀ p : Node`, `∃ i : Nat`) or instance
  resolution fails with "Type of `x[i]` is not known" — hit in `Init` and in `TimeDiverges`.
- **`Effect` → `NodeStepResult`, `install` → `applyNodeStepResult`** (2026-08-02), with
  the binder `eff` → `res`, completing the naming pass that also did `State` → `NodeState`,
  `V` → `Node` and `Round` → `Time`. All are `Sts2`-only: `Sts` and the untracked `Sts2D`
  keep the old vocabulary, so cross-attempt greps will not line up.
- **One record per validator, not parallel maps** (2026-08-01). `Config` was
  `clock : V → Round`, `st : V → State`, `view : V → View`; it is now
  `nodes : V → Local V Msg State` with `Local` holding those three. An action names
  the single field it changes, via `Config.update p f`, and adding per-validator state
  touches one structure. `Config.clock/st/view` survive as thin readers, so every
  existing `x[i].view p` still reads the same — the change is entirely on the update
  side.
- **Assumptions are predicates on executions, not step conditions** (`Synchrony`,
  `Relay`, `Diligent`, `TimeDiverges`, `ViewsSound`), because the two models
  impose different ones over the same step relation. Cost: a liveness theorem is
  vacuous if its assumption set is unsatisfiable, so a realizability lemma
  exhibiting one compliant execution is owed.
- **`Common.System` cannot express liveness** — it is `Init`/`Step`/`Reachable`/
  `Invariant`, all state-based. Hence `Execution` (with labels recorded, so
  `Diligent` can talk about *which* transitions occur).
- **Security definitions abstract over the output** and a prefix relation, so
  blocks, chains and the transaction pool stay out of the framework.

Two example files. `Sts2/Framework/CustomEvents.lean` covers protocol-specific
events: a protocol with **two** timers, showing that `Ev` is just an inductive the
protocol picks, that `enabled` discriminates per event (and reads the state, not
only the round), and that **a timer reaction must push its own deadline forward**
— `enabled` is re-checked against the new state, so a timer that fails to
reschedule stays enabled and can fire again immediately. That hazard is the
protocol's responsibility; unlike tick-idempotence, the framework cannot rule it
out structurally.

`Sts2/Framework/Example.lean` is the entry point for "how do I use this": a toy
announce-once protocol placed under **both** models, which is what actually
checks that the parameterisation fits together. It also demonstrates the sleep
semantics concretely (a validator asleep until round 10 is not active, hence owed
no deliveries, and is owed everything the moment it wakes).

Known gaps, deliberate:

- **Nothing probabilistic.** Majorum's `wop`/`negl(λ)`/`negl(κ)` statements and
  VRF *unpredictability* are out of reach; proposer election must be idealized
  (an abstract `proposer : Slot → V` plus a `GoodLeader` predicate), the way a sibling formalization
  idealizes signatures. This bounds what "liveness proved" can mean here.
- `Models.Majorum.Params.participation` encodes the joining protocol as "awake
  throughout the preceding slot". The paper's window is
  `(voting(t−2)+Δ, voting(t−1)+Δ]`; **tighten this before any liveness claim
  leans on it**.
- Majorum's `Compliant` uses truncated `t - 1` at `t = 0` instead of the paper's
  `H_i := ∅` convention for `i < 0`.
- Mildly adaptive corruption is stated as `CorruptionDelay` against a `requested`
  schedule. Fixing the whole schedule in advance models a *non-adaptive*
  adversary, which is weaker than both papers assume — worth revisiting.
#### Framework.Sts2MX — scratch fork of Sts2M (2026-08-06)

`Framework/Sts2MX/` + `Framework/Sts2MX.lean`, namespace `Framework.Sts2MX`. Created
2026-08-06 as a **verbatim copy of `Framework/Sts2M/`** with `Sts2M` → `Sts2MX` throughout
(every occurrence in `Sts2M` was of the form `Framework.Sts2M`/`Framework/Sts2M`, i.e. a
self-reference, so the rename is mechanical and lossless — `Sts2MX/Lemmas.lean` diffs empty
against `sed s/Sts2M/Sts2MX/ Sts2M/Lemmas.lean`).

**Why**: to try changes to the multiset-log framework while `Sts2M` is in use by other work.
`Sts2M` is the development target and carries both protocol models (the first consumer's model ~16.5k
lines, the second consumer's model); editing it in place would disturb them.

Decisions taken (user's, 2026-08-06):

- **Framework only** — no protocol model was copied. `Sts2MX`'s own
  `Example`/`CustomEvents`/`Models` files are what exercise it, so it type-checks standalone.
  Nothing outside `Sts2MX` imports it.
- **Tracked, not gitignored** — unlike `Framework/Sts2D/`, which was untracked precisely so
  it could not drift. `Sts2MX` will drift from `Sts2M`; that is the point, and the drift is
  meant to be in version control.
- Named with the `Sts2M` prefix so the lineage is explicit: it is a fork of **M**, not a
  sibling attempt like `Sts2A`/`Sts2C`, which vary one design choice against `Sts2`.

No lakefile or Makefile change was needed: the `Framework` lib globs `Framework.+` and
`make framework` greps/builds the whole directory, so `import Framework.Sts2MX` in
`Framework.lean` was the only wiring. `make framework` passes (974 jobs).

It inherits `Sts2M`'s three linter warnings in `Lemmas.lean` (an unused
`DecidableEq` section variable at `Config.ext'`, two unused `simp` arguments at line 327) —
they are pre-existing in `Sts2M`, not artifacts of the copy.

##### The `Config Node Msg NodeState` question, tried three ways (2026-08-06)

The open question above, built rather than argued. Three variants of `Protocol.lean`, each
carrying the **same 24 declarations in the same order with the same one-line docstrings**, so
the only difference is how types are spelled — plus a fourth design tried afterwards:

- `Var/Protocol.lean` — section `variable`s. **Chosen, and folded into `Spec/Protocol.lean`
  on 2026-08-07**; the variant file was deleted once its style was applied, so its
  measurements below are of a file that no longer exists.
- `Ntn/Protocol.lean` — one `local notation` per applied type. **Deleted 2026-08-07.**
- `Sig/Protocol.lean` — the four parameters bundled into `structure Signature`, giving
  `Config σ`. **Deleted 2026-08-07.**
- A `class Params` supplying the four types by instance resolution — tried in scratch only,
  never committed; see the finding below.

All three compiled; `make framework` was 977 jobs and clean. Measured on code lines only
(docstrings and comments stripped), against the baseline's 131 code lines / 5836 chars:

| | code lines | code chars | long spellings left |
| --- | --- | --- | --- |
| baseline `Protocol.lean` | 131 | 5836 | 51 |
| 1 `Var` | 127 | 5086 (−13%) | 31 |
| 2 `Ntn` | 128 | 5374 (−8%) | 22 |
| 3 `Sig` | 129 | 5319 (−9%) | 0 |

**The char column is the wrong headline.** Options 2 and 3 pay a one-time declaration cost
(6 notations; `Signature` plus two `abbrev`s) that option 1 does not, then eliminate uses.
The "long spellings left" column tracks what a reader meets: 51 → 31 → 22 → 0. Option 3's
zero is not a trick — it never writes the baseline's spellings at all.

Findings, in order of how much they cost to learn:

- **Option 2 must be `local notation`, not `scoped`, and then needs no options whatsoever.**
  A `scoped` or global notation outlives the section, so Lean prechecks its right-hand side
  and refuses `Node` — "Unknown identifier `Node` at quotation precheck". A `local` notation
  dies with the section and may depend on its variables. That is the whole rule, and it is
  coherent rather than an obstacle. `scoped notation "Time" => Nat` is legitimately scoped
  because `Nat` is global.
  - **The precheck error's own hint is a trap.** It suggests `set_option quotPrecheck false`,
    which silences the precheck but not *hygiene*, and a failed precheck generates no
    elaboration function — so every use site then reports "elaboration function for `termCfg`
    has not been implemented", an error that looks unrelated to what you changed.
  - **`scoped` + `set_option hygiene false` does compile**, and was the first version of this
    file. Rejected: hygiene off makes the right-hand side resolve at the *use* site, which
    buys exactly the two things the rules exist to prevent — an abbreviation escaping the
    variables it depends on, and one whose meaning is decided by whichever names surround it.
    Cost of doing it properly, measured: 9 residual spellings became 22, and 5214 chars
    became 5374.
  - **A notation over section variables cannot be used in a declaration that *rebinds* those
    names**, which is six declarations here (the four type declarations, `ActionSpec`,
    `system`) — they spell their types out. Under `local` the failure is loud and worth
    recognising: a field written `Loc` inside `structure Config (Node Msg NodeState : Type)`
    refers to the *section* variables, which the structure then auto-includes **in addition
    to** its own parameters, giving `@Config ?m ?m ?m Node Msg NodeState` — six parameters and
    an unsynthesizable mess at every use. With `hygiene false` the same text quietly resolves
    to the structure's own binders instead: same syntax, different type, no diagnostic.
  - `local` is a standard Mathlib idiom in this exact shape — `local notation "M" => Matrix n'
    n' R`, `local notation "Ω" => Quotient <| orbitRel G X`, `local notation "⟪" x ", " y "⟫"
    => inner 𝕜 x y`, dozens of them over section variables. Only 7 Mathlib files use
    `set_option hygiene false`, none of them these.
- **Option 2's decisive cost is that `local` does not cross files.** `Lemmas.lean`,
  `Execution.lean`, `Justified.lean` and `Reachable.lean` would each re-declare the block,
  as Mathlib re-declares `⟪·,·⟫` in seven files. The abbreviation can never become shared
  framework vocabulary the way `Time` and `View` are.
- **Option 2 shrinks goal display, contradicting what was recorded** — inside the declaring
  file. `notation` generates an unexpander, so a goal shows `c : Cfg`. Checked for the obvious
  unsoundness: it fires only when the arguments really are the ambient ones; a
  `Config Nat Bool String` in the same context still prints in full. Holds under `local` as
  well as under the rejected `hygiene false` version — it is a property of `notation`. This
  removes option 3's one exclusive advantage, though only within one file, where option 3's
  `Config σ` prints everywhere.
- **Option 1's argument-order constraint costs nothing here** — corrected 2026-08-07, having
  twice been recorded as costing something. Section variables are inserted *before* a
  declaration's own binders, in declaration order, so one global order must serve every
  signature in the section. Only one declaration loses: `Config.setNode` wants `(c) (p) (r)`
  and gets `(p) (r) (c)`, because `p` must precede `c` for the three writes to keep their
  configuration-last order. Dot notation finds the `Config` argument wherever it sits, so
  `c.setNode p r` is unchanged at every call site.
  - **`Step` was recorded here as a second and worse case. It is not.** The claim was that
    the action cannot sit *between* the variables, forcing `system` to eta-expand
    `Step := Step Pr S` into `fun a c c' => Step Pr S c c' a`. The obstacle was the file's
    layout, not the option: `inductive Action` sat after the writes, so `variable (a : Action
    …)` could only be declared after `c pre c'`, which are needed far earlier. Moving `Action`
    up to join the other type declarations puts `a` in the right slot and restores both the
    baseline signature and the partial application. Verified compiling.
  - It was then called "real damage", which was also wrong: every use of `Step` in the
    framework is fully applied (`Reachable.lean`, three sites in `Lemmas.lean`); the sole
    partial application is that one line in `system`.
  - **A related claim was wrong too, and the mechanism is worth keeping.** "Eta is definitional
    so the two forms are interchangeable" — eta relates `f` and `fun x => f x` and says nothing
    about *reordering* arguments. On an opaque `g`, `(fun a b => g b a) = g := rfl` is rejected.
    What actually holds is that the two `Step`s are *definitions with identical bodies and
    permuted signatures*, so both sides delta-unfold to the same lambda; the equality is
    delta + eta, and only because the bodies coincide.
- **Option 1 cannot reach return types**, which is where most of this file's noise is: six
  definitions return `Config Node Msg NodeState`. Nor types nested in other types
  (`Enabled : Config … → Prop`), nor the structure declarations. That ceiling is why its 31
  remaining spellings beat option 2's 22 by so little despite option 2 paying six declarations
  for the privilege.
- **Options 1 and 2 are not alternatives — 2 presupposes 1.** `Cfg` means "whatever `Node` is
  in scope here", so it is useful exactly where the names come from section variables, and
  useless where a declaration binds its own. The two compose; choosing between them is a false
  choice, and both stop at the same boundary.
- **Option 3's projections make short types longer.** `Schedule σ.Node`, `Multiset σ.Msg`,
  `[DecidableEq σ.Node] [DecidableEq σ.Msg]` — 39 lines of the file carry a `σ.Node`/`σ.Msg`.
  `SignedMsg σ.Node σ.Msg` would have been *worse* than the baseline, hence the
  `Signature.SignedMsg` and `Signature.View` abbrevs. The saving is real only for the types
  taking three or four parameters.
- **Option 3 coarsens dependencies, and that loses documentation.** `Event` needs only
  `Node`/`Msg`/`Ev`, `NodeStepResult` only `NodeState`/`Msg`; over `σ` they all depend on the
  whole bundle, so two protocols differing only in `NodeState` have distinct `Event` types and
  nothing records that events never look at protocol state. The baseline's parameter lists
  *are* that documentation.
- **Option 3's instance resolution was a non-issue**, contrary to the parked note. `σ.SignedMsg`
  is an `abbrev`, hence reducible, so the derived `DecidableEq` is found through it and the
  multiset subtraction in `extract` elaborates unaided. All three variants' proofs are
  byte-identical to the baseline's.
- **What option 3 still has that 2 does not**: `Config σ` names the bundle, so a reader can ask
  what `σ` is, and two signatures can be in scope at once — a simulation between two protocols
  would need that. `Cfg` names nothing. Nothing in the framework needs it today.

##### Option 4, and why `abbrev` is the question's real shape (2026-08-07)

- **A `class Params` supplying the four types is the shortest of all, and unusable.** With
  `class Params where Node : Type; …` plus `export Params (Node Msg NodeState)`, class
  projections take the instance instance-implicitly, so every applied type collapses to a bare
  word: `@f : [inst : Params] → Config → Node → Local`. It fails on plurality — two instances
  in one statement give "synthesized type class instance is not definitionally equal to
  expression inferred by typing rules", and the display becomes *dishonest*, printing two
  different types both as `Config`. Not hypothetical: a consumer's proof file `
  Simulation.lean` maps Algorithm-5 executions to Algorithm-2 configurations, putting
  `Config Node M (NodeState2 Node Tx)` in the same signature as `Exec Pr5 S`.
  Mathlib's invariant is the same lesson — `variable {R : Type*} [CommRing R]`: the carrier
  stays a type parameter, only the *structure on it* is a class, because you constantly need
  several carriers at once.
- **`abbrev` is what the ecosystem actually uses, and our case is its exact complement.**
  ~830 parameterless aliases across the local projects (Lean core 468, Mathlib 307, Aesop 39,
  batteries 10): `abbrev CoreM := ReaderT Context <| StateRefT State (EIO Exception)`. They
  work because the application is *closed*. `abbrev Cfg := Config Node Msg NodeState` becomes
  `@Cfg : {Node Msg NodeState : Type} → Type`, so every use is `@Cfg ?a ?b ?c` — and in a
  **binder** nothing can solve those metavariables, since the header is elaborated before the
  body. Lean says so directly: "all parameter types and holes in its header are resolved
  before its body is processed". Making them explicit gives `Cfg Node Msg NodeState`, no
  saving. The tension in one line: *you only save by omitting arguments, you can only omit
  what is inferrable, and a binder is where nothing is inferrable yet.* An ascription
  `(c : Cfg)` against an already-known type does elaborate — it fails only where we need it.
- **Ecosystem survey** (8 projects, ~11,300 files, 2026-08-07). Mathlib spells `Matrix m n α`
  out ~3000 times with no mitigation; a sibling formalization spells `StateView n Block Message Tx` out 90 times
  with none either. For pervasive types Mathlib uses **global mixfix notation with the
  parameters as notation arguments** — `notation:25 M " →ₗ[" R "] " M₂ => LinearMap (RingHom.id
  R) M M₂`, ~93 of them — which is strictly better than a `local notation` (global, hygienic,
  precheck-clean, no `set_option`) but does not transfer: it wins by burying a parameter and
  reading as an arrow, and our parameter list *is* the length. Structures bundling ≥2 `Type`
  fields: 17 in 11,300 files, **none for brevity** — Mathlib's `MonCat`/`RootPairingCat` bundle
  a carrier with its instances to make a category object (and still spell `RootPairing index R
  weight coweight` out inside), and Aesop's `TreeSpec` is an abstraction barrier for a mutual
  inductive that immediately *unbundles* (`def Goal := tree.Goal`) so downstream never carries
  projections — the very cost option 3 would impose. `local notation` is 604/607
  Mathlib-specific; `set_option hygiene false` appears ~18 times in all 11,300 files.
- **Where our occurrences are**: `Framework/Sts2M/` 129, a consumer's tree 19, a second consumer's tree 16. The
  problem is framework-internal, which is what rules out any option whose cost is paid
  downstream.

**Applied across `Spec/` and `Analysis/` (2026-08-07).** Beyond `Spec/Protocol.lean`:
`Analysis/Lemmas.lean` (the thirteen field lemmas, `applyNodeStepResult_surjective`, and
`Pr`/`S` for both eliminators and `sent_mono`), `Analysis/Justified.lean` (the two helpers),
`Analysis/Execution.lean` (`x`, `i`), `Spec/Execution.lean` (`x`/`i`/`a` for the fairness
definitions, `out` for `Safe`/`Live`/`Secure`). Long applied types across Sts2MX: **130 → 102**.

Three things learned doing it, all of which made the yield smaller than the 50 estimated:

- **A binder-position count overstates what `variable` can reach.** Most of `Lemmas.lean`'s 21
  `(d : Config …)` are ∀-binders *inside* `Step.elim` and `Step.elimR`'s case hypotheses, which
  no section variable can supply. Lemmas came down 62 → 39, not to ~24.
- **The `variable` declaration itself costs occurrences.** `Analysis/Justified.lean` lost three
  and gained two, netting one. Worth checking before editing a file with few repetitions.
- **A section variable used by one declaration is pure indirection**, and was reverted in
  `Analysis/Reachable.lean` where it netted zero.

Two mechanics confirmed by experiment, both contradicting things assumed earlier: a
declaration binding its **own** parameter of a section variable's name is entirely unaffected
(no error, no warning, and the variable is not additionally included), and a later `variable
{p}` after an earlier `variable (p)` simply replaces it. So the `section`/`end` I said would be
needed to stop the field-lemma block reaching the frame lemmas is not needed, and was not used.
One placement rule does bite: a `variable` command may not sit between a docstring and its
declaration.

**Decision (2026-08-07): option 1, applied opportunistically; nothing else.** `local notation`
stays available as a per-file measure if a file becomes hard to read.

**Applied the same day** to `Spec/Protocol.lean`: the section-variable block, and `inductive
Action` lifted above it so `a` can precede `c c'` and `system` keeps `Step := Step Pr S`. The
prose was kept — only the prototype's binder style and declaration order were taken, not its
trimmed one-line docstrings — and `Var/Protocol.lean` was deleted. Everything downstream
(`Analysis/Lemmas`, `Reachable`, `Justified`, `Execution`, both examples) compiled unchanged,
because the only signature whose order moved is `Config.setNode`, reached by dot notation.
`make framework` 977 jobs, clean.

##### Sts2MX reorganized: `Spec/` states, `Analysis/` proves (2026-08-07)

On the user's instruction that spec files must not contain theorems and that theorems and
examples belong in separate directories. The ten flat modules became:

- `Spec/` — `Message`, `Schedule`, `Protocol`, `Execution`.
- `Analysis/` — `Lemmas`, `Reachable`, `Justified`, `Execution`.
- `Examples/` — `Models`, `Example`, `CustomEvents`.
- No fourth directory: the `Var/` prototype was folded into `Spec/Protocol.lean` and deleted.

**The boundary is not `def` versus `theorem`** — that was the first split and it was wrong.
`Spec/` is *the model*; `Analysis/` is *what has been proved about the model*. A definition
coined to be a theorem's conclusion or its hypotheses belongs beside that theorem. Four were
misplaced by the syntactic rule and moved on 2026-08-07 after the user pointed it out:
`Reachable` and `ViewsSound` into `Analysis/Reachable.lean`, `Justified` and `Justifies` into
`Analysis/Justified.lean`. The test that settled it was empirical — none of the four is
mentioned by `Step`, `Init`, `Execution` or `Models`, none by any protocol built on the
framework, and `Spec/Execution.lean`'s only reference to `Reachable` had become a vestigial
`import`. `Reachable` was the one genuine judgement call, being the standard semantic
companion to `Init`/`Step` rather than a predicate coined for one proof; it moved anyway,
because a boundary with no exceptions says something sharper than one with.

`Execution` split in two; `Reachable` and `Justified` moved whole into `Analysis/`; the rest
moved whole into `Spec/`. No `Spec/` file imports an `Analysis/` file.

**`Models` moved to `Examples/` on 2026-08-07**, for the same boundary reason plus a worse
one. Two *instances* of the framework are not the framework's spec — and this instance is
superseded. A consumer's assumptions file states outright that its `Sleepiness`
supersedes `Framework.Sts2M.Models.Majorum.Params.Compliant`, that nothing there calls it,
and that the framework's version is the worse statement on two counts: it inlines the joining
window, so the constraint reads as though joining were part of the sleepiness bound, and it
needs a `2 ≤ t` condition that vanishes once slots are `Int`. A consumer's own `Params` has no
`n` and no `fBound`. **The file's stated justification does not hold** — "if either stops
being expressible, this file stops compiling" only checks that *something named* `Compliant`
typechecks, and it stayed green all the way through being replaced. Real validation of the
parameterisation is a consumer and a second consumer building on the framework. Kept rather than deleted
because it is the only place both interval operators (`awakeSomewhere` vs `awakeThroughout`)
are exercised, and because assembling eleven à-la-carte predicates into two plausible whole
models smoke-tests that they compose; its docstring now says all of this, so it cannot be
mistaken for the paper again.

**The one exception, and it is forced.** `Spec/Protocol.lean` keeps five theorems, because a
*definition* needs them: `spec`'s `feasible` field is Event-B's FIS obligation, discharged by
`nodeStep_total`, which rests on `nodeStep_iff_exists`, `extract_applyNodeStepResult` and the
two `rfl` read-backs `nodes_apply` and `Config.setNode_apply`. The alternative — a
`Spec/Transition.lean` holding `spec`/`Step`/`Init`/`system` and importing
`Analysis/NodeStep.lean` — was considered and rejected: one `Spec → Analysis` edge is a worse
trade than one documented exception. `make framework` is 978 jobs, clean, with only the three
linter warnings inherited from `Sts2M`'s `Lemmas.lean`.

## The flavours renamed (2026-08-10)

The letter names said nothing to a reader: `Sts2A` versus `Sts2C` versus `Sts2M` gives no clue
which is which, and `Sts2Orig` did not say that it is the baseline the rest vary. Renamed, on
the user's request, to what each flavour does — directories, root modules, namespaces,
`lean_lib` names, `make` targets and docs, in one pass. The mapping is at the top of this file
and in [README.md](README.md).

**Prefix kept.** The names are `Sts`-prefixed (`StsMultisetLog`, not `MultisetLog`) because
these are *top-level module roots*: a consumer resolves them in one build graph alongside
Mathlib and its own libraries, where a root named `MultisetLog` is an invitation to collide.
The same reasoning is why `Sts2Orig` was never called `Sts2` here — that collided with a lib
name a consumer already uses.

**The letters were kept discoverable rather than erased.** They are the axis of the measured
comparison of step presentations (A/B/C/D, above), so the new names carry the letter in their
docstring title — "inductive step (presentation A)" — and every root module opens with
`Formerly Sts2A`. Historical entries in this file were **not** rewritten: the log is evidence,
and a mapping table at the top costs one lookup where a rewrite would cost the record.

**Consumer impact, not applied here.** The consuming repository still refers to the old names in
~280 places — 134 `Framework.Sts2MX`, 84 `import Sts2MX`, 58 `Framework.Sts2M`, 5
`import Sts2M`, plus its own `lakefile.toml` and its pre-extraction copies of the framework.
Nothing outside this repository was touched, and no alias or deprecated re-export was left behind
here: an alias would keep two names alive for exactly the flavours whose API is supposed to be
stable, and a consumer discovering the rename at its next build is cheaper than a consumer
discovering it years later. The port is a mechanical `Sts2MX` → `StsMultisetLogLayered`,
`Sts2M` → `StsMultisetLog`, longest name first.

**Mechanics worth reusing.** Order the substitutions longest-first (`Sts2Orig`, `Sts2MX`,
`Sts2M`, `Sts2A`, `Sts2C`, `Sts2D`, then bare `Sts2`), or `Sts2M` eats the `Sts2MX` prefix and
bare `Sts2` eats everything. Two tokens had to be protected from the sweep: identifiers that
*end* in `Sts2M`, which name consumer models rather than flavours. And a blind sweep does rewrite
*historical* sentences into nonsense — `lakefile.toml`'s note that "`Sts2` collides with a lib
name a consumer already uses" became self-referential, and `CLAUDE.md`'s "read old entries as
`Framework/Sts2M/`" lost the very name it was translating. Both were repaired by hand; check every
sentence that *mentions* an old name rather than *using* it.

## The flat multiset-log flavour removed; the fork took its name (2026-08-10)

`Sts2M` — the flat multiset-log flavour, briefly `StsMultisetLog` after the renaming — was
**deleted** on the user's instruction, and `Sts2MX`, the fork that had superseded it, was renamed
into its place. So `StsMultisetLog` is now the layered flavour, and five flavours remain.

This is a **departure from "freeze, do not delete"**, which [CLAUDE.md](CLAUDE.md) still states
for the rest: the two flavours had drifted into duplicates that differed only in presentation,
and keeping both meant reading the older one to find out it was the older one. The rule is
unchanged for the four remaining frozen flavours, which each answer a *different* question.

**What the two actually differed in, measured before the deletion**, since the code can no longer
be diffed:

- **Identical API.** Both declared the same **116** names — `def`/`theorem`/`abbrev`/`structure`/
  `inductive`/`instance`, compared as sorted sets — with nothing only in one. (An earlier count of
  104 in `CLAUDE.md`'s porting note was taken at the time of the port, before later additions.)
- **Files split by role.** Flat `Message`/`Schedule`/`Protocol`/`Execution` →  `Spec/*`;
  `Lemmas`/`Reachable`/`Justified` → `Analysis/*`; `Models`/`Example`/`CustomEvents` →
  `Examples/*`. Not only a move: three theorems left the flat `Execution.lean` for a new
  `Analysis/Execution.lean` — `TimeStepwise.timeMonotone`, `Execution.reachable`, `views_sound` —
  which is why `Spec/Execution.lean` proves nothing (278 lines → 260 + 41).
- **Binders from section `variable`s** rather than repeated per declaration. This made
  `Spec/Protocol.lean` *longer* than the flat `Protocol.lean` (426 vs 409), because it carries the
  docstring explaining the choice and its two traps: `Action` must be declared above the
  `variable` block, or `Step` gets `(Pr) (S) (c) (c') (a)` and `system` loses `Step := Step Pr S`;
  and `Config.setNode` takes `(p) (r) (c)` to keep the configuration-last order elsewhere.
- **Everything else was small drift.** Per-file diff sizes, module name normalized: `Message` 0,
  `Schedule`/`CustomEvents` 2, `Example` 6, `Justified` 13, `Reachable` 23, `Models` 36 (mostly
  the expanded "this is not the authoritative model" caveat), `Lemmas` 64. Totals 1903 → 2025
  lines.

**Mechanics: `git mv A B` where `B` exists moves `A` *into* `B`.** The `git rm` of the flat
flavour was refused first — staged rename content differs from both HEAD and the file, which wants
`-f` — and the following `git mv` therefore nested the whole layered tree at
`StsMultisetLog/StsMultisetLogLayered/` instead of failing. Unwound by hand. Order the two
operations the other way, or check that the destination is gone before moving onto it.

## Vocabulary aligned to the active flavour (2026-08-10)

The four frozen flavours now use the active flavour's words for the same things, on the user's
instruction. 228 lines changed across 20 files; all five flavours still build.

**Renamed, because the two names denoted the same thing.** `Synchronized` →
`SynchronizedClocks` in all four (definitions were character-identical to the active one's).
`Reacts` → `NodeStep`, `reacts_total` → `nodeStep_total`, `justified_reacts` →
`justified_nodeStep` where present. In `StsConditionSplit`, additionally `V` → `Node`, `State` →
`NodeState`, the `Round` notation → `Time`, `Effect` → `NodeStepResult`, `install` →
`applyNodeStepResult`, and the docstring phrase "Guard and effect" → "Condition and effect".

**Deliberately not renamed — the name *is* the experiment.** `StsStepInductive`'s `Enabled` and
its six `enabled_*` lemmas; `StsReactionInLabel`'s `Move`, `Move.action`, `Reaction`,
`permits_total`, `enabled_iff`; `StsConditionSplit`'s `guard`, `StepGuard`, `StepInline`,
`step_iff_guard`, `stepGuard_iff_inline`, `enabled_iff`, `ActionSpec.Choice`/`Permits`/`Apply`.
Renaming any of these would erase what the flavour was built to demonstrate.

**Deliberately not renamed — same role, different semantics.** Two near-misses caught by reading
the definitions before trusting the names:

- `StsConditionSplit.Config.update c p f` takes a *function* `Local → Local`; the active
  flavour's `Config.setNode` takes a replacement record. Renaming would have made a signature
  lie.
- `StsConditionSplit.bumped p c` advances a clock **by one**; the active flavour's
  `setClock p t c` *assigns* `t`. That difference is the design — D's `tick` carries no time
  argument — and is exactly what the active flavour's `Diligent` assumption exists to replace.
  For the same reason D's `TickFair`/`AdvanceFair` were left alone: `Diligent` is not a renaming
  of `TickFair`, it is a different statement.

**One mis-rename, caught afterwards.** `\bState\b` → `NodeState` also hit `structure System
(State : Type u)` in `StsConditionSplit`, whose parameter is the transition system's *state
space*, not a validator's protocol state — the other four flavours called it `Carrier` at the
time. The result compiled (a type-parameter name binds nothing) and read as a lie. Corrected to
match, and then all five were renamed to `SystemState`, see below.

**Two more casualties of the same sweep, in prose rather than code.** `install` → `applyNode
StepResult` rewrote the sentence "Apply a reaction: *install* `p`'s new state" into "Apply a
reaction: *applyNodeStepResult* `p`'s new state"; and `State` → `NodeState` turned the field
docstring "State afterwards" into "NodeState afterwards". Both fixed to the wording the other
flavours use ("store", "The node's state afterwards").

**The lesson, three times over:** a word-boundary rename is still wrong when the word names two
different things, or is an ordinary English word as well as an identifier. Where to look:
universe-polymorphic parameters (`grep 'Type u'` found the `System` case; `Execution`'s
`{St Lbl}` was safe only because it is spelled differently), and every docstring containing the
old token, since renaming a verb like `install` produces grammatical nonsense that compiles.

**Result, measured.** `StsRelationalSetLog` now declares a strict *subset* of the active
flavour's 116 names — zero names of its own. The extras that remain elsewhere are exactly the
lists above, so a name diff between any two flavours is now a report on design, not on wording.
Re-run it with the declaration-name diff in [CLAUDE.md](CLAUDE.md)'s "habit worth keeping".

**Note the tension with "freeze, do not delete".** Editing a frozen flavour at all is a
departure; the justification is that renaming an identifier changes no measurement, and the
comparison the frozen flavours exist for is *easier* to read once only the design differs. What
must not happen is a change to a frozen flavour's structure or proofs.

## "active/frozen" dropped as flavour labels (2026-08-10)

The README no longer labels flavours *active* and *frozen*. Both words were wrong for what they
described, on the user's reading: "active" says only that work happens there, when the fact a
reader needs is **which flavour to pick** — `StsMultisetLog`, as the most general and most
developed; and "frozen" reads as abandoned code, when the other four are working alternatives,
each isolating one design decision, any of which is a reasonable choice if that design is what
you want.

The table's third column is now **Role**: *suggested, and the most general* for one, *one design
choice changed* for three, *the original, kept for comparison* for the baseline. `lakefile.toml`'s
per-`lean_lib` comments and [CLAUDE.md](CLAUDE.md) follow the same wording.

The *concept* of freezing survives where it belongs — [CLAUDE.md](CLAUDE.md) still says to record
an experiment's result and not delete the flavour, and not to change a settled flavour's design.
What changed is only the label a reader sees.

## Section added on the underlying theory (2026-08-10)

[README.md](README.md) now opens with "The theory it rests on": the framework is a labelled state
transition system (`System` is literally `Init` plus a labelled `Step`), why the step is a
*relation* — adversary nondeterminism plus the protocol's own — and hence why `feasible` exists
and is Event-B's FIS obligation; that assumptions are predicates over executions rather than
constraints baked into `Step`, so a theorem can name the ones it needs; `WeakFair`/`StrongFair`
in their usual forms; `Safe`/`Live`/`Secure` as Majorum's Definitions 1–3 with the classical
safety/liveness split; and invariants by induction over `Reachable`.

It ends with background reading — Lamport's *Specifying Systems* and the TLA paper, Alpern and
Schneider's *Defining Liveness*, Abrial's *Modeling in Event-B*, Baier and Katoen, and the
Mathlib docs. Every link was checked to resolve (`curl -o /dev/null -w '%{http_code}'`, all 200);
`http://www.event-b.org/` was the one candidate that 404s, replaced by the book's DOI and the
Event-B wiki. Worth re-checking if they are ever cited from elsewhere.

## `System`'s state parameter: `Carrier` → `SystemState` (2026-08-10)

All five flavours now read `structure System (SystemState : Type u) (Label : Type v)`, on the
user's instruction, after they asked where "carrier" is used in this sense — a fair challenge.

**Where the word came from and why it was wrong.** `Carrier` was in the framework from the
commits that created each flavour. It is standard vocabulary in *algebra* — the carrier set of an
algebraic structure — and Mathlib uses it that way for substructures, which is the likely source.
It is **not** used for a transition system's state space: Lamport, Baier and Katoen, and Keller's
original labelled transition systems all say *states*. A reader coming from the transition-system
side stops at it, which is exactly what happened.

**Cost of the change: none outside the declaration.** `Carrier` was referenced only inside its own
`structure System` in each flavour — nothing passes it as a named argument, `system` supplies it
positionally as `System (Config …) (Action …)`, and `Execution` binds its own `{St Lbl}`. So the
rename is five declarations plus one line of `README.md`, with no call site touched and nothing
for a consumer to port. All five flavours rebuilt clean.

## History rewritten to drop cross-project references (2026-08-10)

All commits were rewritten so that no file in any of them names a neighbouring project or its
directory layout. Papers are untouched, deliberately: `Majorum`, `3SF`, `TOB-SVD` and the BibTeX
key `damato2026majorum` are citations the design target depends on, not project names.

Two things to know if this ever needs undoing or repeating:

- **The mapping, and the original wording, are in `CLAUDE_LOCAL.md`** — gitignored, so it never
  leaves this machine, and it is the only place the pre-rewrite text survives once the recovery
  refs are pruned.
- **The scrub had to be whole-text, not line-based.** Two sentences broke across line
  boundaries — a possessive whose noun was on the next line, and "The X / formalization hit the
  same thing" — so a line-based `sed` produced a stray apostrophe in one and a doubled noun in
  the other. A replacement landing at the start of a sentence also has to be capitalised, which
  a line-based pass cannot see when the sentence began on the previous line.

A scan for the things that usually matter found none of them: no absolute or home-directory
paths in any commit, no credentials or keys, no binary blobs, no hostnames or private URLs, and
nothing in the commit messages but `Co-Authored-By` trailers.
