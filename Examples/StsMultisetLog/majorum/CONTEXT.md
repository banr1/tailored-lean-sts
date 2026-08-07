# Majorum — context log

Durable notes for the Majorum formalization: `Examples/StsMultisetLog/majorum/`, lib `MajorumExample` over
the framework's flat multiset-log flavour, source paper at arXiv:2601.03862v1.

Moved here on 2026-08-08 from the repository-root [CONTEXT.md](../../CONTEXT.md), where this
had grown to some 2.2k lines. The root file keeps what is framework-wide or shared between
experiments; anything that is only about Majorum belongs here. What to write and when is in
[CLAUDE.md](../../CLAUDE.md)'s "Keeping context across sessions" section — the same rules,
applied to this file.

Entries are in the order they were in the root log.

Majorum (3SF). **Statements only** as of 2026-08-02 — `Examples/StsMultisetLog/majorum/` holds the
paper's Definitions 4-7 (`Security.lean`) and all seven of its theorems (`Theorems.lean`)
as `Prop`-valued definitions over the framework's flat multiset-log flavour. No protocol is modelled, nothing is
proved.

- **Source paper**: arXiv:2601.03862v1.
  *Majorum: Ebb-and-Flow Consensus with Dynamic Quorums*, Francesco D'Amato, Roberto
  Saltini, Thanh-Hai Tran, Yann Vonlanthen, Luca Zanolini (Ethereum Foundation).
  arXiv:2601.03862, **v1, 7 Jan 2026** — the only version at time of download — to appear at
  FC'26. Pinned URL <https://arxiv.org/pdf/2601.03862v1>, SHA-256
  `5ea6f61cf1d152a3740d9dd9f8e49c9eb0d36381dd32b20537b44df223bcf7d6`, 1039710 bytes.
- **Statements cite numbered theorems and definitions**, not lines of the Overleaf working
  copy at the paper's own source. That copy was the original source and is *not*
  included here; its line numbers move with every Overleaf sync. Checked on 2026-08-03 that v1
  agrees with it on everything rendered: the same seven theorems in the same order with the
  same names (1 Reorg Resilience, 2 dynamic availability, 3/4 their FFG analogues,
  5 Accountable Safety, 6 Liveness, 7 ebb-and-flow), Definitions 1-7, Theorem 5 opening
  `Let f ∈ [0,n]`, and Constraint (1) reading `|H_{vote(t-1)} \ A_{vote(t)}| > |A_{vote(t)}|`.
  The published text writes `vote(t)` where the tex has `\voting{t}`.
- **`def ... : Prop`, never `theorem`.** The no-`sorry` rule forbids stating an unproved
  theorem; a `Prop`-valued definition says what the claim *is* without asserting it, and
  becomes the statement of a real theorem once proved. `make majorum` checks this, and here
  the check means the opposite of elsewhere: it confirms nothing was smuggled in as
  `theorem ... := sorry`.
- **Three things the renderings cannot say**, all recorded at the definitions: overwhelming
  probability and `negl` (four of the seven theorems are probabilistic); `O(k)` / `O(D)`,
  which become explicit parameters, so quantifying over them is weaker than asserting an
  asymptotic bound; and the cryptographic proof in accountable safety, idealized to a
  function from the message log to a set of validators.
- **Assumptions are per theorem, not one model.** Majorum proves its theorems under
  *different* hypotheses, so `Examples/StsMultisetLog/majorum/Assumptions.lean` names groups
  (`Wellformed`, `Network`, `Synchronous`, `Sleepiness`, `GlobalAwake`, `Resilience`) and
  each statement cites its own. Evidence from the paper: accountable safety opens `Assume
  $f \in [0,n]$` (the paper's source line 983, `:1026`), explicitly overriding the standing `f < n/3`, and
  `:1298` calls it "always" accountably safe; the dynamic-availability analysis assumes
  `GST = 0` (`:1045`); liveness assumes `f < n/3` (`:1426`). Using
  `Models.Majorum.Params.Model` for all of them would hand accountable safety a synchrony
  assumption and a corruption bound it does not need, weakening the paper's strongest claim.
- **`majorum` is self-contained** (2026-08-03): its own `Params`, no dependency on
  `the framework's flat multiset-log flavour.Models`. That module shows the framework can *express* Majorum's model;
  this one states the parameters its *claims* are made over, and the two are free to diverge.
  It also settles a problem found the day before: the framework's `Params` carries
  `fBound : 3 * f < n` as a **field**, so merely taking one assumes `f < n/3` — which
  Theorem 5 does not, being proved for `f ∈ [0,n]`. The bound is now a conjunct of
  `Resilience`, so a theorem that does not assume it does not mention it. 3SF's `Params` was
  built the same way from the start, for the same reason.
- **Slots are `Int`** in the local `Params`, unlike the framework's `Nat` version. `t - 1`
  then does not truncate, so `Sleepiness` reads at slot `t` exactly as the paper writes it,
  with no `t+1` re-indexing and no `2 ≤ t` condition.
- **Review status of the seven statements** (2026-08-03). Reviewed and corrected:
  **Theorem 1** (`ThmReorgResilienceGA`) and **Theorem 2** (`ThmDynamicAvailabilityGA`).
  Not yet reviewed, and marked as such in `Theorems.lean` under a "Not yet reviewed" heading:
  **3, 4** (the FFG pair), **5** (accountable safety — the interesting one, since it is why
  `Resilience` is separable at all), **6** (liveness, the only statement rendered in full) and
  **7** (ebb-and-flow). Each unreviewed one still takes the execution as a *parameter* rather
  than quantifying over the model's executions, so it asserts nothing.
  Theorem 2's review turned up the substantive point: its network assumption is
  `Synchronous` (the Δ bound from round 0) and **not** `Network` (the bound after `Q.gst`),
  because dynamic availability unqualified means "always secure when `GST = 0`". Passing
  `Network` there would state something the paper does not claim.
- **Reviewing the statements found two defects, both in `ThmReorgResilienceGA`** (fixed
  2026-08-02, the rest still to review): it took the execution as a *parameter*, so it
  asserted nothing and was false at a hostile `x` — a theorem must quantify over the
  executions its model admits; and reorg resilience took an opaque `honestAt : Time → Prop`
  tied to neither the proposer nor the schedule, dischargeable by `fun _ => True`. Honesty is
  now `q ∉ S.adv (proposing t)` with `proposedBy` naming the proposer.
- **Constraint (1) is written out in `Assumptions.lean`, over a named `Active`** (2026-08-02).
  The paper's `H_r` is the set of validators *active* at `r`, which the framework cannot
  define — participation is the protocol's business. Majorum's joining protocol determines
  it (the paper's source line 129): a validator waking in `(voting(t-2)+Δ, voting(t-1)+Δ]` becomes active
  at `voting(t)`, so `Active t = awakeThroughout (voting(t-1)+Δ) (voting t)`, written
  `voting t - 3Δ` for the lower end so that `Int` subtraction avoids `Nat` truncation.
  `Models.Majorum.Params.Compliant` had the *same* window inlined — an earlier note here
  calling that a conflation of two notions was **wrong**; the window is `H`, and the only
  defect was that it was anonymous, making the joining protocol look like part of the
  sleepiness bound. Naming `Active` restores the constraint to the paper's one line, and
  re-indexing by `t+1` removes `Compliant`'s `2 ≤ t` condition so every slot is covered.
  Known gap: at `t = 0` the window reaches back to `-2Δ`, where the schedule is total but the
  paper's `H_i := ∅` convention for `i < 0` is not implemented. Nothing depends on it, since
  the constraint starts at slot 1.
- **`AwakeHonest` and `GlobalAwake` are compatible**, checked because they look as though
  they might not be: `Schedule.awake` is the awake *honest* set by construction, so
  disjointness from `adv` is free, and `GlobalAwakeTime` subtracts `adv` before requiring
  awakeness. A witness with a non-empty adversary is proved in the scratchpad. What they do
  jointly imply is `S.awake r = univ \ S.adv r` for `r ≥ gat` — **nobody sleeps after GAT**,
  so any theorem assuming `GlobalAwake` reasons in the static-participation regime, where
  Constraint (1) is close to free (it would follow from `f < n/2` if `Active` were `awake`).
  The joining protocol is the only thing keeping the two apart.
- **Algorithm 5 is specified** (2026-08-03), in
  `Examples/StsMultisetLog/majorum/Algorithm5.lean` (named `Protocol.lean` until 2026-08-03) —
  the first actual protocol model in this repository, as opposed to statements about one.
  `Msg` (propose/vote), `NodeState` (chAva, chFin, vFrozen, chFrozen, gjFrozen), and a
  `handler` dispatching on `r % 4Δ` into the four phases. Decisions worth keeping:
  - **`Ev := Empty`.** Every action happens at a fixed round, so `tick` drives all four
    phases and there is nothing for a protocol-specific event to carry.
  - **`recv` is a no-op.** Lines 29-38 process propose messages received in `[4Δt, 4Δt+Δ]`,
    but the paper delays that processing until `vote(t)` — so the vote handler reads them out
    of the view, which the framework maintains. The framework's decision to hold the view and
    file deliveries before the reaction runs is what makes this a one-liner.
  - **Fork-choice and finality are abstracted** into a `Components` record: `MFC`, `Extend`,
    `fastconfirmsimple`, `GJ`, `GF`, `J`, `valid`, the κ-prefix and the prefix order. The
    paper treats them as given when presenting Algorithm 5; inlining them would be specifying
    Section 4 and Algorithm 2 instead. `Chain`, `QC` and the proposer election are parameters
    too — the last idealizing the VRF, as a sibling formalization idealizes signatures.
  - **Two known infidelities.** Processing several valid proposals for one slot depends on
    arrival order, which the paper leaves open and `processProposals` resolves by folding
    over `V.toList`; only an equivocating proposer can tell. And that makes the model
    **noncomputable** (`Finset.toList` is), so unlike the framework's examples nothing here
    can be `decide`d. Making `step` relational at that point would fix both at once.
- **Everything Algorithm 5 calls is now defined too** (2026-08-03), in `Components.lean`;
  `algorithm5` is the protocol with them supplied, so nothing about Majorum is abstract any
  more except the proposer election. Chains are lists of blocks with prefix order; `MFC` is
  Algorithm 1 over the three vote filters (`FIL_eq`, `FIL_1-exp`, `FIL_lmd`);
  `fastconfirmsimple` is Algorithm 2; justification, finalization, `GJ` and `GF` are §4.
  Four modelling choices, all recorded at the definitions:
  - **`MFC`'s candidates come from the view.** It returns "the longest chain `ch ⪰ chC` such
    that …" over all chains, which is infinite. Restricting to chains someone voted for loses
    nothing, since a chain with no votes cannot meet a majority condition.
  - **Justification is an inductive `Prop`.** "Reachable from genesis by supermajority links"
    is a least fixed point, so it cannot be a `Bool` without deciding reachability; it is
    decided classically, which keeps the model noncomputable.
  - **`QC` had to stop being recursive.** The paper says a quorum certificate "consists of
    the corresponding vote messages", but a vote message carries a `QC`. `QCert` records
    (voter, chain, slot) triples instead, which is everything a certificate is used for.
  - **`Extend` appends one block** rather than producing "a chain of length `t`": the
    property the protocol then checks is `chp.p = t`, and the paper does not say what would
    fill the intervening slots.
- **Lemma 2 was attempted and is *not* proved** (2026-08-03). `Lemmas.lean` has the counting
  core — `quorum_inter` (two sets each over half a pool must meet),
  `comparable_of_common_extension` (prefixes of a common chain are nested) and
  `majority_chains_comparable` (so two majority-supported chains are comparable, which is
  what makes `mfc`'s "the longest such chain" a definite description). All three proved first
  try; the arithmetic is not the hard part.
  What Lemma 2 needs on top, recorded in the file so the next attempt starts informed: the
  execution layer, because "all validators in `H_{vote(t)}` voted for extensions of `ch`" is
  about what happened, not about a view, and must be tied to `handler`'s vote branch having
  run (needs `Execution` and `Diligent`); `Synchrony` + `Relay` to get those votes into `V_i`
  by `propose(t+1)`; Constraint (1) to turn honest-majority into `MFC`'s majority; and a case
  analysis on `chfrozen` relating the `merge` branch to the `vote` branch a slot later. The
  joining-protocol step should be short, since `Active` already encodes it — the one place
  the earlier groundwork pays off directly.
  **Second attempt, reading the paper's proof** (same day): its Case 2 — "given that by
  definition `MFC ⪰ chfrozen`" — is now proved outright as `base_le_mfc`, a fold invariant on
  `mfc`; and Case 1's displayed inequality chain is `voters_lt_two_mul_honest`, pure `Finset`
  arithmetic. Case 1 still needs two things. The **containment** it starts from is where
  synchrony and the joining protocol enter, so it needs the execution layer. And a
  **maximality lemma for `mfc`** — that it returns a chain at least as long as every majority
  candidate — which with `majority_chains_comparable` would finish it.
  That last one was attempted and abandoned on a **misdiagnosis, corrected the same day**.
  The failure was "failed to synthesize `Decidable (mfcGuard …)`", which I recorded as the
  model's fold condition needing to be a `Bool` — a change to `Components.lean`. It is not: the
  condition *is* decidable, and what defeated instance search was naming it with a plain `def`,
  which is not reducible, leaving the conjunction opaque. An `abbrev` or `@[reducible] def`
  resolves it, with `noncomputable` on anything producing data, since the instance mentions
  `voters`. **No model change is needed** — the remaining work is the induction.
  Worth keeping as a Lean gotcha in its own right: a named `Prop` helper silently loses
  decidability at every use site unless it is reducible, and the error points at the
  instance rather than at the definition.
  **With that fixed, the `MFC` half of Lemma 2 is proved** (2026-08-03): `base_le_mfc` is
  Case 2, and `le_mfc_of_majority` is Case 1's conclusion — `MFC ⪰ ch` for any candidate
  extending the base and carrying a majority — via three fold invariants (never shortens, at
  least as long as any majority candidate, and either the base or majority-supported itself).
  All went through first try once the condition was an `abbrev`.
  **Lemma 2 now hangs on exactly one thing**: the containment
  `S(V_i,t+1) ⊆ (H \ A) ∪ (A ∪ …)` and `H \ A ⊆` the supporters of `ch`. Both are statements
  about an execution — "all validators in `H_{vote(t)}` voted for extensions of `ch`" plus
  `Synchrony`/`Relay` delivering those votes by `propose(t+1)` — so they need the execution
  layer and the fact that `handler`'s vote branch ran. Everything view-local is done.
- **Lemma 2 is false for the model as written — five defects, found 2026-08-03 by pushing
  the execution-level proof** (this supersedes "everything view-local is done": two of the
  defects are in `mfc` itself). Stopped before changing anything, per instruction. All five
  live under `Examples/StsMultisetLog/majorum` — the framework held up.
  1. **`candidates` must be prefix-closed** (`Components.lean`; `mfc` and
     `fastConfirmSimple` both read it). The recorded claim that voted-chains-only "loses
     nothing" is wrong in the direction Lemma 2 needs: split the honest votes 50/50 between
     two incomparable extensions of `ch` and no candidate passes the strict-majority test,
     so `mfc` returns `genesis` — while the paper's MFC, quantifying over *all* chains,
     returns `ch` (votes for extensions count towards `ch` itself). Fix: `insert chC` of
     all `List.inits` of voted chains; any chain with one supporting vote is a prefix of
     that vote's chain, so the closure is complete.
  2. **The handler does not implement the joining protocol** (`Algorithm5.lean`). The wake
     *event* sends nothing, but nothing suppresses the next ticks' sends: a validator woken
     at `4Δt` votes at `voting(t)`, where the paper keeps it silent until `voting(t+1)`.
     So `S(V_i, t+1)` can contain honest-but-not-active voters, the containment
     `S ⊆ (H\A) ∪ A` fails, and Constraint (1) cannot deliver the majority. Fix:
     `NodeState` gains an activation round, set by the wake handler from the paper's window
     formula — sound because under `SynchronizedClocks` even a just-woken validator's clock
     reads real time — and the propose/vote branches send `0` while `r < activeAt`, still
     updating state ("executes the protocol, but without sending any message").
  3. **Honest equivocation by double tick.** Nothing stops two ticks at one reading
     (`SynchronizedClocks` forces every tick of an awake validator to the current time, but
     time can stay put across many steps), and deliveries in between change the view, so
     the two vote sends can differ — `FIL_eq` then drops that validator and the count
     fails. The paper's atomic rounds make this structural; here it needs a new execution
     assumption in `Assumptions.lean`:
     `∀ i j p t, x.lbl i = .tick p t → x.lbl j = .tick p t → i = j`.
  4. **`validProposal` does not check the certificate** (recorded at the definition as
     deliberate). The vote-round half of Lemma 2 needs it: the line-36 update of `chfrozen`
     from a proposal's `chC` is bounded only because a valid `QC` certifies `≥ 2n/3`
     slot-`(t-1)` votes for extensions of `chC`. `QCert` already carries
     (voter, chain, slot) triples, so the check is writable — its exact slot discipline
     should be pinned down against the vote-round analysis, not guessed now.
  5. **`mfc` counts messages where the paper counts validators.** Two `vote` messages
     differing only in their fin-vote parts share sender, chain and slot, survive every
     filter, and are distinct elements — one sender can inflate the majority count, and two
     *incomparable* chains can then both pass it, making `le_mfc_of_majority`'s
     comparability hypothesis undischargeable. Algorithm 2's `fastcands` counts senders
     explicitly (`{v_j : …}`), so the paper's `|V^{ch,t}|` is sender cardinality; fix
     `Majority` to count `((… ∩ …).image SignedMsg.sender).card`. This also dissolves the
     sender/message mismatch between `Majority` and `majority_chains_comparable`.
  Two further layers are then still owed, both provable-looking: a **provenance invariant**
  (an honest validator's votes in any view came from its tick at its slot's vote reading —
  adversarial injection under that signature is excluded up to `voting(t+1)` by
  `MonotoneCorruption`, and `SynchronizedClocks` pins the tick's reading to real time), and
  — vote-round half only — **comparability of `chfrozen` with `ch`** through `merge` and
  `processProposals`, which drags in justified-checkpoint reasoning. Staging: fix 1, 2, 3
  and 5, prove the propose-round half; 4 and the `chfrozen` invariant belong to the
  vote-round half.
- **Fixes 1, 2, 3 and 5 applied** (2026-08-03, user-approved; 4 — the certificate check —
  stays deferred to the vote-round half, its slot discipline to be pinned against that
  analysis rather than guessed).
  - `candidates` is prefix-closed via `List.inits`, with the correct completeness argument
    in its docstring (the user's observation: a chain passes the majority test only if some
    vote *extends* it, making it a prefix of a chain the view carries — so prefixes of
    voted chains are complete, and minimal among complete sets).
  - `Majority` moved into `Components.lean` — `mfc` now tests it by name, ending the
    fragile syntactic sync between the fold condition and the proof file — and counts
    **senders** (`.image SignedMsg.sender`).
  - `NodeState` gained `activeAt`; the wake handler sets it via `activationRound`
    (`t = ⌈(r+2Δ)/4Δ⌉`, so `voting` of that ceiling — Nat ceiling division), and the
    propose and vote branches send `0` while `r < activeAt`, still updating state. Genesis
    convention: `activeAt := 0` at init, so initially-awake validators are active from the
    start; a schedule that emits wake events at time 0 would delay them to `voting(1)`,
    a divergence the paper's genesis glossing leaves open.
  - `OneTickPerReading` added to `Assumptions.lean`, à la carte.
  Knock-on strengthenings in `Lemmas.lean`: `majority_chains_comparable` (witness-threaded)
  is **replaced** by `majority_comparable`, hypothesis-free, via the new
  `chain_eq_of_same_sender` — after `FIL_eq`/`FIL_lmd` one sender has one chain, since the
  survivors carry the sender's maximal slot and same-slot different-chain pairs were both
  dropped. `mem_candidates_of_majority` makes membership automatic (a strict majority
  forces a supporting vote; prefix closure does the rest). `le_mfc_of_majority` therefore
  lost both side hypotheses: majority alone now gives `MFC ⪰ ch`, which is exactly the
  paper's step.
- **The provenance layer of Lemma 2 is proved** (2026-08-03, `Lemma2.lean`), on existing
  plus approved assumptions only. Spine: `emitted_of_mem_sent` (the multiset log starts
  empty and only grows, so members enter at a step), `emitted_step` (via `Step.elimR`: a
  step's contribution is the sender's own tick — with the message among that tick's handler
  sends — or an adversarial injection while corrupt), `mem_handler_send` (the handler sends
  only a propose at phase `0` or a vote at phase `Δ`, only once active, carrying the
  reading's slot). Composed: `vote_provenance` — an honest vote for slot `s` was sent by
  its sender's tick at reading `voting(s)`, at real time `voting(s)` (`SynchronizedClocks`
  turns reading into time through the *post*-configuration), with the joining gate open.
  Consequences: `voting_le_of_vote_mem` (no honest slot-`s` vote before `voting(s)`) and
  `honest_vote_unique` (one honest validator, one slot, one vote — `OneTickPerReading`'s
  one job, plus `handler_send_subsingleton`).
  Lean notes: the `if` inside the vote branch's `target` means `split_ifs` yields *two*
  vote leaves, so leaf dispatch should be `first | … | …` rather than positional bullets;
  `Multiset.not_mem_zero` does not exist (the `notMem` renaming again — use bare `simp`);
  `Multiset.sub_self`/`tsub_self` are unavailable for multisets here (no
  `CanonicallyOrderedAdd` instance found) — prove `s - s = 0` by `ext` + `count_sub`. The
  vote branch's shadowing `let s := processProposals …` was renamed `s'` so the send gate
  reads the *pre*-state's `activeAt`, which proofs can see through; `processProposals`
  never writes `activeAt`, so the two spellings agree.
- **The containment step of Lemma 2 needs two further execution assumptions — found
  2026-08-03, not yet approved, nothing applied.** The step: an honest slot-`t` voter must
  be in `Active(t)`. Provenance gives that its vote-tick had the joining gate open
  (`state.activeAt ≤ voting(t)`), and `activeAt ≤ voting(t)` does imply the validator's
  latest wake was early enough (`w ≤ voting(t-1)+Δ`, by the `activationRound` arithmetic) —
  **provided `activeAt` is faithful to the latest wake.** Nothing guarantees that:
  1. *Wake events are not guaranteed to fire.* The framework's `.wake` action is enabled
     exactly at asleep→awake transition configurations, but enabled is not taken. A missed
     wake leaves `activeAt` stale from an *older* wake (or from init `0`) — too **small**,
     so the validator sends while the paper's joining protocol keeps it silent, and
     Constraint (1) cannot bound the voter set. Fix shape: `WakePrecedesTick` — a tick of a
     validator in its transition round (`p ∉ awake(time - 1)`) must be preceded by its wake
     event at that same time.
  2. *Time can skip values.* `advance` sets time to anything, and the wake action is
     enabled only while time equals the transition round — skip it and the wake can never
     fire at all. Fix shape: `TimeStepwise` (`x[i+1].time = x[i].time ∨ = x[i].time + 1`),
     the old framework design's increment-by-one, now as an à la carte assumption. With
     both, plus `Diligent` (which forces a tick in the transition round, triggering 1), the
     state's `activeAt` equals `activationRound` of the latest wake at every tick, and the
     containment argument closes; the no-transition case lands in `Active` directly.
  The alternative — assuming the state–schedule correspondence outright — would assert a
  fact about protocol state rather than constrain the scheduler, the wrong kind of
  assumption. Both fixes live in `Examples/StsMultisetLog/majorum/Assumptions.lean` when approved.
- **File convention in `Examples/StsMultisetLog/majorum/` (user instruction, 2026-08-03):
  `Lemmas.lean` holds one theorem per numbered lemma of the paper, and nothing else.**
  Helper theorems moved out: the old `Lemmas.lean` (filters, majorities, `MFC`) is now
  `Mfc.lean`, and the old `Lemma2.lean` (provenance, activation, the containment) is
  `Provenance.lean` — its former name was misleading anyway, since it held Lemma 2's
  *supporting* material and the eventual `lemma2` theorem belongs in `Lemmas.lean`. Entries
  above referring to those files by their old names describe the same content. The paper's
  *theorems* remain in `Theorems.lean` as `Prop`-valued statements.
- **Spec/proof separation audited** (user instruction, 2026-08-03): every definition in
  `Algorithm5.lean` and `Components.lean` must be used by the protocol specification itself,
  not only by proofs. Result: one violation, `validFinVote` — dead in both directions —
  now deleted; it re-enters with the deferred certificate check (item 4), whose design will
  fix its exact shape. Everything else, including the proof-flavoured vote filters and
  `Majority`, is on `algorithm5`'s dependency chain through `mfc`, which the handler calls.
- **Lemma 2's containment is proved** (2026-08-03, `mem_active_of_honest_vote`): an honest
  slot-`t` voter is in `Active(t)`. The two approved assumptions live in the framework
  (`TimeStepwise`, `WakePrecedesTick`); on top of them `wake_sets_activeAt` (a wake writes
  the activation round of its own real-time round) and `activeAt_lb_step` (no step lowers
  `activeAt` below a bound that also sits below the current round's activation round; the
  per-configuration clock fact threaded through the eliminator's motive) give
  trustworthiness, and the assembly is a dichotomy over the window: awake throughout, or a
  latest transition inside it — whose activation round lands after `voting(t)`,
  contradicting the gate the vote certifies. Import note: `Finset.max'` needs
  `Mathlib.Data.Finset.Max`, and `ring`/`push_neg` are not in this import universe
  (`push_cast`/`omega`/`exact_mod_cast` are) — proofs here are structured around omega with
  nonlinear subterms treated as atoms.
  **What now remains of the propose-round half needs no new assumptions**: delivery of the
  slot-`t` votes into `V_i` by `propose(t+1)` (plain `Synchrony`), filter survival (the
  provenance consequences feed `votesFor`), and the final assembly through
  `voters_lt_two_mul_honest` and `le_mfc_of_majority`.
- **The propose-round half of Lemma 2 is proved** (2026-08-03,
  `Provenance.le_mfc_at_propose`). `ActiveVotesExtend` renders the lemma's hypothesis over
  the log ("every validator active in slot `t` sent, by `voting(t)`, a slot-`t` vote
  extending `ch`"); the proof assembles delivery (`Synchrony 0 Δ` — the GA analysis is
  synchronous, `Q.gst = 0` a hypothesis), filter survival (each honest active's vote passes
  `FIL_eq` by `honest_vote_unique`, `FIL_lmd` by the slot-time bound, expiry trivially), the
  containment (each voter the view shows is corrupt at `voting(t+1)` or active in slot `t`
  via `mem_active_of_honest_vote`), and Constraint (1) instantiated at slot `t+1` — which is
  *exactly* the paper's Equation-(1) step, `Sleepiness`'s indexing matching with no
  adjustment. Conclusion: `∀ b ⪯ ch, mfc V_i V_i b (t+1) ⪰ ch` for any `v_i ∈ H_{vote(t+1)}`
  at `propose(t+1)`.
  Lean notes from the assembly: hypotheses produced by `rintro` on filter predicates carry
  the *unreduced* structure-literal projection (`{sender := p, …}.msg`) while freshly
  elaborated terms carry the reduced one — `omega` then sees two distinct atoms for the same
  value and fails with a counterexample that looks impossible; `dsimp only` refuses to
  bridge them ("no progress"), but a plain type ascription transports across the defeq
  (`have hlt' : t < s' := hlt`). And `rw`'s closing `rfl` runs at reducible transparency
  only, so `rw [hm']` on a goal ending in a `match`-defined function needs an explicit
  `exact rfl` after it.
- **Course correction (user catch, 2026-08-03): Lemma 2 is about Algorithm 2, not
  Algorithm 5.** "In Appendix A, we prove that Algorithm 2 satisfies Reorg Resilience
  (Theorem 1) and Dynamic Availability (Theorem 2). We first establish that … (Lemma 2)."
  Everything Lemma-2-related so far was proved against `protocol C Q` — Algorithm 5's
  handler. Consequences:
  - **The mistake shrinks the problem.** Algorithm 2 has no finality component: `chfrozen`'s
    write paths are `fastconfirmsimple` at merge (provable comparable-to-`ch` by
    2n/3-quorum overlap with the honest slot-`t` voters) and the proposal's `chC` on lines
    33–36 (`if valid(…) ∧ chfrozen ⪯ chC then chfrozen ← chC`) — conditional on a certificate, but
    with **no `GJ`/justified-checkpoint layer at all**. The hardest remaining piece of the
    old plan drops off Lemma 2's critical path entirely.
  - **The machinery transfers, the instantiation does not.** `Mfc.lean` is
    protocol-independent (reusable as-is). The Provenance layer (handler-send shape,
    emission analysis, vote provenance, activation trustworthiness, `le_mfc_at_propose`) is
    per-handler and must be re-instantiated for Algorithm 2's — structurally the same
    proofs against a simpler handler.
  - **The Algorithm-5 work is not wasted**: Algorithm 5 *is* Majorum, needed for the
    Theorems; and Appendix C's lifting ("honest validators send identical messages in both
    protocols except for the finality component") is the eventual bridge from Algorithm 2's
    lemmas to Algorithm 5.
  - **The certificate check enters as part of writing Algorithm 2 fresh**, not as a change
    to an approved model. Design decision to flag: a certificate's entries cannot be taken
    at face value (a `QCert` payload is unauthenticated data — the adversary can fabricate
    one), so `ValidProposal2` checks the certified votes **against the receiver's view**:
    `≥ 2n/3` distinct signers, each entry's chain extending `chC`, slot `t' − 1`, and the
    corresponding vote message present in `V`. That is the signature-idealized reading of
    "verify the QC": a vote you can vouch for is one you hold, and gossip ("a validator
    receiving a proposal also gossips the votes contained") makes carried votes held.
    Genesis `chC` needs no certificate (`fastconfirmsimple` returns `(genesis, ∅)`).
  - Algorithm 2 reuses `Msg` and `Checkpoint` with the paper's own "·" placeholder in
    the fin-vote fields — Algorithm 2's vote is literally `[vote, ch, ·, t, v]` — which
    keeps every Components function and, later, the Appendix-C message correspondence,
    literal (up to the blank fields). The placeholder went through three designs in one
    day (2026-08-03): a fixed `dotCk := ⟨[], 0⟩`, then a parameter `dot` of `protocol2`
    (parametricity = "any value"), and finally — the user's preference —
    **nondeterminism**: `protocol2`'s tick step is `∃ dot, res = handler2 … dot …`, a
    fresh filler chosen at every tick (the framework's `step` being a relation exists
    for exactly this), and `ValidProposal2` accepts certified votes with any filler
    (`∃ src tgt, … ∈ V`). Consequences: `ValidProposal2`/`processProposals2` need no
    filler at all, so the fork-choice value is manifestly filler-independent;
    `ActiveVotesExtend2` went back to the `∃ src tgt` shape; and vote uniqueness can no
    longer compare two handler runs (different ticks choose different fillers) — it
    routes through `tick_sends_subsingleton` ("one tick contributes at most one message
    to the log", from the multiset log delta), with `vote_provenance2` now returning the
    vote's membership in its tick's log delta. `tick_state`/`tick_emits` merged into
    `tick_effect` (one existential shared by the state equation and the emission
    closure, so facts about the same tick agree on the filler). Own state (`NodeState2`: `chi`, `vFrozen`, `chFrozen`,
    `activeAt`); fully concrete handler (no `Components` record — the paper defines every
    function Algorithm 2 uses, and they are all in `Components.lean` already).
- **Provenance layer re-instantiated for Algorithm 2** (2026-08-03,
  `Provenance2.lean`): `protocol2_step_*`, `mem_handler2_send`,
  `handler2_send_subsingleton`, `emitted_step2`, `vote_provenance2`,
  `voting_le_of_vote_mem2`, `honest_vote_unique2`, the `activeAt` machinery
  (`processProposals2_activeAt`, `handler2_activeAt`, `wake_sets_activeAt2`,
  `activeAt_lb_step2`), `mem_active_of_honest_vote2`, and **`le_mfc_at_propose2` — the
  propose-round half of Lemma 2, proved for Algorithm 2's protocol** under
  `ActiveVotesExtend2` (which pins the finality fields to `dotCk`, all an honest
  Algorithm-2 vote can carry). The generic pieces (`time_le_of_le`,
  `emitted_of_mem_sent`, `exists_time_eq`) were generalized in `Provenance.lean` over the
  protocol/state type rather than duplicated; everything handler-shaped is a fresh copy —
  same scripts, simpler handler. Lean notes from the port, both caused by Algorithm 2
  pinning the certificate type concretely (`QCert Node Tx`) where the Algorithm-5 layer
  keeps `QC` an atomic variable:
  - `DecidableEq (SignedMsg Node (Msg (Chain Tx) (QCert Node Tx)))` **fails to
    synthesize with the instance found**: the derivation tree has term size 212, over
    `synthInstance.maxSize`'s default 128, and is rejected on size alone. The trace shows
    `[Meta.synthInstance.answer] ❌` *after* every subgoal succeeds. Fix:
    `set_option synthInstance.maxSize 400` (file level in `Provenance2.lean`). This is
    also why `Algorithm2.lean` needs `open Classical` — there the classical fallback
    covers it (any `Decidable` at low priority), which is fine for definitions but would
    put choice-based instances into *statements*, so the proof file raises the bound
    instead.
  - `le_mfc_at_propose2` needs `set_option maxHeartbeats 1000000`: the closing `omega`
    and the `Majority` unfolding re-check defeq under the full instance trees.
  - `set_option … in` (like `omit … in`) must precede the declaration's docstring;
    between docstring and `theorem` it is a parse error.
- **Lemma 2 is proved** (2026-08-03, for Algorithm 2): `Lemmas.lean` has `lemma2 :
  SettingGA Q S n x → ActiveVotesExtend2 x t ch → ActiveVotesExtend2 x (t+1) ch` — the
  paper's operative clause, the exact shape Lemma 3's induction will consume — resting on
  `Provenance2.le_mfc_at_propose2` and `Provenance2.le_mfc_at_vote2` (the paper's two
  `MFC ⪰ ch` conclusions). **`Assumptions.SettingGA`** (added at the user's request,
  2026-08-03) bundles the Appendix-A setting for reuse by Lemmas 3–5 and Theorems 1–2:
  `Wellformed`, `TimeStepwise`, `WakePrecedesTick`, `OneTickPerReading`,
  `Synchronous` (Δ + relay from round 0), `Sleepiness`, `Resilience`, `Q.gst = 0`. It is
  deliberately the *full* setting, not Lemma 2's minimal row — `Relay`/`AwakeHonest` ride
  along for Lemma 4's gossip argument — and Theorem 5 (accountable safety, `f ∈ [0,n]`,
  no synchrony) must keep citing groups à la carte rather than take it. The Provenance2
  helpers keep loose hypotheses; only the `Lemmas.lean` statements take the bundle.
- **Proposals must be signed by their slot's proposer** (user decision, 2026-08-04,
  option 1 of the discussion): `ValidProposal2` gains `proposer` and the conjunct
  `sm.sender = proposer t'`; `proposedNow` in the handler (and its deterministic core)
  gains `sm.sender == proposer slot`. **Lemma 4 is false without both**: (line 23) a
  corrupt validator's fabricated slot-`t` chain — blocks are `⟨slot, txs⟩`, freely
  fabricable — can be voted for instead of the honest proposer's; (lines 33–36) a
  certificate-backed `chC'` whose quorum the adversary delivers to the victim but
  withholds from the proposer can outgrow `chC_p` and lift `chfrozen` above anything
  bounded by `chp`. The paper's own base-case equalities (`chfrozen,vote(t) = chC_p`)
  need the check, but its `valid([propose, …])` is **never defined** (only checkpoint-link
  validity is) — third authors'-note finding. Structural signing makes the check sound:
  the proposer's sender field cannot be forged, and relayed messages keep their signer.
  Lemmas 2–3 survived with a one-conjunct adjustment to the certificate path.
- **Lemma 4 is proved** (2026-08-04): `Lemmas.lean` has `lemma4 : SettingGA → 1 ≤ t →
  (⟨vp, propose chp chC qc ck t⟩ ∈ log, vp honest at its index and at voting(t)) →
  ∀ t' ≥ t, ActiveVotesExtend2 x t' chp`. `vp = proposer t` is *derived* by provenance,
  not assumed. Induction with `lemma2` as step; the base case
  (`Provenance2.activeVotesExtend_of_propose`, the largest single proof in the
  development) shows every slot-`t` active's vote *is* `chp`:
  - **propose provenance** (`propose_provenance2` + `handler2_propose_send`): the
    proposal came from `vp`'s `4Δt` tick, `chp = Extend(MFC(V_p, V_p, chC, t), t)`,
    `chC`/`qc` are that tick's `fastconfirmsimple` outputs.
  - **`vp`'s own proposal is `ValidProposal2` in every vote view**: the certificate's
    votes travel from `V_p` by synchrony (`fastConfirmSimple_snd_spec` gives the cert's
    content; `fastConfirmSimple_none_fst` covers the genesis case).
  - **fork-choice bounded by `chp`** via `mfc_base_or_majority`: the frozen chain is the
    merge value (`⪯ chC` by the quorum-transfer-into-`V_p` argument) or — sender check +
    one-tick-per-reading + `tick_sends_subsingleton` — `vp`'s own `chC`; a majority
    transfers into `(V_p, V_p)` by `majority_transfer` (numerator from the frozen view
    by synchrony, denominator back by synchrony, `filEq` survival by **`Relay`'s view
    inclusion** — first use of `Relay`; the paper's "Graded Delivery"), where
    `le_mfc_of_majority` over base `chC` (`processProposals2_chFrozen_lb` + comparability
    give `chC ⪯` the processed frozen chain) bounds it by `MFC_p ⪯ chp`
    (`chainLe_extend`).
  - **the vote is pinned**: `voteChoice`/`handler2_vote_send_eq` expose the sent chain;
    the proposal passes the filter (`proposedAt_extend`, the bound above), `findSome?`
    cannot miss it (`List.findSome?_eq_none_iff`), and any hit is a sender-checked
    slot-`t` proposal, hence `vp`'s one message (provenance + `OneTickPerReading` +
    `tick_sends_subsingleton`) — the vote is `chp`, `chainLe_refl` closes.
  Lean notes: `split_ifs at h` can close branches (and whole goals) by itself when `h`
  becomes absurd — don't script bullets for branches that may not exist; `rw [if_pos …]
  at h` on a beta/iota-stuck hypothesis needs `dsimp only at h` first; `injection` keeps
  auto-substituting (dropped `exact h1` again); an anonymous-constructor proof against a
  `match`-defined `Prop` (`ValidProposal2`) elaborates fine via whnf — no `show` needed,
  which sidesteps spelling the reduct.
- **Lemma 3 is proved** (2026-08-04): `Lemmas.lean` has `lemma3 : SettingGA → 1 ≤ t →
  (fast confirmation of ch in slot t) → ∀ t' > t, ActiveVotesExtend2 x t' ch`. The
  hypothesis renders the paper's "an honest validator fast confirms ch in slot t" as
  `∃ i w cert, x[i].time = fconf(t) ∧ fastConfirmSimple (card Node) (x[i][w].view) t =
  (ch, some cert)` — *without* the confirmer's honesty, which this model does not need
  (views are sound: everything in any view is in the log), so the statement is only
  stronger. Induction via `Nat.le_induction`; the step is `lemma2`; the base case
  (`Provenance2.activeVotesExtend_of_fastconfirm`) needs **no majority argument**:
  - the confirming quorum reaches every slot-`t+1` active's `merge(t)` view by
    `Synchrony` (`fconf(t) + Δ = merge(t)`), so its frozen fast-confirmation is at least
    as long as `ch` (`fastConfirmSimple_length_ge` — the fold returns the longest
    quorum-supported candidate) and comparable with it (`supported_comparable`: two
    `2n/3` quorums of at most `n = Fintype.card Node` validators share an honest member
    whose unique slot-`t` vote extends both chains — the paper's "conflicting quorum
    certificates cannot form in the same slot");
  - `processProposals2_chFrozen_mono`: the lines 33–36 condition makes every overwrite an
    *extension*, so `chFrozen` rides monotonically into the vote tick;
  - `base_le_mfc` finishes: the fork-choice always extends its base.
  Sharing with Lemma 2 was factored out on the way: `frozen_at_vote_tick` (the merge
  tick + persistence block, extracted from `le_mfc_at_vote2`) and
  `activeVotesExtend_of_le_mfc` (the vote-production machinery — tick exists, joining
  check open, sent chain extends the fork-choice — extracted from `lemma2`, which is now
  a three-line composition). New view-local pieces: `Mfc.mem_candidates_of_extends`,
  `foldl_longest_le_init`/`foldl_longest_length_ge`. The `Fintype.card Node ≤ n`
  hypothesis threads the structural validator count into the generic-`n` helpers.
  Next: Lemma 4 (honest proposer's chain, same induction shape with a propose-round base
  case), then Lemma 5 and Theorems 1–2.
- **Paper-style vote notation** (2026-08-04, user request): `Algorithm5.lean` defines,
  next to `Msg`, the scoped notation `⟪vote, e, src, tgt, t, p⟫` for the signed vote
  `⟨p, Msg.vote e src tgt t⟩` — the paper's `[vote, ch, src → tgt, t, vᵢ]` with the
  signer last, where the paper writes the signature. Pure sugar (same term, prints back
  the same way, `rfl` projections unaffected); 26 ascribed literals across
  `Provenance.lean`/`Provenance2.lean`/`Lemmas.lean` replaced. Two facts learned on the
  way: literal `<`/`>` can't be notation brackets (comparison operators), and the
  ascriptions were mostly unnecessary anyway — anonymous constructors elaborate bare in
  `∈`-positions, since the container's type reaches them through the `Membership`
  instance.
- **2.2's discharge: pieces in place, assembly next** (2026-08-05).
  `agree_propose_at_tick` (2.1 discharged, committed) is the template. For
  `agree_vote_at_tick`, `h_b5`'s cases: *seed* — strengthen
  `frozen_at_vote_tick`(+`5`)'s statements with the merge tick's **label** (their
  proofs already have it) so the two runs' merge indices identify via
  `OneTickPerReading`; fcs-branch seeds are then congruence-equal and ride
  `processProposals2_chFrozen_mono` under the x2 base; GJ-branch seeds are justified
  → descent. *Certificate* — case on the proposal's origin: pure injections keep
  `τ = id` (needs a small τ-id-for-never-tick-emitted lemma via `tau_write`); honest
  emissions carry fcs-branch fields equal by congruence at the emitting tick (or
  GJ-branch → justified → descent); either way the x2-side message carries the same
  `(chC, cert)`, **`validProposal2_of_cert`** (proved: the cert clause is
  skeleton-shaped, fin-vote fields existential) makes it x2-valid, and
  `processProposals2_chFrozen_lb` + `supported_comparable` on the y-blocker close
  `chC ⪯ b2 ⪯ O2`. *Justified* — descent (as in 2.1). Then `b2 ⪯ b5` via the
  fold-max (`chainLe_foldl_of_comparable`) with the value-set inclusion, and
  `mfc_vote_agree` closes 2.2.
- **2.2's first cross-bound is proved: `b5_le_voteMfc`** (2026-08-06). Algorithm 5's
  processed frozen chain sits below the simulated run's vote-round fork choice, by the
  three provenance cases of `processProposals_chFrozen` (plus Algorithm 5's extra
  justified validity rung, which the same descent covers):
  `chFrozen5_le_voteMfc` (seed), `cert_le_voteMfc` (certificate),
  `justified_le_voteMfc` (justified). New machinery, in `MfcEquiv.lean`:
  `support_of_cert`/`support_mono` (a certificate's signers support its chain; support
  grows with the view), `frozen2_supported_or_nil` (the Algorithm-2 base is genesis or
  quorum-supported — the merge seed through `fastConfirmSimple_fst_cases` and
  `view_mono_le`, a proposal write through the Algorithm-2 certificate check),
  `tick_send_mem5`, `tau_emitted_image` (the table's value at an honest emission *is*
  the simulated tick's send — the `none` branch is impossible by `sends_align`),
  `cert_counterpart` (the origin dichotomy: a pure injection is its own image; an honest
  emission's image carries `fastconfirmsimple`'s `(chC, cert)`, congruence-equal to
  Algorithm 5's because a certificate rules out the `GJ` branch), `cert_votes_transfer`.
  The y-blocker of `processProposals2_chFrozen_lb` is killed by comparability, not by
  identifying the bases: both are quorum-supported at slot `s1`, and the wrong
  orientation contradicts the blocker.
- **Algorithm 5's proposal fold is a maximum under a common bound** (2026-08-06).
  `processProposals_bounded`: with every write value below one chain `O` (certificate
  writes by hypothesis `hval`, justified-chain writes by `hjust`), the processed frozen
  chain stays below `O`, never descends below the seed, **and dominates every valid
  slot-`t` proposal's chain**. The last conclusion is 2.2's second cross-bound engine:
  the paper's justified-chain reset (`chfrozen ← GJ_p.ch` when the accumulator does not
  extend it) moves the accumulator *sideways* in general, and only comparability — which
  the common bound supplies — makes it move up. Lean shape: two abstract fold lemmas
  (`foldl_bounded_mono`, `foldl_ge_of_fires`) combined by `foldl_bounded_all` over a
  write-offer predicate `P`, so the concrete condition tree is never restated — restating it
  fails: a separately elaborated copy of the fold's `match` is *not* accepted as defeq by
  `exact` (matchers compiled per elaboration), so the step obligations must be proved
  inline on the goal `refine` produces. Also: `simp only [hmsg]` normalizes the condition's
  `t = t` to `True`, breaking later `by_cases`/`rw [if_pos]` — destructure the message and
  `subst` instead.
- **The reverse counterpart: `valid2_counterpart5`** (2026-08-06). Every Algorithm-2
  proposal write has an Algorithm-5 write at or above it: for a valid slot-`s1+1`
  proposal in the *simulated* view, the original view holds a valid proposal whose chain
  extends it. By origin — a pure injection is its own counterpart (`ValidProposal2`'s
  certificate clause *is* `ValidProposal5`'s, carried by `cert_votes_transfer` through
  `ViewCorr.symm`); an honest emission's counterpart is the message the tick sent, whose
  `chC` is `fastconfirm`'s: the `fastconfirmsimple` branch gives the same chain *and*
  certificate by congruence, the `GJ` branch gives the greatest justified chain, which the
  branch condition `GJ.ch ⋠ fcs.1` puts strictly *above* the simulated one once both sit under
  the common bound. The `GJ` branch's validity needs the proposer's evidence in the
  voter's view: honest `Relay` at exactly `+Δ` (propose reading to vote reading) plus
  `justifiedIn_mono`. Lean notes: `injection` on a propose equation auto-substitutes and
  scrambles later scripts — use `rw [Msg.propose.injEq] at h` + `obtain`; and prove each
  component as a `have` *before* the final anonymous constructor, since `by` blocks inside
  a `refine` tuple elaborate against goals whose metavariables are not yet fixed.
- **Condition 2.2 is discharged: `agree_vote_at_tick`** (2026-08-06). At every vote
  reading with an open joining check, the two vote-round fork choices agree. Assembly:
  `mfc_vote_agree` over the frozen-view correspondence (`frozen_viewCorr`) and the
  current-view one, with the two bases cross-bounded by
  `processProposals5_at_vote_tick` (`h_b5`) and `b2_le_b5`. Two generality points cost
  most of the work and are worth remembering: 2.2 quantifies over **every** vote reading,
  so slot 0 needs its own (genesis) branch in every lemma of the chain
  (`chFrozen_early5`/`_early2`); and 2.2 hypothesizes only the **joining check**, weaker
  than `Active` — bridged by **`active_of_open_join5`**, factored out of
  `mem_active_of_honest_vote` (whose vote enters only via `vote_provenance`), which turns
  an open check at a vote tick into `Active`-membership for slots ≥ 1.
- **Every statement and citation checked against the paper** (2026-08-06). Part of
  this session had been reading the working copy (the paper's own source),
  which is *not* the source of record: only
  arXiv:2601.03862v1 is. No tool in this environment reads it
  (`pdftotext`, `pdftoppm`, `pypdf` all absent), so the scratchpad now holds a small
  extractor: inflate each content stream, concatenate the per-glyph `TJ` strings with no
  separator, decode octal escapes, insert a space on kerns `≤ -180`, map the CM ligature
  slots (`0x0b–0x0f` = ff/fi/fl/ffi/ffl) and read the symbol font by code —
  `≤` = `<14>`, `≥` = `<15>`, `⪯` = `<16>`, `⪰` = `<17>`. Printed page numbers come from
  the footer digits at each page's last stream. Results (v1): Definitions 3–7 p.4–5,
  Definition 8 p.18, Definition 9 p.19; Lemmas 1–2 p.14, 3–4 p.15, 5 p.16, 6–8 p.17,
  9 p.18, 10 p.19, 11–13 p.21, 14–15 p.22, 16–17 p.23, 18 p.24; Theorems 1 p.16,
  2 p.17, 3 p.21, 4 p.22, 5 p.23, 6 p.24, 7 p.25; Algorithm 2 p.8, Algorithm 5 p.11.
  Eleven citations in the tree were off by one page (Lemma 2 said p.8 — Algorithm 2's
  page, not the lemma's) and are fixed. The statements themselves all match, including
  the ones this session added: Lemma 14's `|H_vote(t)| ≥ 2n/3` and conclusion at
  `fconf(t)`; Theorem 3 against **Definition 5**, whose "does not conflict" justifies
  rendering reorg resilience as comparability rather than inclusion; Theorem 5's
  `f ∈ [0, n]`; Lemma 16's `⪰`; Lemma 18's `GJ^{propose(t)}_p.c < t - 1`; Definition 7's
  `chFin ⪯ chAva`. Two divergences to keep in mind, both ours and both *stronger* than
  the paper: every Algorithm-5 result is stated under `SettingGA`, which fixes
  `GST = 0` and `f < n/3`, where the paper's Appendix C.2 assumes only
  `propose(t) ≥ GST + Δ` (unavoidable wherever the argument routes through Lemma 10,
  gratuitous for Lemmas 15–16, whose proofs use neither); and Definition 9's condition
  2.3/2.4 witness is any validator's `chi` at an earlier time, where the paper's is an
  honest validator's at a vote reading.
- **Spec change: finalization counts fin-votes by source** (user decision, 2026-08-07).
  `FinalizedIn C` is now `JustifiedIn n V C ∧ 2n ≤ 3 * (sourceVoters V C (C.c + 1)).card`,
  where `sourceVoters V C c` counts validators whose fin-vote runs *out of* `C` into a target
  of slot `c` — each with whatever target it chose. The paper writes finalization as a
  supermajority *link*, which forces one common target and makes finality hostage to
  agreement among the next slot's available chains; that is the whole content of the
  thirteenth and fourteenth findings, and counting sources is what the slashing conditions
  actually support. `linkVoters` is untouched and remains what *justification* uses, since
  there it is the target that gets justified.
  * **Appendix B survived with one addition**: `slash_of_source_link`, whose slashing witness
    is parametric in each voter's own target. It costs nothing because E1 and E2 read only the
    target's *slot* and the source pair, so Lemma 8's two evidence sites are unchanged in
    substance, and Lemma 9 and Theorem 5 with them. Lean note: the finalization side's slot
    argument arrives as `⟨chf, cf⟩.c + 1`, an unreduced projection, so `omega` needs an
    ascribed `have hC2 : C2.c = cf + 1 := hC2c` before it can see the arithmetic — the same
    trap appears wherever a `Checkpoint` literal's field meets `omega`.
  * `linkVoters_subset_sourceVoters` is why a link still finalizes its source, which is how
    the already-justified branch of `finalized_chp_next5` now discharges its quorum.
  * **The statements are relaxed, which was the point of the change** (2026-08-07).
    `lemma18`'s finalization half and `theorem6_liveness_of_low` /
    `theorem6_liveness_txpool_of_low` no longer carry an honest proposer at `t+1`: Lemma 18
    holds with **one** honest proposer, at slot `t`, exactly as the paper states it, and
    Theorem 6's `GJ_p.c < t − 1` branch needs only slot `t`'s. New lemmas, all in
    `Analysis/Proofs/Finality5.lean`:
    - `slotPinned_chp_next5` — `SlotPinned x5 (t+1) chp ⟨chp, t+1⟩` from slot `t` alone.
      Taking `chp` itself as the slot's chain makes the structure's chain field
      `chainLe_refl`, and that is the whole trick that removes the slot-`(t+1)` proposal: the
      field is only ever read as a lower bound. `SlotPinned.self` performs the same weakening
      on an instance that did come from a proposal, which is how Case 1 now feeds the shared
      lemmas.
    - `vote_tgt_chAva5` — an honest fin-vote whose source sits at slot `s − 1` targets the
      sender's own `chAva` at its vote tick. It reads the extension branch of
      `handler_vote_fin_content` back off the *message*, so callers never have to identify the
      handler's `chAva` term syntactically.
    - `fastConfirm_ge_chp_next5` / `chAva_ge_chp_at_fconf_next5` — the fast-confirm write
      keeps the longer of the previous chain and the reading, and the reading is above `chp`
      because `GJ = (chp, t+1)` there; so **both** branches of the write land above `chp`, and
      nothing has to be known about the previous chain. That is what made this cheap. The
      earlier route, `chAva_eq_chp_at_fconf5`, proved the sharper `chAva = chp'` and for that
      needed the slot-`(t+1)` proposal.
    - `finvote_source_next25` — every slot-`(t+2)` active's fin-vote runs out of `(chp, t+1)`
      into a target of its own, above `chp` by the two lemmas above plus `chAva_mono`; or its
      view already justified a slot-`(t+2)` checkpoint, which is the escape the caller
      resolves through link validity.
    `finalized_chp_next5`, `chp_le_chFin_at_vote5`, `chp_le_chFin5` and `chFin_txpool5` now
    take `SlotPinned x5 (t+1) chp ⟨chp, t+1⟩` and nothing else about slots `t`/`t+1`, so
    Lemma 18's regime and Case 1 meet at the single hypothesis they share.
    Lean notes: `cases` on `JustifiedIn n V C` with `C` a *variable* no longer eliminates
    `genesis` by unification — the old proof had the literal `⟨chp', t+2⟩` there — so that
    branch has to be closed from `C.c = t+2`; and `mem_sourceVoters_of_vote` concludes
    membership in `sourceVoters V C tgt.c`, so the caller rewrites with the target's slot
    instead of passing it.
- **Lemma 18 is proved, in full** (2026-08-07), and with it Theorem 6's liveness half in the
  regime Lemma 18 covers. The chain of lemmas, in `Analysis/Proofs/Finality5.lean`:
  `SlotPinned` (what a slot's development needs of its proposal: a checkpoint `T` at that
  slot, chain below the proposal, justified from `fconf(s)` on, target of every honest
  slot-`s` fin-vote) → `slotPinned_of_low` (slot `t`'s instance, from re-justification) →
  `gj_eq_window5` → `fastConfirm_eq_chp5` → `chAva_eq_chp_at_fconf5` →
  `vote_tick_bounds_chp5` → `chAva_and_justified_le_chp5` (the paired induction) →
  `finvote_target_eq_chp5` (the tick-order induction on targets) → `finvote_of_active5_next`
  → `justified_chp_next5` → `slotPinned_next5` (slot `t+1`'s instance, from slot `t`'s
  conclusion) → `finalized_chp_next5` → `chp_le_chFin_at_vote5` → `chp_le_chFin5`. Faces:
  `lemma17`, `lemma18`, `theorem6_liveness_of_low`.
  Three things worth keeping:
  * **the `SlotPinned` refactor is what made slot `t+1` reachable.** `GJ_p.c < t - 1` is false
    at `t+1` — `(GJ_p.ch, t)` is justified by `propose(t+1)` — so the development had to be
    re-expressed over what it actually uses. Everything downstream of `gj_eq_window5` now
    takes the structure instead of the re-justification hypothesis.
  * **two inductions, both in tick order, for the same reason.** A view at exactly
    `voting(s+1)` may already hold slot-`(s+1)` fin-votes from validators that ticked first,
    so `no_justified_above_slot` (strict `<`) does not apply there. The first induction pairs
    the available-chain bound with the justified-chain bound (each feeds the other one index
    apart); the second pins the fin-vote targets.
  * **the source classification carries the value, not just its consequence.**
    `finvote_of_active5_next`'s second disjunct names the source `(chp, t+1)`, and link
    validity (`C.c < C'.c`) is what then identifies a supermajority link's source — which is
    how finalization gets its link in the case where the target checkpoint was already
    justified.
  Lean notes from this pass: `rw` rewrites *one* instance of an `if`-lemma, so a handler goal
  with both a `send` and a `state` tree needs `simp only` instead; `(setClock vi τ c)[vi].view
  = c[vi].view` needs a closing `rfl` after `simp only [setClock_getElem, if_true]`;
  `Checkpoint` has no `ext`, so `congr 1` does the record split; `cases` on `JustifiedIn`
  whose index is a local variable binds one fewer name than when it is a parameter
  (`| link hjust hlk`, source implicit); and `greatestBySlot_c_max` will not unify a goal
  stated as `t + 1 ≤ …` with `?C.c ≤ …`, so the membership must be given first and the
  instance ascribed.
  **What remains in C.2** (as of 2026-08-08): nothing that the paper states. Theorems 5, 6
  (all three branches, with their transaction-pool clauses) and 7 are proved, as are Lemmas
  15–18. What is *optional*: a single face for Theorem 6's liveness half in place of the three
  branch faces, which would have to state the weakest of their round bounds (Case 2's
  `fconf(t+4)`; see the fourteenth finding).
- **Definition 2 is over the paper's `H_r`, and majorum now says so** (user decision,
  2026-08-08: keep the correction majorum-local). Checked against the paper, §2.2 p.5:
  "…any rounds `r ≥ Tsec` and `r_i ≥ r + Tconf`, any transaction `tx` in the transaction pool
  at time `r`, and any validator `v_i` **active** in round `r_i`, `tx ∈ Ch^{r_i}_i`." The
  framework's `Live` quantifies over validators *awake* at the later round — a larger set, so
  a stronger claim, and one that is **false** of this model: a validator that has just woken
  has stepped nowhere (`init` puts `chAva`/`chFin` at genesis, and both are written only at
  the node's own ticks, the vote-round write behind `activeAt ≤ r`). The framework's docstring
  already flagged the divergence and prescribed "its own participation predicate"; that is
  now `LiveActive` in `Spec/Security.lean`, taking `active : Node → Time → Prop` exactly as
  `ReorgResilient` takes `proposedBy`/`proposing`, instantiated at `ActiveAtRound Q S`.
  * **No honesty conjunct is needed.** §2.1: "Adversarial validators are always awake. Thus,
    awake, asleep, and active apply only to honest validators", and `H_r` is "the set of
    active validators at round `r`". The model says the same by keeping `S.awake` disjoint
    from `S.adv` (`Wellformed`), so activity already implies honesty.
  * **Definition 7's middle conjunct now carries two time bounds.** The paper: `chFin` is
    "always safe and live after `max(GST, GAT) + O(Δ)`" — safety from 0, liveness after the
    bound — where the old rendering imposed the one bound on both through `Secure`. Ours is
    stronger on the safety half and matches the paper.
  * `SecureActive`, `DynamicallyAvailable`, `SecureEbbAndFlow`, `ThmDynamicAvailability{GA,FFG}`,
    `ThmLiveness` and `ThmEbbAndFlow` all take `active` now. `ThmLiveness` had `x.Honest`
    where the paper writes `v_i ∈ H_r`; that was the same mistake one level up.
  * **What this bought immediately**: `theorem4_dynamicallyAvailable` — Definition 4 for
    `chainava`, `SecureActive` from time 0 with `Tconf = slotLength·2κ + Δ + 1`, proved from
    `theorem4`'s two halves. The `+1` is the model's strict bound at the `+2κ` vote round.
    So Definition 7's first and third conjuncts and the safety half of the second are proved;
    only its liveness half is open, and that is issue 2 below.
  Lean note: `ring` is not available in `Analysis/Theorems.lean` (Mathlib's tactic is not
  imported there) — `rw [Nat.mul_add, Nat.add_assoc]` does that job.
- **The statement files are back to one-line faces** (2026-08-08). `Analysis/Lemmas.lean` and
  `Analysis/Theorems.lean` exist to be *scanned* against the paper, so every face is a
  delegation, never a proof. Two things had drifted and are now fixed: `theorem7` and
  `theorem4_dynamicallyAvailable` (their assemblies moved to the new
  `Analysis/Proofs/EbbAndFlow5.lean`, along with `HonestProposerPairs`), and Theorem 6's Case-2
  pair (`Finality5.chp_le_chFin_case2_5`, `Finality5.chFin_txpool_case2_5`). `lemma18`'s face
  had an inline `by` block computing the slot-`(t+1)` `GAT` bound, which is exactly
  `Finality5.gat_le_voting_succ5 hgat`.
  Also closed: **`ThmDynamicAvailabilityFFG`** — `theorem4_dynamicallyAvailable` is now stated
  *through* it rather than through `DynamicallyAvailable` directly, so the abstract rendering
  has an instance. What is left uninstantiated, and why:
  * `ThmReorgResilienceGA` / `ThmReorgResilienceFFG` — `ReorgResilient` asks for a proposer
    honest at `proposing(t)`, the *propose* round; `theorem1`/`theorem3` need it honest at
    `voting(t)` as well, which is what pins the slot's votes. Instantiating them faithfully
    means proving reorg resilience from honesty-at-propose alone, not plumbing.
  * `ThmDynamicAvailabilityGA` — quantifies over executions given four assumptions, where
    `theorem2` needs `SettingGA`'s full bundle (`TimeStepwise`, `WakePrecedesTick`,
    `OneTickPerReading`, `gstZero` besides). Closing it means deciding whether the paper's GA
    section fixes those, which is the open question its docstring already records.
  * `ThmLiveness` — **not provable as stated**: it assumes one honest proposal
    (`proposedBy t chainP`) and fixes the round at `4Δ(t+3) + 2Δ`, while Theorem 6's Cases 1
    and 2 both need the slot-`(t+1)` proposer honest too and Case 2 only lands at
    `fconf(t+4)`.
- **Theorem 7 is proved** (2026-08-08), so Appendix C.2 is complete. `theorem7 : ThmEbbAndFlow`
  in `Analysis/Theorems.lean`, Definition 7's three conjuncts assembled:
  `theorem4_dynamicallyAvailable` relaxed to the shared confirmation time
  (`LiveActive.mono_tconf`), `chFin_safe` at every pair of indices with the liveness half from
  Theorem 6, and `chFin_le_chAva`.
  * **Lemma 1 became a hypothesis with an explicit window** (user decision, 2026-08-08):
    `HonestProposerPairs W x5` — from any time `τ`, honest proposers at two consecutive slots
    `t`, `t+1` with `propose(t) ∈ [τ, τ + W·4Δ]`, each half carrying the proposal and the
    proposer's honesty at emission and at its vote round. The paper gets this from Lemma 1
    *w.o.p.*; with no probability layer it is assumed, and `W` is what makes the confirmation
    time finite. `HonestProposalWindow5` will not substitute: it gives *one* honest proposal
    per `κ` slots, and Theorem 6's Cases 1 and 2 both need two in a row.
  * **`tconf` dominates both chains' bounds**, since Definition 7 states one: `4Δ·2κ + Δ + 1`
    for `chainava`, `4Δ·(W + 4) + 2Δ` for `chainfin` — the `+4` is Case 2's extra slot. `slack`
    need only clear `2Δ`, which is what puts the pair's vote window past `GAT`.
  * **The activity gap closes itself.** `LiveActive` hands over a validator active at the
    *later* round, not one active in slot `t+3`/`t+4` as the Theorem 6 faces want. Past `GAT`
    every honest validator is awake (`GlobalAwakeTime`) and corruption is monotone, so
    honest-at-the-later-round gives awake throughout the earlier windows — the same
    `hact2`-style step `chp_le_chFin_at_vote5` already used one slot down.
  * The proof needs no case split on slot `t`'s own carried checkpoint: Cases 1 and 2 between
    them cover `gjp'.c = t` and `≠ t` and neither constrains `gjp`, so
    `theorem6_liveness_txpool_of_low` is not used here at all.

- **Theorem 6's Case 1 is proved too** (2026-08-07), so both of the theorem's *provable*
  branches are done: `theorem6_liveness_case1` / `theorem6_liveness_txpool_case1` beside
  `theorem6_liveness_of_low` / `theorem6_liveness_txpool_of_low`. Case 1 turned out
  *simpler* than Lemma 18's regime — no induction — because `lemma17_gjFrozen` pins the
  slot-`(t+1)` frozen checkpoint to the proposal's own `GJ_{p'}` outright, so the extension
  branch fires by the case hypothesis `GJ_{p'}.c = t` and the target is the tick's available
  chain.
  Two refactors made that possible, and both are improvements in their own right:
  * **the shared lemmas no longer take the slot's pinning.** `fastConfirm_eq_chp5`,
    `chAva_eq_chp_at_fconf5`, `vote_tick_bounds_chp5` and `chAva_and_justified_le_chp5` used
    it only for chain bounds that `justified_le_chp_before5` supplies outright. What still
    needs pinning is exactly what should: the branch analysis at slot `t+1`.
  * **finalization is re-based on the slot-`(t+1)` pinning.** `finalized_chp_next5`,
    `chp_le_chFin_at_vote5`, `chp_le_chFin5` and `chFin_txpool5` take
    `SlotPinned x5 (t+1) chp' ⟨chp, t+1⟩` rather than slot `t`'s, so the two branches meet
    at the one place they agree: Lemma 18's regime reaches it by re-justification
    (`slotPinned_next5`), Case 1 by the proposal (`slotPinned_case1_5`).
  `gat_le_voting_succ5` slides the global-awake bound forward a slot, which the faces had
  been repeating inline.
- **Fourteenth authors'-note finding: Theorem 6's Case 2 inherits the thirteenth finding, and
  Theorem 6's own hypotheses cannot repair it** (2026-08-07). Read from v1 p.24, the theorem
  assumes honest proposers at `t` and `t+1` only, and splits on `GJ^{propose(t)}_p.c`:
  * `< t − 1` — Lemma 18 at slot `t`, whose finalization half needs an honest proposer at
    `t+1`: **available**, so this branch is fine, and it is the one proved here
    (`theorem6_liveness_of_low`).
  * `= t − 1`, **Case 1** (the slot-`(t+1)` proposer sees a slot-`t` justification): the
    finalization is at `t+2`, and the slot-`(t+2)` fin-votes are pinned by the honest
    proposer at `t+1`: **available**, so this branch is provable — it is the work still to
    do.
  * `= t − 1`, **Case 2** (it sees none): the paper applies Lemma 18 *at slot `t+1`*, so the
    finalization is at `t+3` and the slot-`(t+3)` fin-votes need an honest proposer at
    `t+2` — which Theorem 6 does not assume. **This branch does not follow from the stated
    hypotheses.**
  The adversary's attack was the thirteenth finding's, one slot later: a corrupt slot-`(t+2)`
  proposer sends different (individually valid) proposals to different honest validators, the
  honest slot-`(t+2)` votes split, the fast confirmations differ, and so do the available
  chains that become the slot-`(t+3)` fin-vote targets. Splitting the honest validators so
  that no group plus the `f < n/3` corrupt reaches `2n/3` prevented any *link* forming, so
  nothing was finalized at `t+3`.
  **Retired by the spec change, and Case 2 is now proved** (2026-08-07): with finalization
  counting fin-votes by source, the split targets no longer matter, Lemma 18 needs only its
  own slot's honest proposer, and Case 2 follows from Theorem 6's stated hypotheses — the
  relaxed Lemma 18 at slot `t+1` (whose `hlow` is exactly Case 2's "sees no slot-`t`
  justification": `propose_gj_c_lt5` gives `GJ.c < t+1` for any honest slot-`(t+1)` proposal,
  and `≠ t` closes it), then `chp ⪯ chp'` by Lemma 12 (`chp_le_chp_next5`). No honest proposer
  at `t+2` is needed. Faces: `theorem6_liveness_case2`, `theorem6_liveness_txpool_case2`.
  **One divergence to keep**: this branch finalizes `(chp', t+2)`, so its conclusion holds for
  validators active in slot `t+4`, from `fconf(t+4)` on — a slot later than the other two
  branches, where the paper states one round bound, `r ≥ 4Δ(t+3) + 2Δ`, for all three. The
  paper's Case 2 has the same shape (it applies Lemma 18 at `t+1`, which finalizes at `t+3`
  what is justified at `t+2`), so the bound looks optimistic by one slot rather than our
  rendering being weak.
- **Theorem 6's remaining case, analysed** (2026-08-07). The paper splits on
  `GJ^{propose(t)}_p.c`; the `< t − 1` branch is Lemma 18 and is proved. The `= t − 1` branch
  (its Case 1 and Case 2) **cannot reuse `SlotPinned` as it stands**, and the reason is worth
  keeping: there the slot-`t` checkpoint `C` that the honest slot-`(t+1)` fin-votes take as
  their source is only known to be justified *in the slot-`(t+1)` proposer's view at
  `propose(t+1)`* (that is the case hypothesis, `GJ^{propose(t+1)}_{p2} = C = (ch', t)`),
  whereas `SlotPinned.justified` asks for justification from `fconf(t)` on. It cannot be
  pushed back: `C` is justified by slot-`t` fin-votes, and while the honest ones are delivered
  by `fconf(t)`, the quorum may need corrupt ones, which the adversary can inject at any time.
  What to do instead, all of it available:
  * where the slot-`t` development used `gj = T` in the window, use the **bound** instead —
    `justified_le_chp_before5` (proved, and hypothesis-free in this respect) gives
    `(gj …).ch ⪯ chp` for every view below `voting(t+1)`, which is all that
    `fastConfirm_eq_chp5` and `chAva_eq_chp_at_fconf5` need of it (they only have to know the
    `GJ` branch of `fastconfirm` does not fire);
  * where it used the merge's frozen checkpoint, use **Lemma 17 at slot `t+1`**
    (`lemma17_gjFrozen`, which needs nothing about carried checkpoints): the slot-`(t+1)`
    proposal's own `GJ_p` becomes every active's frozen checkpoint there, so the branch
    analysis at `t+1` runs off the proposal rather than off the merge;
  * `C.ch ⪯ chp` comes from `justified_le_chp_before5` again.
  So the shape is the same but the pinning comes from the proposal, not from a window: expect
  a `SlotPinnedByProposal`-style variant rather than an instance of the present structure.
- **Thirteenth authors'-note finding: Lemma 18's finalization half does not follow from its
  hypotheses** (2026-08-07). The paper's Lemma 18 concludes "chain `chp` is justified at slot
  `t+1`, and finalized at slot `t+2`". The justification half is proved here
  (`justified_chp_next5`, face `lemma18_justified`). The finalization half is not, and cannot
  be: finalizing `(chp, t+1)` needs a **supermajority link** out of it, so the slot-`(t+2)`
  fin-votes must agree on their *target* as well as their source, and the paper's proof argues
  only the source — "In slot `t+2`, all honest validators vote with source `(chp, t+1)`, and
  by round `4Δ(t+2)+2Δ` these votes are visible to all honest validators, finalizing `chp`".
  The target is each voter's *own* available chain (Algorithm 5 lines 14–15, extension
  branch, since `GJfrozen.c = t+1 = (t+2)-1`), and with a **corrupt slot-`(t+1)` proposer**
  those need not agree: such a proposer can send different proposals to different halves of
  the honest validators, so the honest slot-`(t+1)` votes split, and a chain can reach `2n/3`
  support in one view and not another — `n/2` honest plus `f < n/3` corrupt exceeds `2n/3`,
  so the two halves can fast-confirm *different* chains, leaving different available chains at
  slot `t+2`. Lemma 18 assumes nothing about the slot-`(t+1)` proposer.
  **The repair, and why it costs nothing:** Theorem 6 is the only consumer, and it has honest
  proposers at both `t` and `t+1`, so the missing hypothesis is exactly "slot `t+1` has an
  honest proposer". With it, Lemma 17 at slot `t+1` pins every honest vote there, the slot's
  fast confirmation is that proposal, and the slot-`(t+2)` targets agree. That is the
  development still owed — it is the `GJ.c = s - 1` companion of everything proved for slot
  `t` (whose `hlow : GJ_p.c < t - 1` fails at `t+1`, since `(GJ_p.ch, t)` is justified by
  `propose(t+1)`), so it needs its own pass rather than an instantiation.
  **Resolved by the spec change instead** (2026-08-07, entry above): finalization now counts
  fin-votes by *source*, so the slot-`(t+2)` targets are free to differ and the attack has
  nothing to attack. `lemma18` holds with one honest proposer, at slot `t`, as the paper
  states it, and the repair described in this entry — an honest proposer at `t+1` — is
  superseded, not needed.
- **Twelfth finding resolved by the pseudocode itself — no spec change** (2026-08-06).
  Algorithm 5's proposal-processing block, read off page 11 of v1 with the glyph codes,
  is: line 33 `GJ_p <15> GJ^frozen_i`, line 35 `if ch^frozen_i ⋡ GJ_p.ch`, line 37
  `if ch^frozen_i <16> ch_Cp`. So the relation on **checkpoints** is `≥` while the two on
  **chains**, in the immediately following lines, are `⪰`/`⪯`. The paper therefore does
  not mean chain extension at line 33, and our slot-only rendering
  (`acc.gjFrozen.c ≤ gjp.c`) is right. The consequence stands: the paper's Lemma 17 Case
  2 needs `GJ^{frozen,merge}_i.ch ⪯ chC_p`, which its `GJ_p ≥ GJ^{frozen,merge}_i` does
  not give, and we bridge it with `justified_chains_comparable` instead — routed through
  the available chain, hence through Lemma 10 and `GST = 0`. Cross-slot nesting of
  justified checkpoints does *not* follow from E1/E2 alone: two conflicting justified
  checkpoints at different slots violate neither condition.
- **Appendix C.2 under way** (2026-08-06), in `Analysis/Proofs/Finality5.lean`. Proved:
  **Lemma 15** (honest validators are never slashed), **Theorem 5** (accountable safety —
  and this one *is* the `Security.lean` rendering, `ThmAccountableSafety`, since Definition
  6 has no probability layer), **Lemma 16** (the finalized chain grows), plus Theorem 6's
  safety half (`chFin_comparable`) and Definition 7's third conjunct
  (`chFin_le_chAva5`). Notes:
  * this half is *not* a transfer — Algorithm 2 has no finality component, so nothing comes
    through Lemma 10. It rests on Appendix B's counting (Lemmas 8–9) plus behavioural
    invariants of Algorithm 5's own fin-votes.
  * `justified_nest` is the workhorse: a finalized checkpoint's chain prefixes every
    justified checkpoint at or above its slot, Lemma 8's slashing disjunct being killed by
    Lemma 15 and `f < n/3`. Used by Lemma 16, `chFin_comparable`, `gf_le_gj`.
  * Lemma 15 and Theorem 5 need **no corruption bound** (the paper's `f ∈ [0, n]`), so
    `gjFrozen`'s monotonicity takes `0 < Fintype.card Node` rather than resilience.
  * Lemma 16 is proved by induction over the step, not the paper's contradiction on a first
    violating round; that route needs neither synchrony nor the paper's
    merge-in-between argument.
  **Remaining in C.2**: Lemmas 17–18 (an honest proposal's votes and the re-justification
  chain), Theorem 6's liveness half, Theorem 7.

  Groundwork for Lemma 17 already in place (all green): the **gjFrozen component of
  `frozen_at_vote_tick5`** (the checkpoint a validator carries into its vote tick was frozen
  at the previous slot's merge — `handler_merge_gjFrozen` plus the extended
  `handler_frozen_quiet`/`frozen_step5`); **`processProposals_gjFrozen_eq`**, the fold
  characterisation pinning `gjFrozen` to `GJ_p` when every valid slot-`t` proposal in the
  view names it (over the abstract `foldl_absorbing`/`foldl_keeps`, so the concrete condition
  tree is never restated); and **`propose_fields5`** (an honest proposal's sender is the
  slot's proposer and its checkpoint is `GJ` of its own view at its tick, with the tick's
  label, time, awakeness and emission returned).

  **Lemma 17 is proved** (`lemma17_gjFrozen`, 2026-08-06): in a slot with an honest
  proposer, every active validator's vote tick freezes the proposal's own `GJ_p`. Its
  ingredients: `propose_fields5` (an honest proposal's sender, checkpoint, chain,
  fast-confirmed chain and certificate, read off its own tick, with the tick's label, time,
  awakeness and log delta), `honest_propose_valid5` (such a proposal is valid in any view
  that has caught up with the proposer's — certificate rung from `fastconfirm`'s own
  certificate, justified rung on the `GJ` branch), and the identification of any valid
  slot-`t` proposal in the voter's view with *this* one (validity pins the sender;
  `propose_provenance5` + `OneTickPerReading` + `tick_sends_subsingleton5` pin the message).
  Also proved: **`justified_of_quorum_votes`** — a quorum of matching fin-votes justifies its
  target, Lemma 18's engine.

  **The plan for Lemma 18, worked out in detail** (2026-08-06). With `GJ_p.c < t - 1`, Lemma
  17 makes every slot-`t` active's fin-vote read `GJ_p → (GJ_p.ch, t)`: the source is the
  frozen checkpoint and the target's re-justification branch fires precisely because
  `gjFrozen.c ≠ t - 1`. After `max(GST, GAT) + 4Δ` *every* honest validator is active
  (`GlobalAwake`, a hypothesis Lemma 18 must take — the paper's `max(GST, GAT)` clause), so
  those votes number `n - f > 2n/3` and `justified_of_quorum_votes` justifies
  `T = (GJ_p.ch, t)` in every honest view by `proposing(t+1)`.
  **All three uniqueness facts this rests on are now proved** (2026-08-06):
  `fcs_eq_of_honest_agreement` (a slot's fast confirmation is exactly the chain its honest
  voters agreed on — at least it, being a quorum-supported candidate; at most it, since its
  own quorum holds an honest validator whose slot vote *is* that chain),
  `justified_slot_unique` (a slot's justified checkpoint is the one its honest voters
  targeted) and `no_justified_above_slot` (nothing above slot `t` is justified before slot
  `t+1`'s votes exist — an honest fin-vote's slot is its target's checkpoint slot, and such a
  vote is not in the log before `voting(s)`), alongside `justified_of_quorum_votes`. **Lemma 18's first round is proved**: `rejustified_target5` — with an
  honest proposer whose carried checkpoint is older than the previous slot and every
  validator awake (`GlobalAwakeTime`, the paper's `max(GST, GAT)` clause), `(GJ_p.ch, t)` is
  justified in every awake validator's view from `voting(t) + Δ` on, over
  `finvote_of_active5` (every active's slot-`t` fin-vote reads `GJ_p → (GJ_p.ch, t)`, by
  Lemma 17 and the target's re-justification branch), `active_of_globalAwake`,
  `honest_quorum` and `justified_of_quorum_votes`. What remains of Lemma 18 is the second
  round. **Its first five steps are now proved** (2026-08-06), and the route turned out
  cheaper than the plan above: the `chMFC ⪯ chp` fact does *not* need extracting from
  `Provenance2.chi_le_mfc`, because the vote itself carries it.
  1. **The vote's own bound.** Algorithm 2's Lemma-4 base case already proved the vote *is*
     `chp` and threw it away in the statement; it is now split — `activeVotesEq_of_propose`
     keeps the equality (`ActiveVotesEq2`) and `activeVotesExtend_of_propose` is the one-line
     weakening Lemma 2's induction consumes. It crosses to Algorithm 5 unchanged
     (`activeVotesEq_transfer'`: a vote's chain is not a finality component, so dynamic
     equivalence leaves it alone), assembled as `MfcEquiv.activeVotesEq5_of_propose`. Then
     `chainLe_of_votePicks5` + `vote_chain_ge_mfc5` turn an honest vote into
     `chMFC ⪯ its chain` **and hand back the emitting tick** — which is also how the
     vote-tick index is obtained from the vote alone, with no diligence argument.
  2. **`honest_slot_vote_pinned5`**: an honest slot-`t` vote is exactly
     `[vote, chp, GJ_p → (GJ_p.ch, t), t]` — chain from step 1, source and target from
     `finvote_of_active5`, the two identified because a validator votes once per slot
     (`honest_vote_unique`). This one lemma serves every later "all honest slot-`t` votes
     agree on …" hypothesis.
  3. **`fcs_eq_chp5`**: `fastconfirmsimple` at slot `t` returns `chp` in every awake view
     from `fconf(t)` on, over `fcs_eq_of_honest_agreement`.
  4. **`gj_eq_target5`**: between `fconf(t)` and `voting(t+1)` the greatest justified
     checkpoint of every awake view is `(GJ_p.ch, t)` — justified by round one, maximal
     because `no_justified_above_slot`, unique at its slot by `justified_slot_unique`.
  5. **`chAva_eq_chp_at_fconf5`**: every honest validator leaves slot `t` with
     `chAva = chp`. The vote tick's three candidates all sit below `chp` (previous chain by
     Lemma 13 ∘ step 1, κ-deep prefix by `kappaPrefix_le_self`, frozen justified chain by
     Lemma 17 with `GJ_p.ch ⪯ chp`); `chAva_quiet_between` carries that to the fast-confirm
     tick (`chAva`'s only writes are at vote and fast-confirm readings, and no reading of
     either kind falls strictly between a slot's two); and there the write takes the longer
     of `chAva` and `chp`, which antisymmetry makes `chp` either way.
  **What remains of Lemma 18, with the obstacle resolved on paper** (2026-08-06):
  * *the target at slot `t+1` is `(chp, t+1)`*. The fin-vote target is
    `⟨chAva_new, t+1⟩` (the non-re-justification branch, since `gjFrozen.c = t`), so
    agreement needs `chAva_new = chp`, hence `kappaPrefix κ (t+1) chMFC ⪯ chp`.
    `kappaPrefix_le_of_close` would want `slotsIncreasing chMFC`, which the model does
    **not** give — chains are lists and `candidates`/`mfc` do not filter `sortedChain`, so
    an adversarial vote can carry an unsorted chain. **That detour is unnecessary**: at the
    slot-`(t+1)` vote tick one can prove `chMFC = chp` outright. `mfc`'s majority test
    counts *slot-`t`* votes (`fil1Exp` keeps `msgSlot = t − 1`), every honest slot-`t` vote
    is `chp` (step 2) and every honest slot-`t` vote is in the frozen view (sent at
    `vote(t)`, delivered by `fconf(t) ≤ merge(t)`), so a candidate not below `chp` draws
    support from corrupt senders only: `2f > n − f` contradicts `f < n/3`. With
    `mfc_base_or_majority`, the base case is `processProposals_bounded` with `O := chp` —
    its certificate writes are bounded by the same counting and its justified-chain writes
    by step 4 — and Lemma 12's `chp ⪯ chMFC` closes the equality. So **no spec change is
    needed**, and in particular `candidates` need not filter `sortedChain`.
  * *the counting half of that is now proved* (2026-08-06): `le_chp_of_support5` (in a view
    where every honest slot-`t` vote is `chp`, a chain with more than `f` supporting senders
    is a prefix of `chp` — one supporter is honest) and `majority_le_chp5` (hence nothing
    beyond `chp` passes the slot-`(t+1)` majority test, whose numerator must exceed
    `(n − f)/2 > f`). Its caller owes two hypotheses: `hall`, from
    `honest_slot_vote_pinned5`, and `hvoters`, the honest validators being slot-`t` voters
    in the view, built like `fcs_eq_chp5`'s `hin_view`.
  * **the one obstacle left, with its shape identified.** `mfc_base_or_majority`'s *base*
    case needs the processed frozen chain `⪯ chp`. Its write offers are: the seed (the
    merge value, `= chp` by `fcs_eq_chp5` + `gj_eq_target5` at the merge index), a valid
    proposal's `chC` (bounded by `support_of_cert` + `le_chp_of_support5`), and a justified
    checkpoint's `GJ_p.ch`. For the last, `processProposals_bounded`'s `hjust` asks for the
    bound on **every** justified checkpoint in the view, which is more than the fold needs —
    the write is conditional on `acc.gjFrozen.c ≤ GJ_p.c`, and the accumulator starts at
    `T = (GJ_p.ch, t)`, so only slot-`t` checkpoints can fire, and those are `T` itself by
    `justified_slot_unique`. **Corrected 2026-08-07 — these are not alternatives.** The
    slot condition alone does *not* close it: at time exactly `voting(t+1)` a view may
    already hold slot-`(t+1)` fin-votes, from validators whose ticks came first, so
    `no_justified_above_slot` (strict `<`) does not apply and a slot-`(t+1)` checkpoint
    passes `acc.gjFrozen.c ≤ GJ_p.c` too. Bounding *its* chain means bounding the honest
    slot-`(t+1)` targets, which is the thing being proved — so the induction is
    unavoidable:
    **do this** — prove "every checkpoint justified in a view at time `≤ voting(t+1)` has
    chain `⪯ chp`" with `MfcEquiv.justified_le_of_chAva_le`, whose hypothesis is exactly
    "every *strictly earlier* vote tick's `voteChAva` is `⪯ chp`", by induction on the
    index in the shape of Lemma 10's `table_and_dominance`. It also pins the honest
    slot-`(t+1)` targets in tick order, which is what a quorum on one target needs.
    **Optional afterwards** — generalise `processProposals_bounded` to a *conjunctive* fold
    invariant (`chFrozen ⪯ O` with `seed.gjFrozen.c ≤ acc.gjFrozen.c`); it would shorten
    the `hjust` obligation but is not what unblocks it. If attempted, remember that a
    restated copy of the concrete `match` is not accepted as defeq, so the step obligations
    must be discharged inline on `refine`-produced goals.
  * **the induction, worked out to the case level** (2026-08-07, ready to type in). Use
    `MfcEquiv.justified_to_voteChAva`, **not** `justified_le_of_chAva_le`: the former hands
    back a vote tick with its **joining check open**, so `vote_tick_chAva` turns its
    `voteChAva` into the post-state `chAva` and the whole argument stays about states. The
    statement, by induction on `m` (ordinary, not strong):

        ∀ m, x5[m].time ≤ voting(t+1) →
          (∀ u, chainLe x5[m][u].st.chAva chp) ∧
          (∀ u C, JustifiedIn n x5[m][u].view C → chainLe C.ch chp)

    Order matters inside the step: prove the `chAva` half at `m+1` from **both** halves at
    `m`, then the justified half at `m+1` from the `chAva` half at indices `≤ m+1` — which
    is why the two must be one induction. Cases of the `chAva` half, over `chAva_step5`:
    - unchanged: the induction hypothesis;
    - vote write at slot `ti ≤ t`: the check is open in that case, so the write *is* the
      post-state `chAva` at `m+1`, whose time is `voting(ti) ≤ voting(t)` —
      `chAva_le_chp_before5`, no fold analysis at all;
    - vote write at `ti = t+1` (the only other possibility, by the slot arithmetic): the
      three `voteChAva` candidates are the previous `chAva` (induction hypothesis), the
      κ-deep prefix (`⪯ chMFC`, and `chMFC ⪯ chp` by `mfc_base_or_majority` —
      `majority_le_chp5` for the majority branch, `processProposals_bounded` with `O := chp`
      for the base, its `hseed` the merge value `= chp` by `frozen_at_vote_tick5` +
      `fastConfirm_eq_chp5`, its `hval` by `support_of_cert` + `le_chp_of_support5`, its
      `hjust` **the justified half at `m`**), and the processed `gjFrozen.ch` (the
      pre-state's, `= T` by `frozen_at_vote_tick5`'s `gjFrozen` component with
      `gj_eq_target5`, or a justified checkpoint of the view — again the justified half at
      `m`);
    - fast-confirm write at `ti < t`: post-state time `fconf(ti) < voting(t)`, so
      `chAva_le_chp_before5`; at `ti = t`: `fastConfirm_eq_chp5`; at `ti = t+1`: excluded by
      the time bound.
    **This is now done** (2026-08-07): `processProposals_gjFrozen_cases` (over the new
    abstract `foldl_seed_or_prop` — restating the concrete fold in a generalized `have`
    fails, because the definition's `let` shows up as `have` in the goal),
    `vote_tick_bounds_chp5` (both slot-`(t+1)` bounds, given the justified bound) and
    `chAva_and_justified_le_chp5` (the induction). Also `handler_vote_sends5_extend`, the
    extension branch's send.
  * **A second tick-order induction is needed, one level up** (found 2026-08-07 while
    proving `finvote_extend_of_active5`, which is *not* in the tree — the attempt was
    reverted). The fin-vote target is
    `if gjFrozen.c = t then ⟨chAva_new, t+1⟩ else ⟨gjFrozen.ch, t+1⟩`, and `chAva_new = chp`
    is settled per validator (monotonicity from slot `t`'s fast confirm, plus the induction's
    upper bound). What is not settled is which branch fires: the processed `gjFrozen` is
    `T = (GJ_p.ch, t)` *or* a checkpoint justified at slot `t+1`, because
    `no_justified_above_slot` needs `time < voting(t+1)` and the vote tick sits exactly at
    `voting(t+1)` — a view there may already hold slot-`(t+1)` fin-votes from validators that
    ticked first. Both cases give the same target, so the lemma is true:
    - `gjFrozen.c = t` — then `gjFrozen = T` by `justified_slot_unique`, the extension branch
      fires, and the target is `⟨chp, t+1⟩`;
    - `gjFrozen.c = t+1` (the only other value, by `no_justified_above_slot` at slot `t+1`,
      whose time bound `< voting(t+2)` *does* hold, and the fold's slot monotonicity from
      `T`) — then the re-justification branch fires with target `⟨gjFrozen.ch, t+1⟩`, and
      `gjFrozen.ch = chp` because that checkpoint's own quorum holds an honest validator
      whose fin-vote named it, and an honest slot-`(t+1)` target's chain is that voter's
      `chAva_new = chp`.
    The second case is what needs the induction: it appeals to *another* validator's target,
    at a strictly smaller index. So the statement to prove by strong induction on the index
    is "every honest slot-`(t+1)` fin-vote in the log targets `⟨chp, t+1⟩`", with the case
    split above inside the step. Only then do `justified_of_quorum_votes` (justifying
    `(chp, t+1)`) and slot `t+2`'s link (finalizing it) follow.
  * then a second `justified_of_quorum_votes` justifies `(chp, t+1)`, and slot `t+2`'s votes
    with that source finalize it — `FinalizedIn` being justification plus a link one slot
    up. Theorem 6 then splits on `GJ_{p₂}` as the paper does, using the de-probabilized
    *two consecutive honest proposers* window, and Theorem 7 assembles Theorems 4, 5, 6 with
    `chFin_le_chAva5`.
  What Lemma 17 needed, now done:
  * **the honest proposal is valid in the voter's view** — the certificate rung on
    `fastconfirm`'s quorum branch (its votes are in the proposer's view, which synchrony
    delivers) and the justified rung on the `GJ` branch. Algorithm 2's counterpart is the
    `hvalidprop` block inside `Provenance2.chi_le_mfc`; that is the pattern to port.
  * **one proposal per honest proposer per slot**, to identify any valid slot-`t` proposal in
    the view with *this* one: `propose_provenance5` puts both at the same tick
    (`OneTickPerReading`) and `tick_sends_subsingleton5` collapses them — for which
    `propose_fields5` should return the log *delta* rather than plain membership.
  Then Lemma 18 needs the quorum-construction step (honest fin-votes at a slot form a
  `link`, so their common target is justified), and Theorem 6 additionally a de-probabilized
  *two consecutive honest proposers* window — the paper's Lemma `2honestproposers`, to be
  rendered on the `HonestProposalWindow` pattern.
- **Appendix C.1 is complete** (2026-08-06): Lemmas 10–14 and Theorems 3–4, in
  `Analysis/Proofs/Availability5.lean` with faces in `Analysis/Lemmas.lean` /
  `Analysis/Theorems.lean`. Two things the paper's "replace `Chain` with `chainava`"
  instruction hides, both from Algorithm 5's extra `chainava` write (the fast-confirm
  round's `chainava ← fastcand`, where `fastcand` is the **greatest justified chain**
  whenever that chain does not extend the fast-confirmed one):
  * the **order facts**. `chAva_comparable` (any two available chains of a run are
    comparable) comes from Lemma 10's dominance plus Algorithm 2's own Theorem 2, and
    `chAva_mono` (a validator's available chain only grows) from it — the `GJ`-branch write
    could move `chainava` sideways for all the pseudocode says, so neither is readable off
    the algorithm. Theorem 4's safety half *is* `chAva_comparable`.
  * the **`GJ` branch** in Lemma 14 (which the paper's "follows Lemma 7's proof" skips,
    though it does treat the analogous case inside Theorem 4's proof). Discharged by: the
    justified chain descends to some honest validator's available chain
    (`justified_to_voteChAva`), Theorem 3 orders `chp` against that chain, and both orders
    that would leave `chp` outside the justified chain also put the justified chain below
    the fast-confirmed one — against the branch's own condition.
  Hypothesis note: **Lemma 14's Lean statement carries `1 ≤ κ` and
  `HonestProposalWindow5`, which the paper's Lemma 14 does not** — they are the cost of
  covering the `GJ` branch, which routes through Theorem 3 (hence Lemma 10 and Lemma 13).
  The paper's Lemma 7, whose proof it inherits, needs neither, Algorithm 2 having no such
  branch. Theorems 3 and 4 are rendered in the direct style of `theorem1`/`theorem2` (the
  `Security.lean`-shaped `ThmReorgResilienceFFG`/`ThmDynamicAvailabilityFFG` `Prop`s stay
  unproved as stated, for the same reason as for Algorithm 2: they quantify differently).
  Reusable pieces: `le_fcs_of_votes` (a slot's fast-confirmed chain extends anything its
  actives all voted above — the counting is view-local, and the quorum-intersection step
  is Algorithm 2's, reached because the two runs' views share a vote skeleton),
  `chAva_at_fconf5`, `propose_image5`/`propose_chain_facts5` (a proposal's chain is
  slot-sorted and tipped at its slot, read off the counterpart proposal in the simulated
  run — dynamic equivalence pins the *proposed* chain).
- **Appendix C's Lemmas 10–13 have paper faces** (2026-08-06). *Appendix C is not
  finished*: Definitions 8–9 and Lemmas 10–13 are done, and what remains of it is
  §C.1's **Theorem 3** (reorg resilience for Majorum), **Theorem 4** (dynamic
  availability) and **Lemma 14** (fast liveness), plus the whole of §C.2, partial
  synchrony — **Lemmas 15–18** and **Theorems 5–7** (accountable safety, liveness,
  ebb-and-flow). Theorems 3–7 exist as the `Prop` shells `ThmReorgResilienceFFG`,
  `ThmDynamicAvailabilityFFG`, `ThmAccountableSafety`, `ThmLiveness`, `ThmEbbAndFlow` in
  `Analysis/Theorems.lean`; Lemmas 14–18 have no rendering at all yet.
  `Analysis/Lemmas.lean` now carries `lemma10`–`lemma13`, each a single call into
  `MfcEquiv`, with `n` instantiated at `Fintype.card Node` (so the internal
  `hn : n = Fintype.card Node` is discharged by `rfl`). Lemmas 11–13's interface
  hypotheses (`MfcEquivalent`, the Algorithm-2 setting, the transferred window) are now
  discharged *from* Lemma 10 rather than assumed, so the faces read as statements about
  Algorithm-5 runs alone. Two housekeeping moves this required: the proof layer moved into
  namespace `Majorum.MfcEquiv` (the Analysis2 pattern — the faces need the plain
  `lemma11`… names; `ViewCorr.symm` is declared with a `_root_.` prefix so dot notation
  still resolves), and the `Lemma10Statement` shell `def` is gone. Axiom check:
  `lemma10`–`lemma13` depend on `[propext, Classical.choice, Quot.sound]` only.
- **Lemma 10 is proved** (2026-08-06). `lemma10`: every compliant Algorithm-5 run has an
  MFC-equivalent compliant Algorithm-2 run — `simulate x5`. The grand induction
  (`table_and_dominance`) carries Definition 8's table invariant and the dominance
  invariant together over the step index: the table's step consumes conditions 2.1/2.2 at
  the current tick (`agree_propose_at_tick`, `agree_vote_at_tick` — which need both
  invariants at *earlier* steps), and the dominance step (`dominance_step`) consumes the
  table invariant at earlier steps. Definition 9's condition 1 is `sends_correspond` (a
  tick's log delta is exactly its core's send, signed; the table maps one to the other and
  `sends_align` stops either side emitting alone). The window transfer is
  `window_transfer` via `tau_propose_slot` (a proposal's image is a proposal for the same
  slot — no table invariant needed, since the window quantifies the chains existentially).
  `dominance_step`'s vote-tick case is the interesting one: the κ-prefix written by
  Algorithm 5 is the κ-prefix of the *same* fork choice (2.2), which the simulated run
  either writes into its own confirmed chain at that very tick, or already tops — the two
  being comparable because both sit under the fork choice (Lemma 5's vote conjunct).
- **`chi_le_mfc`'s hypotheses split per conjunct** (2026-08-05): the propose-round
  conjunct now takes `x.Awake b vj` (its whole use of `Active` was deriving
  awakeness to receive by synchrony — verified in `le_mfc_at_propose2`/`_of_ave`/
  `_of_quorum`, all three weakened accordingly); the vote-round conjunct keeps
  `vj ∈ Active (s0+1)` (it needs the frozen trace's `Diligent` window). This is what
  lets 2.1's discharge work at a merely-awake proposer — a proposer's tick cannot
  witness `Active(s)`, whose window extends past it. Callers updated (Analysis2's
  `lemma5` face keeps its old statement, deriving awakeness from Active;
  `mfc_bounds_of_ave2` and `lemma13` derive x2-awakeness from the transferred tick's
  own enabledness). Also `justified_early` (nothing but genesis is justified in views
  at time ≤ Δ — the slot-0 vacuity that replaces `h25` at slot-0 propose ticks).
- **Post-option-A plan for 2.2's bounds** (2026-08-05). With the conditions aligned, the
  two processed frozen chains are conditional-max folds over write-sets satisfying: all
  writes sit under the simulated vote-round output `O2` (seed = the other's seed or
  justified; certificate writes via the x2-fold's `chFrozen_lb` + the y-blocker's
  quorum-comparability; justified writes via the descent + D + `chi_le_mfc`), hence
  pairwise comparable, hence the folds compute maxima
  (**`chainLe_foldl_of_comparable`**, proved); Algorithm 5's write-set = Algorithm
  2's ∪ justified extras (honest proposals' `chC` fields relate through 2.1 at the
  proposer's tick; adversarial ones are verbatim; `valid2 ⇒ valid5`), so **`b2 ⪯ b5`
  is free** and 2.2 closes by an `mfc` base-monotonicity step (`b2 ⪯ b5` +
  `b5 ⪯ mfc(b2)` ⇒ equal outputs — still to write, from `mfc_base_swap` +
  `base_le_mfc` + trans: `b2 ⪯ b5 ⪯ mfc(b2)` gives the swap's other bound
  directly, so `mfc_base_swap` suffices, no new lemma). Remaining before the strong
  induction: the value-set correspondence lemma (the two folds' chC-write
  multisets, per-proposal via `TableDynEq` + 2.1-at-earlier-ticks), `agree_at_tick`
  packaging 2.1/2.2 discharge, then the induction (TableDynEq ∀k, D ∀k), the window
  transfer, and `lemma10`.
- **Eleventh finding resolved: option A, the split condition** (user decision,
  2026-08-05; noted for the future: *revisit weakening Definition 9 instead*, if the
  deviation from the paper's pseudocode nesting becomes a problem). Algorithm 5's
  `processProposals` now performs the `chfrozen ← chC_p` write behind
  `valid ∧ chfrozen ⪯ chC_p` alone — exactly Algorithm 2's condition — while the
  `GJ_frozen`/`gjp.ch` writes stay behind the justification condition. Every certificate
  write is now common to both folds; Algorithm 5's extras are justified chains,
  covered by the descent. Proof fallout was five fold-lemmas
  (`processProposals_vFrozen`/`_activeAt`/`_chAva`/`_gjFrozen_justified`/`_chFrozen`);
  Lean note: for projection-invariant fields, `simp only [apply_ite
  NodeState.<field>, ite_self]` collapses arbitrarily nested condition structure where
  `split_ifs` refuses conditions containing `ite`s (split the `ite`-free condition by
  hand first when the field does change).
- **Eleventh finding (context): the two proposal folds' asymmetric conditions can
  break Lemma 10's conditions 1 and 2.2** (2026-08-05, STOPPED for user decision).
  Algorithm 5's `upon`-block covers *all three* writes — `GJ_frozen`, the
  `gjp.ch`-write, and the `chfrozen ← chC_p` write — behind
  `valid ∧ J(GJ_p, V_i) ∧ GJ_p ≥ GJ_frozen` (LaTeX nesting checked in the working
  copy: `\>\>\>` under the `\>\>` if; our spec is faithful). Algorithm 2's block
  makes its `chfrozen ← chC_p` conditional on `valid ∧ chfrozen ⪯ chC_p` only — it has no
  checkpoints to check. Consequence: an adversarial (slot-proposer-signed) proposal
  with a *valid certificate but unjustified `GJ_p`* is folded by every Algorithm-2
  receiver and skipped by every Algorithm-5 receiver; worse, `J(GJ_p, ·)` is
  view-dependent, so two Algorithm-5 receivers can *disagree* (fin-votes in flight),
  and no single simulated message can track both (mangling the free `qc`/`chC`
  fields kills the write for all x2 receivers or none). In a no-majority
  configuration the divergent frozen bases surface as the vote-round MFC outputs
  themselves, i.e. as the *votes* — breaking condition 1, hence Lemma 10, for the
  paper's own algorithms as written. The quorum-to-majority route cannot patch it:
  a `2n/3` certificate quorum survives the equivocation filter only up to `f`, and
  `2n/3 − f > |voters|/2` fails for `f` near `n/3`. All previously proved pieces
  are unaffected (they are conditional on `MfcEquivalent` or independent); what is
  at stake is whether `Lemma10Statement` is provable — or true — as rendered.
- **Definition 9 refined: condition 2.2 is gated by the joining check**
  (2026-08-05, flagged for user review). A validator asleep through the merge has
  stale frozen state, and the two vote-round fork choices genuinely need not agree at
  its silent ticks; the paper's per-slot conditions quantify over *active* validators
  (`H`), so `x5[k][p].st.activeAt ≤ t →` in 2.2 is the faithful reading, not a
  weakening. 2.1 stays ungated (propose reads current views only). Consumers updated:
  `tableDynEq_step`'s `hV` gains the gate (derived in-proof from the fired send via
  `mem_handler_send`), `mfc_bounds_of_ave2`/`lemma13` derive it from
  `Active`-membership via the new **`activeAt_le_voting5`** (ported from Provenance2)
  + **`tick_reading5`**/`tick_time5`. Lemmas 11–13 unchanged in statement.
- **Lemmas 11, 12 and 13 are all proved on the interface** (2026-08-05) — Appendix
  C's transfers, complete; Definition 9's statement is fully validated. `MfcEquiv.lean`:
  `lemma12` (an honest proposer's proposal crosses at its emitting tick —
  `propose_provenance5`, new, `vote_provenance`'s propose twin — dynamic equivalence
  preserves the proposed chain and slot, honesty at the counterpart's index follows
  from `propose(t) ≤ voting(t)` and monotone corruption; Lemma 4 runs on the
  equivalent run; votes and fork-choice bounds return through the transfers and
  `mfc_bounds_of_ave2`, Lemma 11's engine factored for reuse at every later slot) and
  `lemma13` (three lines of substance: the state-level 2.3/2.4 dominance hands
  `chAva` to an Algorithm-2 confirmed chain of no later a time, `chi_le_mfc` bounds
  that by the equivalent run's fork choice at either reading, 2.1/2.2 carry it back —
  the state-level rendering of 2.3/2.4 pays off exactly here). `lemma13` takes
  `HonestProposalWindow x2` directly; the face after Lemma 10 will need the window
  transfer from the x5 side (short, via `propose_provenance5` + condition 1 — still
  to write). All three: axioms `[propext, Classical.choice, Quot.sound]`. Remaining
  for Appendix C: the window transfer, the paper faces (blocked on Lemma 10), and
  the parked grand induction.
- **Lemma 11 is fully proved on the interface** (2026-08-05): `MfcEquiv.lean`'s
  `lemma11` — all three of the paper's conjuncts: at every slot-`t+1` active's propose
  and vote ticks the Algorithm-5 fork choice extends `ch` (conditions 2.1/2.2 rewrite
  the x5 MFC terms to the x2 ones, where `le_mfc_at_propose_of_ave` and
  `le_mfc_at_vote2` — both already existed — give the bounds), and the votes
  propagate (`lemma11_votes`). Axiom check: `[propext, Classical.choice, Quot.sound]`
  (manual `#print axioms`; majorum has no compiled audit file). The paper-faithful
  face (with Lemma 10 invoked internally rather than `MfcEquivalent` hypothesized)
  waits for the grand induction. Slot-arithmetic note: condition 2.1's instance
  carries `t + 1 - 1` — `simp only [Nat.add_sub_cancel]` before the rewrite.
- **Lemma 11's votes half is proved on the interface** (2026-08-05) — the statement
  validation the parking decision asked for. `MfcEquiv.lean`: `ActiveVotesExtend5`
  (the Alg-5 vote fact), `mem_of_mem_sub`, the two directional transfers
  **`activeVotesExtend_transfer`/`'`** (an active's vote crosses the equivalence at
  its own emitting tick: `vote_provenance`(2) finds the tick, condition 1's delta
  pairing hands over a vote with the same signer/chain/slot, and the other run's
  synchronized clock pins the reading), and **`lemma11_votes`** = transfer ∘
  `Analysis2.lemma2` ∘ transfer. Watch-outs hit: Analysis2 pins the quorum threshold
  at `Fintype.card Node` — unifying against a generic `n` makes `whnf` unfold
  `protocol2` until timeout; paper-facing transfer statements take
  `hn : n = Fintype.card Node` and `subst` it. Next: Lemma 11's two MFC conjuncts
  (via 2.1/2.2 + the x2-side MFC bounds), Lemma 12 (propose transfer + Lemma 4),
  Lemma 13 (chAva ⪯ MFC via 2.3/2.4 + Lemma 5), then their faces in
  `Analysis/Lemmas.lean`.
- **Definition 9 rendered; the grand induction parked** (user decision, 2026-08-05):
  prove the transfers (Lemmas 11–13) against `MfcEquivalent` *as a hypothesis* first,
  validating Lemma 10's statement before paying for the lengthy induction.
  `MfcEquiv.lean`: **`MfcEquivalent x5 x2`** — same non-delivery steps; each shared
  tick's log deltas pair under `SDynEq` (condition 1/2.7 — deltas are the handlers'
  sends, at most singletons, honest by `AwakeHonest`); 2.1/2.2 as the two MFC-term
  equalities at propose/vote readings; 2.3/2.4 strengthened to state level (`chAva`
  dominated by some x2 `chi` of no later a time, at *every* step — implies the
  paper's two reading samples). **`Lemma10Statement`** (a `Prop` shell, unproved) —
  hypothesis row: `SettingGA` + card ≤ n + `3f < n` + `1 ≤ κ` +
  `HonestProposalWindow5` (the Alg-5-side window, new def) — Lemma 5's row, forced by
  the paper's own use of Lemma 5. User approved the three rendering decisions
  (delta-based condition 1, state-level dominance, the hypothesis row).
- **Lemma 10, stage C2b-3c: base provenance done; only the grand induction remains**
  (2026-08-05). `MfcEquiv.lean` gains **`processProposals_chFrozen`** (Algorithm 5's
  processed frozen chain is the merge seed, a checked slot-`t` proposal's `chC`, or a
  justification-checked checkpoint's chain — with the justification exposed) and
  `voteSkel_mono`. With `majority_comparable` (already in `Mfc.lean`),
  `processProposals2_chFrozen`(`_mono`/`_lb`), and everything above, **every
  ingredient of the grand induction now exists**; the induction itself (strong on the
  step index, carrying `TableDynEq` + the D dominance invariant + 2.1/2.2 per the
  recorded designs) is the one remaining large proof before C3. Lean notes:
  `first`-alternatives do NOT backtrack on a nested `by`-block that merely *logs*
  unsolved goals — enumerate `split_ifs` leaves with explicit bullets when
  alternatives can partially succeed; Alg 5's `let acc := …` chains elaborate as
  `have`-bindings, and respelling the fold lambda in a `have hgen` will not unify —
  `unfold` + `revert hmem; generalize V.toList = l; intro hmem` keeps the real term
  while retaining the membership fact.
- **Lemma 10, stage C2b-3c: the vote-round base bounds, designed** (2026-08-05).
  2.2's two cross-bounds at a vote tick, case-analyzed. `b2 ⪯ mfc(…, b5, …)`: both
  frozen chains *seed at the same merge value* (`fastConfirmSimple_congr` at the
  merge, via `frozen_viewCorr`), Algorithm 2's evolution is monotone
  (`processProposals2_chFrozen_mono`), so `seed ⪯ b2 ⪯ mfc2` (`base_le_mfc`), and the
  comparability trick (both below `mfc2`, condition orients) or the symmetric swap
  handles the rest. `b5 ⪯ mfc2` by `b5`'s provenance (an Alg-5 analogue of
  `processProposals2_chFrozen`, to be written — final `chFrozen5` is the merge seed,
  a checked proposal's `gjp.ch`, or its `chC`): the seed as above; `gjp.ch` is
  justified in the vote view → `justified_le_of_chAva_le`; `chC` is certified —
  `ValidProposal5`'s three rungs: genesis `⪯` everything; a certificate's `2n/3`
  quorum at slot `t−1` transfers by skeleton into the x2 pair (`majority_transfer`
  machinery) and bounds via majority — where `le_mfc_of_majority`'s
  extends-base requirement is discharged by **`majority_comparable`** (already in `Mfc.lean` — no subset
  hypothesis needed; `voteSkel_mono` added to `MfcEquiv.lean` alongside), or by the
  justification rung
  (`JustifiedIn` → the engine). All ingredients for the grand induction now exist or
  are short; the induction itself is the remaining large proof.
- **Lemma 10, stage C2b-3c: the grand induction's carried invariant, designed**
  (2026-08-05). Strong induction on the step index `k`, carrying: `TableDynEq x5 j`
  for all `j ≤ k`, the MFC agreements (2.1/2.2) at every tick `< k`, and the
  dominance invariant **D**: for every vote tick `k' < k` of `w` at reading `t` with
  the joining check open, `∃ a ≤ some-index, chainLe (voteChAva x5 k' w t)
  ((simulate x5)[a][w'].st.chi)` with `(simulate x5)[a].time ≤ t` — the paper's 2.3.
  D's maintenance at a new vote tick: the `chAva` fold's output is one of its three
  candidates (a fold-cases lemma still to write): (i) the *κ-prefix of `chMFC5`* —
  equal, via 2.2 at this step, to the κ-prefix of `chMFC2`, which is **exactly the
  chi the simulated counterpart's own tick writes** (`chi_step2`'s vote disjunct):
  witness `a := k'+1, w' := w`, equality; (ii) the *previous `chAva`* — trace back
  through `chAva_step5` (its fconf disjunct: the adopted fast confirmation is the
  simulated fconf tick's conditional write, dominance either way; its GJ case recurses);
  (iii) *`gjFrozen.ch`* — justified, descend through fin-vote targets as in
  `justified_le_of_chAva_le` until a fresh-mode target (an earlier `voteChAva`, D
  applies) or genesis. At each call site, D composes with **`chi_le_mfc`**
  (Provenance2's Lemma-5 engine: any x2 `chi` with time ≤ the reading is below both
  the propose- and vote-round MFC outputs — hypotheses `SettingGA`-shaped **plus
  `1 ≤ kappa` and `HonestProposalWindow (simulate x5)`**, which Lemma 10's face must
  therefore carry, matching the paper's Lemma 5 dependencies) to discharge
  `justified_le_of_chAva_le`'s `hchAva` and hence 2.5/2.6, hence 2.1/2.2
  (`mfc_propose_agree`/`mfc_vote_agree`), hence `tableDynEq_step`'s two obligations
  (`hP` directly; `hV` via `simPick_eq_pick5` + `viewCorr_of_tableDynEq`). Check
  whether `HonestProposalWindow` transfers from x5 (label/schedule-shaped?) or must
  be assumed on the simulated run directly.
- **Lemma 10, stage C2b-3c, opening: `chAva`'s step analysis** (2026-08-05).
  `MfcEquiv.lean`: **`chAva_step5`** — one step of Algorithm 5's available chain is
  unchanged, or the owner's vote tick with the joining check open writes the `chAva`
  fold (`voteChAva`, the same named fold `justified_le_of_chAva_le`'s hypothesis
  reads), or the owner's fast-confirm tick adopts a longer fast confirmation
  (`fastConfirm`'s output, with the not-below condition). With
  `processProposals_chAva` (the proposal fold never writes `chAva`). This is
  condition 2.3/2.4's case analysis — the paper's line-12/lines-21-23 sources.
  Lean notes: state execution equations at the `x5[m+1]` getElem spelling and bridge
  `exec5_succ` with an ascribed `have h5 : x5[m + 1] = _ := exec5_succ m` (defeq
  accepts; `rw` is spelling-sensitive both ways); after `cases h : x5.lbl m`, goal
  occurrences of `x5.lbl m` are already substituted, so label equalities in
  conclusions are supplied as `congrArg (Action.tick p) htr`, not `h.trans …`;
  `simp only [...getElem lemmas...]` leaves a cfg-vs-getElem spelling residue that
  only `rfl` (defeq) closes.
- **Lemma 10, stage C2b-3b: the 2.5/2.6 engine is proved** (2026-08-05).
  `MfcEquiv.lean`: **`justified_le_of_chAva_le`** — a checkpoint justified in *any*
  view reachable by step `i` is below any chain `M2` that dominates every earlier
  honest vote-tick's `chAva` output (`voteChAva`, the named fold). Strong induction on
  the checkpoint slot with the inner claim quantified over all (step, validator)
  pairs. The link case extracts an honest link voter (`exists_honest_of_quorum`),
  runs `vote_provenance`, reads the send (`handler_vote_fin_content`), and splits on
  the target mode: *fresh* (`gjFrozen.c = slot − 1`) hands `J.ch = voteChAva …` to
  the hypothesis; *stale* descends — the target's chain equals its source's, the
  source is the voter's processed `gjFrozen` (justified in the voter's own view,
  `gjFrozen_justified`), and link validity strictly drops the slot. **No `Relay`, no
  slack hypothesis**: because the inner claim ranges over all (step, validator)
  pairs, justification is consumed where it lives — the design discoveries about
  Relay slack and intra-reading fin-votes dissolved. What 2.5/2.6 now cost the step
  induction: only the `hchAva` composite (2.3∘Lemma 5: every earlier honest
  vote-tick's `chAva` output is below the target MFC output). Lean note: spell
  execution projections `x5[k][w]`, not `(x5.cfg k)[w]` — `vote_provenance`'s
  conclusion uses getElem and `rw` patterns are syntactic.
- **Lemma 10, stage C2b-3b: raw materials + two design discoveries** (2026-08-05).
  `MfcEquiv.lean` gains `exists_honest_of_quorum` (a `2n/3` quorum has a member honest
  at any given round: `CorruptionBounded` + `f < n/3` + card ≤ n) and
  `handler_vote_fin_content` (the vote send's `src`/`tgt` fields, exactly: source is
  the processed `gjFrozen`, target is `⟨chAva-fold, slot⟩` or `⟨gjFrozen.ch, slot⟩`).
  Discoveries while designing the 2.5 lemma: (i) the justification transfer from the
  fin-voter's view into the caller's view goes by `Relay` — which needs a `Δ` of slack
  between the voter's tick and the caller's reading; at a *propose* reading the phases
  supply it (`time ≡ 0 (mod 4Δ)` and `> 4Δs + Δ` force `≥ 4Δ(s+1)`), but at a *vote*
  reading a same-slot honest fin-vote can arrive within the same reading
  (intra-reading interleaving, which our model allows and the paper's atomic rounds
  exclude), and its target chain is the voter's *same-reading* `chAva` fold output —
  bounding it needs that voter's vote-round MFC agreement *at the same slot*, already
  proved only for strictly earlier steps. (ii) Consequence: **the grand induction is
  on the step index `k`, not on slots** — strong induction on steps carries 2.1–2.7
  for every earlier step, and the same-reading-earlier-step case is then ordinary.
  The 2.5 lemma should abstract its bound target (`M2 : Chain Tx` with the
  2.3∘Lemma-5 composite as a hypothesis: every honest vote-tick `chAva` output at an
  earlier step is `⪯ M2`), so the step induction can discharge it at both readings.
- **Lemma 10, stage C2b-3b, opening: the justification toolkit** (2026-08-05).
  `Finality.lean` gains `justifiedIn_mono` (justification survives view growth — link
  voters are monotone) and `gj_justified` (`GJ(V)` is justified: the fold starts at
  genesis and adopts only members of the justified-filtered set). `MfcEquiv.lean`
  gains the x5 execution invariant **`gjFrozen_justified`**: Algorithm 5's frozen
  greatest-justified checkpoint is justified in the current view at every step —
  genesis at init, `GJ` of the current view at merges, a justification-checked
  proposal checkpoint through `processProposals` (`processProposals_gjFrozen_justified`,
  the fold-invariant), monotone through deliveries. **The 2.5 proof, designed precisely** (strong
  induction on `J.c`, `J` justified in the proposer's view `V5`): genesis is below
  everything; for a link `C → J`, extract from the `2n/3` `linkVoters` a voter honest
  at the propose-view's time (`CorruptionBounded` + `f < n/3` + card ≤ n; monotone
  corruption pushes honesty back to all earlier times), run `vote_provenance` on its
  fin-vote, and read the tick's send shape: `src = s'.gjFrozen`, `tgt = J` with
  `J = ⟨chAva', s⟩` (then-branch) or `⟨s'.gjFrozen.ch, s⟩` (else-branch). Then-branch:
  `J.ch` is the vote-tick `chAva` fold output — bounded by the 2.3 hypothesis composed
  with `chi_le_mfc` on `simulate x5`. Else-branch — **the key simplification**: the
  target's chain *equals the source's* (`J.ch = C'.ch` where `C' = s'.gjFrozen` is the
  fin-vote's own source), `C'` is justified in the voter's tick view
  (`gjFrozen_justified` + `processProposals_gjFrozen_justified`), transfers into `V5`
  by `Relay` + `justifiedIn_mono`, and **link validity supplies the descent**
  (`C'.c < J.c` — no `chAva ⪰ gjFrozen` invariant needed, which is unprovable anyway);
  recurse. State the lemma with the 2.3∘Lemma-5 composite as a hypothesis
  (`∀` honest vote-tick at slot < ti, its `chAva` output `⪯ MFC2`), so the slot
  induction can discharge it. Still to write before the induction: the honest-quorum
  extraction counting lemma, `handler_vote_fin_content` (the vote send's `src`/`tgt`
  fields, exactly), and the `chAva`-fold upper bound (`chAva' ⪯` its own fold, for
  the then-branch's hand-off to 2.3).
- **Lemma 10, stage C2b-3a: the MFC agreements are assembled** (2026-08-05).
  `MfcEquiv.lean`: **`mfc_propose_agree`** (condition 2.1) and **`mfc_vote_agree`**
  (condition 2.2), each conditional on exactly the deep bounds the induction must
  supply. 2.1 takes skeleton equality plus *one* hypothesis — the 2.5 bound
  `GJ(V5).ch ⪯ mfc(V2, V2, fcs(V2,t−1).1, t)` — because the simple fast-confirmations
  coincide by congruence (`fastConfirmSimple_congr`), so either `fastconfirm`'s quorum
  branch makes the bases *equal* (no swap needed), or Algorithm 5's base is the
  justified chain — and then **both bases are prefixes of the simulated output** (2.5
  and `base_le_mfc`), hence comparable (`comparable_of_common_extension`), the
  GJ-branch condition orients them (`¬(GJ.ch ⪯ fcs.1)` forces `fcs.1 ⪯ GJ.ch`), and
  `mfc_base_swap` closes. This kills what looked like a missing-comparability gap: no
  ebb-and-flow interaction lemmas needed for 2.1. 2.2 takes the two frozen-base
  cross-bounds as hypotheses outright. Field projections of `components` are `rfl`
  (`components_mfc`/`_fastConfirmSimple`/`_gj`/`_prefixLe`) — unlike derived defs
  over `C`, which are not (`components_voteHits` needed `ext`).
- **Lemma 10, stage C2b-3: the attack plan** (2026-08-05, recorded before building).
  What remains, in dependency order, all in `MfcEquiv.lean` over `simulate x5`:
  1. **Skeleton equality from correspondence** — immediate: `voteSkel_eq_of_corr` on
     `viewCorr_of_tableDynEq` (2.1's pair) and `frozen_viewCorr` (2.2's frozen side).
  2. **Base bounds for `mfc_base_swap`** (the deep legs). For 2.1 at `propose(t)`:
     Algorithm 2's base `fastConfirmSimple(V2, t−1).1` is genesis or quorum-supported
     — a `2n/3` quorum is a `Majority` (numerator ≥ 2n/3 > n/2 bound via
     `numerator_skel` + skeleton equality transfers it into the `(V5, V5)` pair), so
     `le_mfc_of_majority` bounds it by the Algorithm-5 output; Algorithm 5's base
     `fastConfirm(V5, t−1).1` is either `fastConfirmSimple(V5, t−1).1` (same quorum
     argument into `(V2, V2)`) or `GJ(V5).ch` — the justified chain, which needs
     **condition 2.5**: `JustifiedIn n V5 J → J.ch ⪯ MFC2` — via the paper's route:
     `JustifiedIn` unfolds to a `2n/3` quorum of *fin-votes* with target `J`; an honest
     fin-vote's target chain is the sender's `chAva`-or-`gjFrozen.ch` at its vote tick
     (handler shape, `handler_vote_content`-style fact for the target field); by
     induction (2.3 at earlier slots) some Algorithm-2 confirmed chain `Ch^{vote(tk)}`
     dominates it; `chi_le_mfc` (Lemma 5's engine, on `simulate x5` through
     `sim_settingGA`) bounds that by the current MFC output. For 2.2 the same with the
     frozen bases (`chFrozen` writes are certified `chC`s — quorum — or Algorithm 5's
     `gjp.ch` — justified).
  3. **MFC agreement** — `mfc_congr` (skeleton-equal pairs, same base) composed with
     `mfc_base_swap` (cross-bounded distinct bases): 2.1 and 2.2 at every tick.
  4. **The slot induction**: strong induction on `k` (or on slots with an inner
     induction to the phase readings) carrying `TableDynEq x5 j` for all `j ≤ k` plus
     2.3/2.4's dominance facts; step by `tableDynEq_step` whose two obligations `hP`
     and `hV` are 3's agreements (hV via `simPick_eq_pick5`).
  5. Then Definition 9's rendering, Lemma 10's face, Lemmas 11–13.
  Note 2.3/2.4 (the `chAva` dominance chain) enter only through 2's fin-vote-target
  step; they are *cross-execution* statements (x5's `chAva` under some x2 `chi`)
  proved in the same induction — the paper's Case 1/2/3 analysis of line 12's three
  `chAva` sources (`chi_step2`'s Algorithm-5 analogue on `chAva`, to be written).
- **Lemma 10, stage C2: the correspondence layer** (2026-08-05). `MfcEquiv.lean` now
  holds the slot induction's running invariant and its step machinery:
  **`TableDynEq x5 k`** (every τ-key is `SDynEq` to its image — Definition 8,
  tablewise; reflexive at `k = 0`), `viewCorr_of_tableDynEq` (an `SDynEq` table makes
  every validator's two views `ViewCorr` — the shape the skeleton layer consumes), and
  **`tableDynEq_step`**: the invariant survives one step given exactly two per-phase
  facts at that step's tick — the propose-round fork choices agree (`hP`), and the
  simulated pick is the original's (`hV`). `hV` itself reduces (`simPick_eq_pick5`)
  to `ViewCorr` at the tick plus vote-round MFC agreement, via `voteHits2_corr`
  (corresponding views have equal hit sets — the filter reads only what `DynEq`
  preserves) and `components_voteHits` (the two algorithms' hit sets coincide at the
  instance — an `ext`, *not* `rfl`: the `Finset`s carry independently synthesized
  `DecidableEq` instances, and the match-compiled filters are not definitionally
  equal). Send-shape lemmas `handler_propose_send`/`handler_vote_content` pin both
  handlers' exact messages. Also proved: **`frozen_viewCorr`** — the two runs' frozen
  views correspond whenever the table has been `SDynEq` all along (both freeze their
  current views at the same merge ticks; phase lemmas `handler_merge_vFrozen`,
  `handler_vFrozen_quiet`, `handler2_vFrozen_quiet`), so `mfc_congr` has all its
  view-pair inputs for 2.1 (current×current) and 2.2 (frozen×current). **What remains
  for C2b-3**: the MFC agreements themselves — skeleton equality via
  `voteSkel_eq_of_corr` on the corresponding pairs, then `mfc_base_swap` with the
  2.5/2.6 justified-chain and quorum-majority *base bounds* (the deep legs: x5
  fin-vote-target facts, Lemma 5 on `simulate x5` through `sim_settingGA`) — and the
  slot induction assembling it all. Lean note: the h5-rewrite-then-cases pattern needs
  the x2 side handled by per-case `have e2 : … = …` equations (`show` + `simp only
  [simStep, h]` + occasional `rfl` for literal-`getElem` projections) — rewriting
  both sides at once makes `rw` motives ill-typed against `simStep`'s match.
- **Lemma 10, stage C2: the setting transfers to the simulated run** (2026-08-05).
  `Analysis/Proofs/Transfer.lean`: **`sim_settingGA : SettingGA Q S x5 → SettingGA Q S
  (simulate x5)`** — Lemmas 2–7 now run on the simulated execution. Label/time-shaped
  predicates carry over through `sim_time`/`sim_clock` and the label translation
  (`simLbl_tick_iff`/`_wake_iff`; spell bridge equations over `x5[i].time`, not
  `(x5.cfg i).time` — omega treats the two spellings as distinct atoms). `Synchrony`
  and `Relay` go through **table stability** (`tau_stable`): each τ-key is written at
  most once, at its own honest tick — a second tick re-sending the same message would
  share its reading (`reading_of_send_eq`: the message shape carries phase and slot,
  so the reading is determined; then `OneTickPerReading`), and an injected message's
  signer is corrupt, hence never awake at a later tick of its own
  (`MonotoneCorruption` + `AwakeHonest`). On top of stability: `view_image` (original
  views map into simulated ones under τ), `view_covered`/`sent_covered` (everything
  simulated is a τ-image). **Construction fix on the way**: simulated adversarial
  injections are now τ-routed (`⟨p, (τ ⟨p,m⟩).msg⟩`, sender preserved —
  `sim_table_sender`), not verbatim — a corrupted validator re-injecting its own old
  honest send would otherwise put a message in the simulated log that its deliveries
  never carry, and `Synchrony (simulate x5)` is *false*; the reverse collision
  (inject first, honest tick later) is impossible by `MonotoneCorruption` +
  `AwakeHonest`. Next (C2b): the τ-image is `SDynEq` at honest ticks — the mutual
  slot induction for conditions 2.1–2.7, now with both `SettingGA`s in hand.
- **Option B implemented: the nondeterministic vote pick** (2026-08-05, one session,
  far below the days estimated — the churn counts were low). The shape: `pickSet hits
  fallback` (hits, or the fallback alone when none — the paper's "if there is one, or
  `chMFC` otherwise") with `Components.voteHits`/`votePicks` (generic) and
  `voteHits2`/`votePicks2` (concrete); both handlers bind the vote chain from it —
  Algorithm 2 as a second `←` next to the `dot` blank, **Algorithm 5's handler is now
  `Set`-valued** and its `protocol.step` relational (`res ∈ handler`). Proof layer:
  `handlerCore`/`handler2Core` gain a `pick` parameter after `dot`; the inversions
  (`mem_handler_iff`, `mem_handler2_iff`) hand it over constrained
  (`pick ∈ votePicks…`); `tick_effect`/`tick_delta_send`/`emitted_step`(2)/
  `vote_provenance`(2) expose `∃ pk ∈ votePicks…`; `voteChoice` and
  `chainLe_getD_findSome` are *gone*, replaced by `mem_voteHits2` +
  `chainLe_of_votePicks2` (every admissible pick extends the fork-choice) and
  shape-only `handler2_vote_send_eq`/`_content` (`send = {vote pick ·· slot}`);
  Lemma 4's pinning now shows `voteHits2` is nonempty at `chp` and every hit is pinned
  by provenance — *simpler* than the `findSome?` version. Simulation: `exec5_tick`
  inverts a tick into `∃ pk ∈ votePicks`, `pick5` extracts it by choice (`dite` +
  `Classical.propDecidable` off tick labels), `exec5_succ` keeps its match shape via
  `pick5`+`handlerCore`, and the simulated tick runs at **`simPick`** — the original's
  pick when admissible in the simulated view, any admissible pick otherwise — keeping
  the construction total and every step legal; that `simPick = pick5` at honest ticks
  *is* condition 2.7's content, deferred to stage C where it belongs. Lean traps hit:
  (i) a derived `DecidableEq (Finset (Chain Tx))` baked into `pickSet`'s `if` makes
  every downstream `whnf` try to *evaluate* the emptiness test on symbolic views —
  deterministic timeouts three files away; pin `Classical.propDecidable` explicitly
  (`@ite _ _ (Classical.propDecidable _)`), same class as the `mfc_congr` kernel
  timeout; (ii) `honest_vote_unique`'s two same-tick sends now go through the log
  delta (`tick_sends_subsingleton5`: any reaction's send is subsingleton, whatever the
  pick) instead of handler-term determinism; (iii) `injection` auto-substituting
  closed the pinning goal by itself again (dropped `exact h1`).
- **Tenth finding: the vote phase's proposal pick is order-dependent, and Lemma 10 is
  false for the `findSome?` rendering** (2026-08-05; user decision: **option B**, the
  nondeterministic pick — fidelity to the paper's indefinite article over proof
  economy: option A would prove theorems about a protocol that hard-codes a
  fall-back-under-equivocation behaviour no arrival-order implementation has).
  Algorithm 2
  line 22–23 (and Algorithm 5's vote phase identically) reads "let ch := proposed chain
  from slot t extending chMFC and with ch.p = t, **if there is one**, or chMFC
  otherwise" — the paper does not say which chain when there are several (an
  equivocating Byzantine proposer can plant two filter-passing proposals). Both our
  handlers resolved the choice as `V.toList.findSome? …`: deterministic, but a function
  of `Finset.toList`'s arbitrary enumeration order, which is uncorrelated between two
  executions whose views merely correspond (Definition 8 preserves no order — and
  `Multiset.toList` is a `Quot`-representative choice, so even insertion order gives no
  handle). Consequence: Definition 9's condition 1/2.7 (honest votes carry *equal*
  chains) can genuinely fail for `simulate x5` — the two `findSome?` calls can pick
  different equivocated proposals — and **no simulated adversary can prevent it**:
  `Synchrony` (framework form: every `sent` message is in every awake view within `Δ`)
  forces both counterparts into every x2 view, since the transfers need `SettingGA` on
  x2; per-recipient suppression, mangled injections and delivery reordering were each
  checked and each is defeated by synchrony or by per-validator divergent picks. The
  paper avoids this because its validators process messages in *arrival order* and its
  adversary decision (iv) aligns the arrival orders of the two executions — an
  instrument our `Finset` views erase. Options: (A) make the pick order-independent in
  both algorithms — vote the unique filter-passing chain, fall back to `chMFC` on zero
  *or several* (deviates from arrival-order semantics only under equivocation, where
  the paper pins nothing; Lemma 4's uniqueness argument already gives the singleton in
  the honest-proposer case; smallest blast radius: `voteChoice` + 3 send lemmas + the
  Lemma-4 pinning site); (B) make the pick nondeterministic (the paper's indefinite
  article taken literally; Algorithm 5's step becomes relational — `exec5_succ` and
  `simulate` rework, `handler2Core` gains a pick parameter through ~4400 lines);
  (C) ordered views (framework change, heaviest, most faithful to arrival order).
- **Lemma 10, stage C2 opening: the base-swap engine** (2026-08-05). `Mfc.lean` gains
  `chainLe_antisymm` and **`mfc_base_swap`**: two `MFC` calls over the same view pair
  agree whenever *each base sits below the other call's output* — the four cases of
  `mfc_base_or_majority` close by `le_mfc_of_majority` and antisymmetry, entirely
  view-local. This is conditions 2.1/2.2's engine: Algorithm 5's propose-round base is
  `fastconfirm`'s (GJ-branch-substituted) output and Algorithm 2's is
  `fastconfirmsimple`'s, and the vote-round frozen chains diverge through the GJ
  lifts — the swap reduces "the fork choices agree" to the two ⪯-bounds, which the
  slot induction supplies from 2.5/2.6 (justified chains below the fork choice, via
  Lemma 5 on the simulated run) and quorum-vs-majority counting. The symmetric form
  was the key discovery: no comparability side-conditions in the lemma itself — the
  earlier asymmetric attempts needed quorum-intersection counting inside. **C2's
  remaining plan**: view-monotonicity/frozen-⊆-view for both executions (Majority's
  snapshot discipline), the x5 fin-vote-target facts, then the mutual slot induction
  (send-correspondence ⇒ view skeleta equal ⇒ `mfc_congr` + `mfc_base_swap` ⇒ MFC
  agreement ⇒ next slot's sends), stated over `simulate x5` with `SettingGA` on x5.
- **Definition 8 repaired** (user decision, 2026-08-05, the ninth finding's other
  half): `DynEq`'s propose clause frees everything but the proposed chain and slot —
  the paper frees only the GJ field, inconsistent with its own `fastconfirm`, whose
  GJ-branch substitutes the justified chain for `(chC, QC)`; since `fastconfirm` is
  finality-coupled by construction the whole pair is finality-*derived*. Nothing
  downstream loses strength (the transfers read only `chp` and the slot; the
  frozen-chain divergence is handled by bounding). The tighter substitution-aware
  alternative — free the pair only when `QC = none ∧ chC` equals the message's own GJ
  chain — is recorded in the docstring should full-strength condition 1 ever be
  wanted. Votes' clause is the paper's, verbatim.
- **Ninth authors'-note finding, and `ValidProposal5`** (user decision, 2026-08-05).
  Algorithm 5's `fastconfirm` GJ-branch emits `(GJ(V).ch, ∅)` — an *uncertified*
  nonempty `chC` — in every slot without a fast-confirm quorum (the ordinary
  partial-participation case), while the validity it inherits from Algorithm 2
  demands a certificate: **Algorithm 5 rejects its own honest proposals**, the fresh
  justified checkpoint never reaches voters' fin-vote targets through the propose
  path, and the finality pipeline's two-slot latency argument (Lemmas 17–18,
  Theorem 6) breaks in exactly the regime the branch serves. Also, such proposals
  differ from their Algorithm-2 counterparts in `chC`/`QC`, so Definition 8 (and
  Lemma 10's condition 1) is false as literally worded. Fix (validity half):
  **`ValidProposal5`** in `Spec/Components.lean` — `ValidProposal2` with a third
  certificate rung, `qc = none ∧ chC = gjp.ch ∧ JustifiedIn n V gjp` ("justification
  certifies"; evidence proportional to the claim: genesis/quorum/justification).
  Kept **separate from `ValidProposal2`**: sharing the widened clause is *unsound*
  for Algorithm 2 — its checkpoint field is the nondeterministic blank and honest
  fin-vote fields are unconstrained there, so justification over Algorithm-2 views is
  adversary-steerable and the widened clause revives the chain-smuggling attack the
  certificate check stops (the original Lemma-4 finding). `components.validProposal`
  now instantiates `ValidProposal5`; no proof fallout. The Definition-8 half of the
  finding (which fields count as finality-affected for proposes) is a separate
  decision, pending.
- **Lemma 10, stage C1: the skeleton congruences** (2026-08-05).
  `Analysis/Proofs/Equivalence.lean`: Definition 8's dynamic equivalence preserves
  exactly the **vote skeleton** — the `(signer, chain, slot)` triples (`voteSkel`) —
  and the whole fork-choice layer factors through it: `filLmd_fil1Exp` (the
  latest-vote filter is the identity after the expiry filter — all slots equal),
  `mem_votesFor_skel`, `numerator_skel` (Majority's numerator characterized on two
  skeletons **under the call sites' snapshot discipline** `Va ⊆ Vb` — the intersection
  is of message sets, which dynamic equivalence does not preserve, but any triple
  surviving both views' skeleton-expressible filters is realized by one message of the
  smaller view), `voters_skel`, `candidates_skel`, `support_skel`, `qcert_skel`, and
  the congruences `Majority_congr`, `fastConfirmSimple_congr` (chain *and*
  certificate), `mfc_congr`. `SDynEq`/`ViewCorr` render Definition 8's signed and set
  forms; `voteSkel_eq_of_corr` converts. Lean notes: `fastConfirmSimple` must be
  zeta-reduced with `simp only [fastConfirmSimple]`, not `unfold` (do-elaborated
  `have`-bindings again); and `mfc_congr` originally made the **kernel** time out —
  `if_pos`/`if_neg` rewriting inside the fold with `Majority`'s concrete decidability
  instances (an `abbrev`, so the counting unfolds) blows the proof term up;
  `set_option maxHeartbeats` does not govern the kernel. Fix: `foldl_mfc_congr`, the
  fold congruence over an **abstract decidable predicate**, instantiated at `Majority`
  once — elaborates and checks in seconds.
- **Lemma 10, stage B: the simulation is built** (2026-08-05).
  `Analysis/Proofs/Simulation.lean` has `simulate : Exec Pr5 S → Exec Pr2 S` — the
  Algorithm-2 execution induced by any Algorithm-5 execution, on the same schedule and
  label stream, exactly as designed (CONTEXT entry below): recursion over labels with
  each successor *defined as the framework's effect term*, so every step proof is
  shape-only; ticks take `handler2Core` at the fixed blank `simBlank = ⟨[], 0⟩`;
  deliveries route through the per-step correspondence table `τ` (updated at each tick
  to pair the two handlers' sends); adversarial injections carry over verbatim.
  Cheap invariants proved: `sim_time`, `sim_clock`, `sim_activeAt` (the two runs' clock
  faces and joining state agree), `sim_table` (`τ` is the identity or points into the
  simulated log), `sim_sent` (the `τ`-image of the original log is in the simulated
  log — the deliver steps' enabledness), and `sends_align` (the handlers send together
  or not at all: the conditions read only phase, proposer and `activeAt`). `DynEq` renders
  Definition 8. Lean notes, hard-won:
  - **A `def` whose body uses a section-variable `(x : Exec Pr S)` is silently
    dropped** — no error, the name simply does not exist afterwards (reproduced
    minimally; a plain `Nat` section variable works). This is why `Provenance2` binds
    `{x : Exec Pr2 S}` per-theorem everywhere. Explicit binders throughout.
  - `exec5_succ` resolves Algorithm 5's determinism into a per-label successor
    equation; the `spec`/`nodeStep_iff_exists`/`protocol_step_*` reduction chain must
    run in that order.
  - The record-literal-across-lines parse gotcha strikes in `refine ⟨{ state := …,
    \n send := 0 }, …⟩` too — anonymous constructors `⟨st, 0⟩` avoid it.
  Stage C remains: Definition 9's conditions as a slot induction over `simulate x5`
  (dynamic equivalence of views/sends, MFC agreement via 2.5/2.6, the `chAva`
  domination 2.3/2.4), then Lemma 10's face and the Lemma 11–13 transfers.
- **Lemma 10, stage A: Algorithm 5's spec aligned with Algorithm 2's** (2026-08-05).
  Lemma 10 (the Algorithm 5 → Algorithm 2 simulation, Appendix C) is formalized in
  three stages; its send-correspondence (Definition 9's condition 2.7) is false unless
  the two vote phases agree modulo finality fields, so the approved Algorithm-2
  findings had to reach Algorithm 5 first:
  - `Components.validProposal` now takes the **view** and is a `Prop`, instantiated
    with `ValidProposal2 n proposer` — whose definition *moved* from
    `Spec/Algorithm2.lean` into `Spec/Components.lean` (same name, same namespace, no
    proof fallout): the paper has one `valid([propose, …])` for both algorithms, the
    GJ-justification conjunct being Algorithm 5's separate line-30 check.
    `processProposals`' condition became a Prop-`if` (mirroring `processProposals2`;
    `Algorithm5.lean` opens `Classical`).
  - `proposedNow` in Algorithm 5's vote phase gains the proposer-identity and
    `sortedChain` conjuncts (findings 3–4), through a new `Components.sortedChain`
    field instantiated with `slotsIncreasing`.
  - the `chAva`/`chFin` vote-phase updates sit behind the joining check (finding 5),
    exactly as Algorithm 2's `chi`; the listening state (`processProposals`' writes)
    stays unconditional.
  **The stage-B/C design** (recorded before building): `simulate : Exec Pr5 S →
  Exec Pr2 S` by plain recursion over the label stream — `Execution` is just
  `(cfg, lbl, init, step)`. Same schedule, same tick/wake/advance labels; the
  Algorithm-2 ticks take the deterministic core with a fixed blank; `deliver` labels
  are routed through a **step-indexed correspondence table** `τ` updated at each tick
  (the framework's `deliver p m` requires `m ∈ sent`, so x₂ must deliver its own
  counterpart of each x₅ message — the paper's adversary decision (iv)); adversarial
  injections carry over verbatim (`Msg` is shared). The construction is total and
  unconditional, with cheap invariants (time/clock/activeAt equality, `τ`-image
  containment in `sent₂`) proved alongside; Definition 9's MFC-equivalence
  (conditions 2.1–2.7) is then a **slot induction on the completed execution**,
  reusing the Appendix-A machinery on x₂ — the paper's inductive construction of the
  adversary and our post-hoc equivalence proof are the same argument, but splitting
  them keeps `Provenance2`'s `Exec`-quantified lemmas applicable (they cannot run on
  a partially built execution).
- **Appendix B is proved: Lemmas 8–9** (2026-08-04). `Analysis/Proofs/Finality.lean`
  (faces in `Analysis/Lemmas.lean`): Lemma 8 (a justified checkpoint at or past a
  finalized one extends it, or `n/3` validators are slashable) and Lemma 9 (two
  conflicting finalized chains ⇒ `n/3` slashable). **Assumption-free** — no schedule,
  no synchrony, no corruption bound: the `f ∈ [0, n]` regime, rendered by assuming
  nothing; purely view-local Finset counting. New spec pieces in `Spec/Components.lean`:
  `E1`/`E2` (the slashing conditions, p. 9 — E1 double vote: distinct fin-votes with one
  target slot; E2 surround), `SlashableIn` (two fin-votes by one signer in the evidence
  view violating E1 ∨ E2 — *validity not required*: misbehaviour is evidence
  regardless), `linkVoters` (extracted from `link` for the counting), and — a fix —
  **`link` now carries the paper's fin-vote validity** `C.c < C'.c ∧ C.ch ⪯ C'.ch`
  (p. 9): the earlier rendering omitted it, admitting links into checkpoint slot `0`
  and chain-incoherent links, and Lemma 8 is false without it (its proof reads the
  source chain's prefix bound and the counter ordering from validity). Proof shape:
  the paper's minimality contradiction became a strong induction on `c_j`, unwinding
  the justification chain one link at a time; all three evidence sites (same-slot
  double justification, the `c_j = c_f + 1` double vote, the surround) close through
  `slash_of_links` — `third_inter` (two `2n/3` quorums over ≤ `n` validators share
  `n/3`) plus fin-vote extraction (`mem_linkVoters`). Lemma 9 is Lemma 8 twice via
  `Nat.le_total` and `comparable_of_common_extension`. `chainLe_trans` moved from
  `Provenance2` to `Mfc` (it is view-local; Finality imports only Mfc). Lean notes:
  a `Checkpoint` projection of a literal (`(⟨chf, cf⟩ : Checkpoint _).c`) is an opaque
  atom to omega — re-`have` the hypothesis at the reduced type first; `cases` on
  `JustifiedIn … ⟨ch, c⟩` substitutes the components through the index unification.
- **Directory reorganized: `Spec/`, `Paper/`, `Analysis2.lean`** (user request,
  2026-08-04). `Examples/StsMultisetLog/majorum/` now has: **`Spec/`** (Components, Algorithm2,
  Algorithm5, Assumptions, Security — the protocol and its model); the proof layer at
  the root (Mfc, Provenance, Provenance2); **`Analysis2.lean`** (namespace
  `Majorum.Analysis2`) with the Appendix-A results *in full* — the real proofs of
  Lemmas 2–7, Theorem 1, and Theorem 2's split faces (`theorem2_safety`,
  `theorem2_liveness`, `theorem2_liveness_txpool`) plus the assembled `theorem2`
  conjunction; and **`Paper/`** with the paper-facing lists — `Paper/Lemmas.lean` (one
  theorem per numbered lemma) and `Paper/Theorems.lean` (the paper's actual theorems:
  proved `theorem1`/`theorem2` and the remaining `Prop` shells), **every proof a single
  call** into `Analysis2` so the lists read without proof noise; split versions are
  banned from `Paper/Theorems.lean` by convention. Canonical names stay
  `Majorum.lemmaN`/`theoremN` (the Paper faces); the full proofs are
  `Analysis2.…`. Namespaces did not move with the files (`Spec/*` keeps
  `namespace Majorum`), so the reorg was import-path churn only; the lakefile's
  `Majorum.+` glob needed nothing. Lean notes: scoped notation declared in
  `Examples.StsMultisetLog.majorum` is active inside the sub-namespace `….Analysis2` (entering a nested
  namespace opens its ancestors); a docstring-block regex for programmatic edits must
  be tempered (`(?:(?!-/)(?!/--).)*`) or it silently swallows whole theorems between
  two docstrings — one mangled build caught it.
- **Theorem 2 is fully proved: the liveness half** (2026-08-04). `Theorems.lean` has
  `theorem2_liveness` (the chain fact: past slot `t`, once `2κ` slots and a round have
  gone by, every validator active at that round confirms a chain extending some honest
  window proposal from `[t+1, t+κ]` — the paper's `Tconf = 8κΔ + Δ`) and
  `theorem2_liveness_txpool` (Definition 2's shape: any transaction pooled by a round
  of slot `t` is in a block of the confirmed chain — the issue-2 statement-level
  mempool shell: `memTx`/`poolSet` parameters, pool monotonicity, and `hcover`
  rendering `Extend`'s contract). New pieces:
  - **`ActiveAtRound`** (`Assumptions.lean`): the paper's `H_r` at an arbitrary round —
    some voting round *strictly* before `r` opened the activity window and the
    validator stayed awake through `r`. The strictness is the intra-round
    interleaving rendering (states are sampled between events; the paper's atomic
    round `r` includes its own writes), shifting the paper's bounds by one round.
    The overnight plan's state-level rendering (`Awake ∧ activeAt ≤ time`) was
    abandoned: awake-at-a-point does not recover the awake *span* the argument needs
    (wake events mark tick-preceding transitions only — `WakePrecedesTick` — not every
    sleep/awake flip of the schedule), while the schedule-level span plugs directly
    into `activeAt_le_voting` and `Diligent`.
  - **`le_chi_of_honest_proposal`** (`Provenance2.lean`, the engine): the activity
    window contains a covered vote round of slot `s' ≥ tp + κ` (`max tw (tp + κ)`);
    the tick exists (`TimeDiverges`/`Diligent`), its joining check is open
    (`activeAt_le_voting`), so the writer is `Active` (`active_of_open_join`); the
    fork choice sits above `chp` (`le_mfc_at_vote2`) and the slot-indexed prefix
    *retains* it (`le_kappaPrefix_of_stale` — issue 1's payoff); the fold lands at or
    above `chp` — the kept-old case is comparable with the prefix through the fork
    choice by **Lemma 5's own engine** (`chi_le_mfc` at `a = b = j`), which closes
    what would otherwise be an unknowable old chain. Persistence to `a` walks
    `chi_step2`: later κ-deep writes retain `chp` the same way; a fast-confirm write
    adopts a chain comparable with `chp` (honest supporter + vote uniqueness), and the
    regressive direction `fq.1 ⪯ chp ⪯ chi` is exactly what the **line-23 condition**
    blocks (issue 3's payoff) — `chi_step2`'s adopt disjunct now carries the condition's
    negation for this purpose.
  - Mfc: `le_kappaPrefix_of_stale` (a sorted prefix ≥ κ slots stale survives the cut;
    via `takeWhile_append_of_all` + `slot_le_proposedAt_of_mem`), `mem_takeWhile_pred`.
  All four Theorem-1/2 results audit to `propext, Classical.choice, Quot.sound`.
- **Paper-style prefix notation** (user request, 2026-08-04): `Components.lean` defines
  scoped `⪯` for `chainLe` and `≺` for the new `chainLt` (strict prefix,
  `chainLe a b && !chainLe b a`). Specs (`Components`, `Algorithm2`) and the
  lemma/theorem statements use the notation; the proof layers keep the named constant
  (goals still *display* with `⪯`, since notation is surface syntax over the same
  term — the swap is elaboration-neutral, which is also why the handler/`handler2Core`
  alignment was unaffected).
- **Issue 1 of the liveness roadmap is settled: `kappaPrefix` is slot-indexed**
  (2026-08-04, "push through"). `Components.kappaPrefix kappa t ch` is now
  `ch.takeWhile (·.slot + κ ≤ t)` — the paper's p.4 definition `(·)⌈κ,t` (longest prefix
  with `p ≤ t − κ`) on the sorted chains the fork choice produces; the `+ κ ≤ t`
  spelling avoids `Nat` truncation, so below `t = κ` nothing qualifies, matching the
  paper's `p ≤ t − κ < 0`. This replaced the count-based `take (length − κ)`: equally
  strong for Lemma 5's absorption, materially different for Theorem 2's liveness (an
  honest proposal from `κ` slots back survives the slot-indexed prefix regardless of
  block counts — the paper's `chp ⪯ (MFC)⌈κ,ti` step; count-based would need a
  chain-growth argument the paper never makes, and once-per-κ proposals only give κ
  blocks in κ² slots). Algorithm 5's `Components.kappaPrefix` field became
  `Nat → Chain → Chain` (the paper's line 12 is the same slot-indexed rule); the
  instantiation `kappaPrefix := kappaPrefix kappa` is textually unchanged. New Mfc
  lemmas: `kappaPrefix_nil_of_lt` (below `κ`, genesis), `mem_takeWhile_pred` (no
  Mathlib lemma for "takeWhile members satisfy the predicate" was found —
  `List.mem_takeWhile_imp` does not exist here), and `kappaPrefix_le_of_close`
  restated: the absorption now argues the first block past the proposal carries a
  later slot and so fails the prefix test (`proposedAt_lt_head_append` on the
  `takeWhile` prefix itself — no `length_sub_le_span` arithmetic).
  **`HonestProposalWindow` moved with it**: quantification starts at `t = κ` (the
  boundary slot's prefix can retain a slot-`0` block, so the absorption needs a
  windowed proposal there too — below `κ` the prefix is empty and no window is
  needed), and gains `1 ≤ tp` (the paper's window at `t = κ` reaches slot 0;
  `lemma4`'s machinery assumes `1 ≤ t`, so slot-`0` proposals are excluded in the
  hypothesis instead — implied anyway for `t > κ`). Consequence documented in the
  def's docstring: at `κ = 1` the `t = κ` instance is unsatisfiable and Lemma 5 is
  vacuous — degenerate for the paper too (w.o.p. needs κ large); the alternative, if
  ever needed, is `lemma4` at `t = 0` (its base case simplifies: no previous-slot
  votes, genesis frozen chain). The master's short branch simplified
  (`kappaPrefix_nil_of_lt` replaces the length arithmetic; `mfc_vote_ok`'s
  `proposedAt` bound is no longer consumed there), the absorption's `hclose` became
  `ti ≤ tp + κ` off the window directly, and everything else — `lemma5`, `lemma7`,
  `theorem1`, `theorem2_safety` — compiled untouched. **All three liveness blockers
  are now closed**; what remains for Theorem 2's liveness half is proof work: the
  round-indexed activity rendering (`Awake ∧ activeAt ≤ time`), the
  first-active-vote-tick lemma, the `chp ⪯ chi` persistence induction over
  `chi_step2`, and the statement-level mempool shell.
- **Seventh authors'-note finding, and a spec change: Algorithm 2's line 29 needs
  Algorithm 5's line-23 condition** (user decision, 2026-08-04: "write it like line 23 of
  Algorithm 5"). Algorithm 2's fast-confirm write is a plain `Chi ← fastcand`;
  Algorithm 5's counterpart (line 23) reads `if chAva ⪰̸ fastcand then chAva ←
  fastcand`. Without the condition, **Theorem 2's liveness is false**: with `|H_s| =
  2n/3 − f` honest actives (Constraint 1 allows it for any `f < n/3`), all honest
  slot-`s` votes extend the window's proposal `chp` (Lemma 4), and the `f` corrupt vote
  for an old strict prefix `P ⊊ chp` — `support(P) = |H_s| + f = 2n/3` is a quorum
  while nothing above `P` clears `2n/3 − f`, so `fastcand = P` and line 29 regresses a
  `Ch` the κ-deep rule had already pushed `⪰ chp`; at `ri = fconf(s)` the confirmed
  chain misses `txpool^r`, violating Definition 2. The paper's "fast confirmation does
  not interfere" paragraph proves only *comparability* (the quorum's `> n/3` honest
  members extend both) — the gap is invisible in Lemma 7, whose `|H| ≥ 2n/3`
  hypothesis makes `chp` itself quorum-supported. Safety never noticed either way
  (`P ⪯ chp`; Lemma 5's fconf case covers both branches). The handler now requires:
  `chi := if chainLe fq.1 s.chi then s.chi else fq.1` under the certificate check.
  Fallout was three small proofs (`handler2_fastconfirm`'s RHS, a case split in
  `chi_step2` — its *statement* is unchanged, the keep-branch lands in the "untouched"
  disjunct — and a `chainLe_trans` in `le_chi_at_fconf`); `chi_le_mfc`, `lemma5`,
  `lemma7`, `theorem1`, `theorem2_safety` compile untouched. Lean note: the
  multi-line record-update parse gotcha again — `{ state := if … else s, send := 0 }`
  across lines fails; hoist the `if` into a `let`.
- **Issue 2 of the liveness roadmap is settled: statement-level mempool** (user
  decision, 2026-08-04, option A). No protocol change. `Block.txs : Tx` stays an
  abstract payload and `pool : Nat → Tx` keeps the reading "the body an honest slot-`t`
  proposer packs" — faithful because the paper's `txpool` is global and read-uniform, so
  the honest body *is* a function of the slot (instantiate `Tx` at a transaction-set
  type). The liveness theorem, when stated, proves the chain fact `chainLe chp Ch`; the
  paper's `txpool^r ⊆ Ch` conclusion is a corollary shell over statement-level
  parameters `memTx : τ → Tx → Prop`, `poolSet : Time → Set τ` with two hypotheses —
  `poolSet` monotone, and coverage `tx ∈ poolSet (4Δt) → memTx tx (pool t)` (the
  rendering of `Extend`'s contract). Matches `Security.lean`'s existing
  `(mem)`/`(pool)` vocabulary. Rejected: a concrete mempool in the protocol
  (`Block.txs : Finset τ`, `extend` packing `txpool(propose t)`) — since `Tx` is
  abstract it adds nothing over the instantiation, and the paper does not specify
  whether `Extend` deduplicates, so agnosticism is the more faithful position.
- **Sixth authors'-note finding: "Property 1" is cited but never stated**
  (2026-08-04). Theorem 2's proof says "Due to Lemma 6 and Property 1, chp includes all
  of the transactions in txpool^{propose(tp)}"; the string "Property 1" occurs nowhere
  else in the paper. The intended content is `Extend`'s specification (p. 4, "The
  Protocol"): for `ch.p < t`, `Extend(ch, t)` extends `ch` to length `t` and includes
  all of `txpool^{propose(t)}` — *unspecified* for `ch.p ≥ t`. The pairing with Lemma 6
  decodes as: Lemma 6 (`MFC^{propose(t)}.p < t`) is what puts the fork-choice output
  inside `Extend`'s specified domain. Our development already mirrors this exactly:
  `slotsIncreasing_extend` needs `proposedAt ch < t`, which is `ch.p < t`.
- **Theorem 2: the safety half is proved; the liveness half is blocked on three
  modelling decisions** (2026-08-04). `Theorems.lean` has `theorem2_safety : SettingGA →
  1 ≤ κ → HonestProposalWindow → ∀ a vi b vj, the two confirmed chains are comparable` —
  the paper's "we now show safety" paragraph verbatim (a common later vote tick, Lemma 5
  twice, prefixes of one chain are comparable; neither validator's honesty needed). The
  **liveness half** (`Tconf = 8κΔ + Δ`: an honest proposal within the window is `⪯` every
  honest `Ch` a couple of κ-spans later, carrying its `txpool`) is *not stated*, for
  three reasons that are decisions rather than proof work — the roadblock the overnight
  mandate said to stop at:
  1. **The κ-deep prefix is slot-indexed in the paper, count-based in this model.** The
     paper's p.4 definition: `ch⌈κ,t` is the longest prefix with `ch′.p ≤ t − κ`; our
     `kappaPrefix κ ch = ch.take (ch.length − κ)` drops the last κ *blocks*. For Lemma 5
     the two agree in strength (the count-based absorption went through), but for
     liveness they differ materially: with slot-indexing, an honest `chp` proposed at
     `tp ≤ ti − κ` *survives* the prefix regardless of how few blocks sit above it,
     which is exactly the paper's Theorem-2 step `chp ⪯ (MFC^{vote(ti)})⌈κ,ti`; with
     count-indexing that step needs `≥ κ` blocks above `chp`, i.e. a chain-growth
     argument the paper never makes (and which the once-per-κ window is too weak to
     supply — it gives one block per κ slots, so κ blocks take κ² slots). Switching the
     spec to `takeWhile (·.slot + κ ≤ t)` (equal to the paper's definition on the sorted
     chains the fork choice produces) is the faithful fix; it eases Lemma 5's absorption
     for `t > κ` but re-opens its `t ≤ κ` boundary — there the prefix can retain a
     genesis-era block, the length shortcut no longer empties it, and the window must
     reach down to slot 0 (the paper's Lemma-1 window `[t−κ, t)` does include slot 0;
     ours starts at `tp ≥ 1` because `lemma4`/`of_propose` assume `1 ≤ t`). So the
     switch drags in either slot-0 proposals (extending Lemma 4 to `t = 0`) or a
     genesis convention.
  2. **`Property 1` / `txpool` has no rendering.** The model's `pool : Nat → Tx` is one
     fixed transaction per slot (`extend` appends `⟨t, pool t⟩`); the paper's liveness
     conclusion "`chp` includes all of `txpool^r`" needs a mempool: a time-indexed *set*
     of pending transactions, an assumption that honest proposers include it
     (Property 1), and a membership predicate over chains.
  3. **`GAT`/`GlobalAwake` is not woven into the activity sets.** The liveness statement
     quantifies over `H_{ri}` for *every* round `ri` past the confirmation delay, which
     is only nonempty-and-stable under `GlobalAwake`; `SettingGA` does not include it
     (safety never needed it), and the joining-protocol arithmetic for "the first active
     round of `vi` at or after `vote(t + 2κ)` is a vote round" is new machinery.
  Each is a spec-level choice worth discussing before building; none blocks anything
  currently proved.
- **Theorem 1 (Reorg Resilience) is proved** (2026-08-04): `Theorems.lean` has
  `theorem1 : SettingGA → 1 ≤ κ → HonestProposalWindow → (honest propose of chp in slot
  tp) → ∀ a vi, chainLe chp x[a][vi].st.chi ∨ chainLe x[a][vi].st.chi chp` — the
  paper's "chp does not conflict with Ch^{ri}_i" (`Security.Conflicts` unfolded),
  following the paper's proof exactly: pick `sj > max(tp, slot(ri))` (concretely
  `max tp (x[a].time / 4Δ) + 1`), `Sleepiness` at `sj+1` makes `Active(sj)` inhabited,
  `TimeDiverges`+`Diligent` produce an active `vj`'s vote tick there, Lemma 4's
  machinery (`ave_of_honest_proposal` + `le_mfc_at_vote2`) puts `chp` below that tick's
  fork choice, Lemma 5 puts the confirmed chain below the same fork choice, and two
  prefixes of one chain are comparable (`comparable_of_common_extension`). Proved
  theorems live at the end of `Theorems.lean` in a **fresh namespace scope**: the
  statement block's `variable {Msg : Type}` (the abstract renderings range over any
  message type) would otherwise shadow Algorithm 5's `Msg` inductive — the file closes
  and reopens `namespace Majorum` for the proved section. The `Security.lean`
  `ThmReorgResilience` rendering stays a `def : Prop`: its hypothesis row (Wellformed ∧
  Network ∧ Sleepiness ∧ Resilience, no tick discipline, no window) predates `SettingGA`
  and is not what the proof needs. Lean note: `ring` is not imported in that file —
  `omega` closes the Int rewrites; a projection like `.2` off an applied lemma does not
  pin implicit args appearing only in the other conjunct (`vi`, `a`, `b` passed
  explicitly).
- **Lemma 5 is proved** (2026-08-04): `Lemmas.lean` has `lemma5 : SettingGA → 1 ≤ κ →
  HonestProposalWindow → (∀ a vi, ∀ propose/vote round b of vj ∈ Active(sj) at or after
  x[a].time, chainLe x[a][vi].st.chi MFC_b)` — both round shapes as a conjunction, `vi`'s
  honesty *not* assumed (all state is handler-conformant; the adversary only injects
  messages). `HonestProposalWindow` (defined in `Provenance2.lean`) is **Lemma 1
  de-probabilized**: every slot `t > κ` has an honestly-proposed slot in `[t−κ, t)`;
  taken as hypothesis wherever the paper says "w.o.p.". `1 ≤ κ` is needed by the paper
  too (its window is empty at κ = 0). The proof replaces the paper's minimality
  contradiction with a strong induction on the index of the last `chi` write
  (`Provenance2.chi_le_mfc`), over the step shape `chi_step2`:
  - *κ-deep write* (conditional on the joining check — see the spec-change entry): the
    writer is active (`active_of_open_join`), its fork choice `M` is slot-sorted with
    `proposedAt ≤ slot − 1` (`mfc_vote_ok`, the invariant's fork-choice block extracted
    with `honest_vote_chain` closing what the induction hypothesis used to). For slots
    `≤ κ` the one-block-per-slot bound (`slotsIncreasing_length_le`) makes the κ-prefix
    empty — **no window needed below κ**, which is what lets the hypothesis start at
    `κ < t`. Past κ, the window's proposal `chp` satisfies `chp ⪯ M`
    (`le_mfc_at_vote2` off `ave_of_honest_proposal`) and absorbs the prefix
    (`kappaPrefix_le_of_close`; `proposedAt chp = tp` by provenance), and `chp` reaches
    every later fork choice (Lemma 4's machinery + `le_mfc_at_propose_of_ave`).
  - *fast-confirm write* (unconditional, safe: a current-view quorum): the next slot reads
    the quorum directly (`le_mfc_at_vote_of_quorum` — Lemma 3's base case extracted —
    and the new `le_mfc_at_propose_of_quorum`), later slots via `ave_propagate`.
  New helper `le_mfc_at_propose_of_ave` closes the propose-round with the tick's *real*
  base: an honest supporter of a nonempty base has one slot vote
  (`honest_vote_unique2`) extending both the base and the lock, so they are comparable
  and `le_mfc_at_propose2`/`base_le_mfc` split. Lean notes: `Nat.le_of_mul_le_mul_left`
  / `Nat.lt_of_mul_lt_mul_left` for slot-from-time cancellation (omega cannot divide);
  omega misses `[].length` unless `List.length_nil` is in the simp set; a two-element
  `foldl` inverts by `List.foldl_cons/nil` + `split_ifs at h` with the branch-shaped
  `first`-dispatch.
- **The κ-deep rule runs only once active** (2026-08-04, fifth authors'-note finding,
  spec change): `handler2`'s vote branch now updates `chi` behind the joining check
  `s.activeAt ≤ r` (the same check that already conditioned the vote *send*). **Lemma 5 is
  false without it**: the κ-deep rule reads the *frozen* snapshots, and a validator
  that slept through `merge(t−1)` and wakes at `vote(t)` κ-deep-confirms from stale
  ones. Concretely: the adversary feeds vi, before it sleeps, a merge-view "quorum" for
  a long junk chain (a corrupt slot-proposal can append many junk blocks at once, and
  `n/3 honest + f corrupt` support suffices for `2n/3`); the network drops that fork,
  every later fork-choice is junk-free, but the woken vi writes
  `kappaPrefix κ (junk)` into `Ch` — incomparable with every later `MFC`. With the
  condition, a chi-updating vote tick implies activity, activity implies the freeze is
  fresh (`frozen_at_vote_tick`), and freshness is what the paper's Case 1.1 silently
  uses (its honest-window proposal is comparable with the fork-choice only through a
  shared slot-(t−1) honest voter, which a stale freeze does not provide). The paper
  leaves a re-joining validator's `Ch` unspecified; the joining protocol's "sends
  nothing until active" must be read as covering the frozen-state-dependent
  confirmation rule too. The **fast-confirmation update stays unconditional**: it reads the
  *current* view, and a `2n/3` quorum there is network-anchored (its honest majority
  part reaches every active's next merge freeze by `Δ`), so it is safe for silent
  validators — and `lemma7` keeps its any-ticking-validator statement.
- **Lemma 6 is proved** (2026-08-04): `Lemmas.lean` has `lemma6 : SettingGA → 1 ≤ t →
  x[a].time = 4Δt → Awake a w → proposedAt (mfc … propose-view … t) < t`. Stated for any
  *awake* validator (weaker than the paper's `H_propose(t)`), and for `1 ≤ t` only: the
  paper's `B_genesis.p < 0` sentinel makes its `t = 0` instance true, ours has
  `proposedAt [] = 0` — convention divergence, not content. The engine is
  `Provenance2.mfc_propose_ok` (extracted from Lemma 4's base case, which now calls it):
  the propose-round fork-choice output is genesis or a prefix of a slot-`t−1` honest
  vote's chain — quorum case by `f < n/3` (`exists_honest_sender`), majority case by
  Constraint (1) (the actives vote by `activeVotesExtend_of_le_mfc'` and deliver by
  synchrony, so the majority's supporters cannot all be corrupt) — and the honest-chain
  invariant bounds that vote's chain. Extraction gotcha: the new theorem was inserted
  between `set_option maxHeartbeats … in` and the docstring it governed, silently
  re-attaching the option to the new theorem and starving the old one — timeouts, not
  errors, were the symptom.
- **Chains must be slot-sorted: `slotsIncreasing`** (2026-08-04, fourth authors'-note
  finding, follow-up to the proposer-identity check): the paper's chain model grows by
  one block per slot with strictly increasing slots built in; our blocks are free lists
  of `⟨slot, txs⟩`. Without a structural check, a corrupt proposer feeds honest voters a
  slot-garbled chain and Lemma 5's κ-window arithmetic and Lemma 6 are false.
  `Components.slotsIncreasing` (pairwise `<` on consecutive block slots) joins
  `ValidProposal2` and the handler's `proposedNow` filter (spec change); `Mfc.lean` gains
  the structure suite (`slotsIncreasing_of_prefix`, `proposedAt_le_of_prefix`,
  `proposedAt_lt_head_append`, `length_sub_le_span` — one block per slot bounds length by
  slot span — `kappaPrefix_le_of_close`, `slotsIncreasing_extend`, `proposedAt_extend`).
- **The honest-chain invariant `honest_vote_chain`** (2026-08-04, the largest proof in
  `Provenance2.lean`, `maxHeartbeats 4000000`): every honest vote's chain is
  `slotsIncreasing` with `proposedAt ≤` the vote's slot. Strong induction on the *log
  index* of the vote (`Nat.strong_induction_on`): the voter's fork-choice output is
  genesis (trivial) or rides through the frozen fast-confirmation / certificate check /
  majority — each case produces an *earlier honest vote* whose chain the output prefixes
  (quorum: `f < n/3` gives an honest supporter; majority: Constraint (1) plus
  actives-do-vote, `activeVotesExtend_of_le_mfc'`, the slot-generic production that also
  covers slot 0), and the induction hypothesis at the earlier index plus the prefix
  closure lemmas finish. Slot 0 needs its own case (`chFrozen_at_slot0_tick`: nothing is
  frozen before the first vote round). Lemma 4's base case then *derives* the honest
  proposal's structural validity proposer-side instead of assuming it.
- **Lemma 7 is proved** (2026-08-04): `Lemmas.lean` has `lemma7 : SettingGA → 1 ≤ t →
  2n ≤ 3·|Active(t)| → (honest propose of chp in slot t) → any validator's fconf(t)-tick
  leaves chi ⪰ chp`. Composition: `lemma4` at `t' = t` (every active votes `chp`) +
  `Provenance2.le_chi_at_fconf` (the `2n/3` activity bound turns those votes into a
  quorum for a `⪰ chp` candidate in every fconf view — `fastConfirmSimple_length_ge` +
  `supported_comparable` pick it or something longer and comparable). Stated for *any*
  validator ticking at `fconf(t)`, not only `H_fconf(t)`: the tick's enabling supplies
  awakeness.
- **Spec files hold only spec** (2026-08-04, extending the 2026-08-03 convention):
  `handler2Core`, `mem_assign`, `mem_pure_exists` and `mem_handler2_iff` moved from
  `Algorithm2.lean` to the top of `Provenance2.lean` — the deterministic core is a proof
  device, not part of the protocol. The one obligation that had leaned on it,
  `protocol2.total`, now uses a self-contained `handler2_nonempty` (feasibility is a spec
  obligation, so it stays; proved directly on the `Set` structure — note `unfold
  handler2` leaves do-elaborated `have`-bindings that block `split_ifs`; `simp only
  [handler2]` reduces them). `Algorithm5.lean` was already clean.
- **The nondeterministic-assignment style IS the main version** (2026-08-04). The
  comparison attempt (`Nda/`, see below) was promoted at the user's request and the
  directory deleted: `Algorithm2.lean`'s `handler2` is now the `Set`-valued one-`do`-block
  handler (`←` = nondeterministic assignment for the blank finality fields at their use
  sites, `return` per branch, `attribute [local instance] Set.monad`), `protocol2`'s tick
  step ties in by membership, and the former parametric handler survives as
  **`handler2Core`** — the deterministic core the proof layer works over, recovered by
  `mem_handler2_iff : res ∈ handler2 … ↔ ∃ dot, res = handler2Core … dot …` (with the
  `mem_assign`/`mem_pure_exists` bridge lemmas). `Provenance2.lean` changed mechanically:
  the six tick sites rewrite with `, mem_handler2_iff`, and every handler reference is
  spelled `handler2Core`. `lemma2` unchanged.
- **`Nda/`: the nondeterminism-style comparison, concluded** (2026-08-04, user
  request; directory since promoted into the main files and removed — see the entry
  above; history at commits 3cdb5bf/f5b0638). What it established, kept for the record:
  a `Set`-monadic handler and the `∃`-at-the-step form prove the same theorems; the
  monadic form costs one inversion lemma plus a one-token rewrite per tick-analysis
  site, and pays for itself in pseudocode-fidelity (and more so if further choice
  points — any received valid proposal, fork-choice tie-breaks — ever go
  nondeterministic, each `←` replacing a hand-hoisted `∃`). Lean notes:
  - `Monad Set` is **not** a global instance; enable per file with
    `attribute [local instance] Set.monad` (`import Mathlib.Data.Set.Functor`).
    Downstream files consuming only `∈`/`∃` statements need neither.
  - Don't `simp [Bind.bind, Pure.pure]` to invert monadic membership — unfolding the
    instance projections recurses (maxRecDepth even at 8192). Prove tiny bridge lemmas
    (`mem_assign : res ∈ (do let x ← univ; pure (f x)) ↔ ∃ x, res = f x` via
    `rw [Set.bind_def]; simp [Set.pure_def, eq_comm]`, and `mem_pure_exists` for
    deterministic branches with a vacuous `∃`) and close each `split_ifs` branch by
    `exact` — never running simp over the big branch bodies.
- **The validator count is structural** (user decision, 2026-08-03): `Params` has **no
  `n` field** — the paper's `n` is `Fintype.card Node`, the universe every schedule and
  view is already indexed by, so `n = |validators|` holds by construction instead of via
  an assumption field (the earlier `SettingGA.validators : Q.n = n` is gone).
  `Resilience` is now `S.CorruptionBounded Q.f ∧ 3 * Q.f < Fintype.card Node`, and
  `Lemmas.lean` instantiates Algorithm 2's quorum threshold with the structural count:
  `local notation "Pr2" => protocol2 Q (Fintype.card Node) kappa pool proposer`. The
  Provenance2 helpers stay generic over the threshold `n` (they never need the tie).
  Why this matters (from the discussion that triggered it): `Sleepiness` bounds `|A|`
  against the *universe* (`|A| < card/2` via `MonotoneCorruption`), while quorum
  thresholds count against *`n`*; with the two untied, `Resilience` was doing work that
  the paper's model gives for free — with the tie, sleepiness alone would already
  preclude a fully-corrupt `2n/3` quorum (`n/2 < 2n/3`), though the proofs keep using
  `Resilience`'s direct `f < n/3` bound.
  How the vote-round half went through, for reuse in Lemmas 3–5:
  - **Producing the vote** (not just constraining it): `TimeDiverges` + `exists_time_eq`
    reach `voting(t+1)`, `Diligent` ticks it, `handler2_vote_send` shows the tick votes
    `proposedNow.getD chMFC ⪰ chMFC`, and `tick_emits`/`tick_time` place the message in
    the log at the right time.
  - **The joining check stays open** (`activeAt_le_voting`): the framework's wake event
    is enabled only on a sleep→awake transition (`p ∉ S.awake (time − 1)`), so a
    validator awake through the activity window has no wake strictly inside it; a wake at
    or below the window's bottom activates by `voting(t+1)`
    (`activationRound_le_voting`). Induction from `activeAt = 0` at `Init`.
  - **Frozen-state provenance**: the merge tick exists inside the window; between
    `merge(t)` and `voting(t+1)` no reading has the merge or vote phase except the two
    endpoints (`phase_pins_reading` — nonlinear div/mod arithmetic via explicit
    `Nat.mul_le_mul_left` + `Nat.mul_succ` expansions before `omega`), and
    `OneTickPerReading` excludes the endpoints, so `frozen_step2` persistence gives
    `vFrozen = view@merge(t)` and `chFrozen = fastConfirmSimple(view@merge(t), t).1` at
    the vote tick (`tick_state` + `handler2_merge`).
  - **`chFrozen` comparable with `ch`** on both write paths, by one counting argument
    (`hsupported`): a `2n/3`-supported chain's supporters contain an honest sender
    (`exists_honest_sender`), whose slot-`t` vote is unique (`honest_vote_unique2`) and
    equals its official vote, which extends `ch` by hypothesis —
    `comparable_of_common_extension`. Path 1: `fastConfirmSimple_fst_cases` (genesis, or
    quorum-supported). Path 2: `processProposals2_chFrozen` (fold invariant: the initial
    value, or a `ValidProposal2`-checked `chC`, whose view-checked certificate hands the
    same counting its `≥ 2n/3` signers at slot `t`).
  - **The majority**: official votes delivered into *both* the frozen and live views
    (`Synchrony` applied at `merge(t)` and at `voting(t+1)`), filter survival
    view-parametric (`mem_votesFor_of_official`), containment view-parametric
    (`voters_containment` — visible slots pinned to `t` by the equality `fil1Exp`), and
    Constraint (1) closes. Then the dichotomy: `chFrozen ⪯ ch` → `le_mfc_of_majority`;
    `ch ⪯ chFrozen` → `base_le_mfc` + transitivity.
  Lean notes from this stretch:
  - A structure literal/update `{ s with a := x, b := y }` **must not break the line
    after a field's comma** at these indentations — `unexpected identifier; expected '}'`
    (hit twice); keep record updates on one line.
  - `simpa using h` can fail with a "Type mismatch: After simplification" whose displayed
    types are *identical* (the connection `exact` needed was destroyed by simp's
    normalization); plain `exact h` succeeded. Try `exact` before diagnosing instances.
  - `injection h with h1 …` on a constructor equation **substitutes** when a side is a
    local variable, closing the very goal the equation was wanted for — a following
    `exact h1` errors with "No goals to be solved"; drop it.
  - Casting pitfall in window arithmetic: `push_cast` on the goal turns `↑(sl * (t+1))`
    into `↑sl * (↑t + 1)` while Nat-side hypotheses keep the atom `sl * (t+1)` — `omega`
    then sees unrelated atoms and fails; *don't* `push_cast`, and let `omega` relate the
    casts of the shared Nat atoms itself.
- **`FIL_1-exp` is an equality filter — the user's resolution (2026-08-03) of the
  same-round-delivery problem.** The problem: at the vote round, `mfc`'s denominator
  `voters(V, t+1)` counted every visible vote with slot `≥ t`; an honest validator active
  at `t+1` but not at `t` (woken this slot) can tick at `voting(t+1)` before `v`, and the
  adversary can deliver its slot-`(t+1)` vote into `v`'s view at the same time value —
  in the denominator, never in the numerator (`vFrozen` predates it). Equation (1) says
  nothing about fresh `t+1`-actives, so a mass wake-up made the majority test — and the
  lemma — **false in the model as it stood** (counterexample: 10 actives at `t`, 90 fresh
  at `t+1`, zero corruption: denominator 100, numerator ≤ 10). Two candidate fixes:
  - a `DeliveryLags` execution predicate (`∀ i p m, m ∈ x[i][p].view → ∃ k,
    x[k].time < x[i].time ∧ m ∈ x[k].sent` — "nothing is seen in the round it was
    sent"), rendering the lock-step semantics the paper's Appendix-A counting
    (`S(V) ⊆ H_{vote(t)} ∪ A`) implicitly relies on; **rejected by the user** in favor of:
  - **`fil1Exp V t` keeps exactly the previous slot's votes** — predicate
    `t = msgSlot sm.msg + 1`, was `t ≤ msgSlot sm.msg + 1` (the paper's literal "discards
    votes older than one slot", which also keeps current-slot ones). At every `MFC` call
    site (`MFC(…, t+1)` at propose and vote) only slot-`t` votes count, so every counted
    voter is corrupt-or-`Active(t)` *structurally*, however delivery is scheduled — no
    timing assumption at all. Under the paper's lock-step rounds the two readings
    coincide at the call sites (a slot-`t` vote is not visible at `vote(t)` or earlier;
    adversarial future-slot votes fall under `A` either way), so this is a
    robustness-of-encoding choice, not a protocol change — but it does diverge from the
    paper's *text*, worth an erratum note alongside the Lemma-2 dichotomy hole. The
    change made the proofs shorter: the filter itself pins visible slots to `t`, so the
    `filLmd` survival and voter-containment arguments in `le_mfc_at_propose`(`2`) dropped
    their `voting_le_of_vote_mem`(`2`) timing steps, and `filLmd` over an equality-filtered
    set is vacuous (all slots equal — nothing is "later").
- **A hole in the paper's own proof of Lemma 2**, found the same way (2026-08-03; worth
  reporting to the authors). The proof asserts "clearly
  `chfrozen^{propose(t+1)} = Bgenesis ∨ chfrozen ⪰ ch`". Counter-scenario: `n = 100`,
  `f = 30`, `|H_{vote(t)}| = 40` — Constraint (1) holds (`40 > 30`). The 40 honest vote
  extensions of `ch`; the adversary's 30 vote an extension of `m`, the prefix of `ch` one
  block short, branching off after `m`. Then `support(m) = 70 ≥ 2n/3` while
  `support(ch) = 40 < 2n/3`, so `fastconfirmsimple` at `merge(t)` returns `m` (and the
  `fastconfirm` wrapper passes it through when `GJ` is still genesis): `chfrozen = m`,
  neither genesis nor `⪰ ch`. The *lemma* survives, because what the argument actually
  needs is `chfrozen` **comparable** with `ch`: if `chfrozen ⪯ ch` then `ch` is still a
  legal MFC candidate and Case 1's majority argument applies unchanged; if
  `chfrozen ⪰ ch`, Case 2. The formalization will use the comparability dichotomy.
- Two pairs of statements **coincide** (`ThmReorgResilienceGA`/`FFG`,
  `ThmDynamicAvailabilityGA`/`FFG`) because the two algorithms they distinguish are not
  modelled. Kept separate so they can diverge later.
- `the framework's flat multiset-log flavour.Models.Majorum` is a different thing: the *network and adversary model*,
  already expressed. This directory holds the *claims*.
