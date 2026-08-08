# Majorum — findings for the authors

Places where *Majorum* (arXiv:2601.03862v1) says
something the formalization could not use as written: a statement that does not follow from its
hypotheses, a definition that is cited but never given, or pseudocode whose literal reading
makes one of the paper's own lemmas false.

Collected here because they were scattered through [CONTEXT.md](CONTEXT.md), which stays the
working record — each entry below names the log entry it came from, greppable by its headline.
Nothing here is a complaint about rigour in general: most of these are one-line repairs, and
several are things the paper's proofs clearly *intend* and only omit to say.

**On the numbering.** The ordinals were assigned informally as findings turned up, and 1, 2
and 8 have no labelled entry — not in the log and not in its git history. So the numbering has
holes; the twelve below are all of them that were ever labelled. They are listed in the
paper's own order, not by number.

**Status** distinguishes what is checked from what is argued:

- *mechanized* — the formalization contains the proof, or the repaired spec plus the proofs
  over it;
- *argued* — reasoned out and written down, no Lean counterexample built;
- *resolved* — turned out not to be a defect on a closer reading.

---

## Definitions

### Definition 5 (Reorg Resilience) asks honesty one round too early — 15th

Definition 5 (p.5) asks reorg resilience of "any chain proposed in slot `t ≥ t_reorg` by a
validator **honest in `propose(t)`**". That reading is false. The adversary is adaptive (§2.1,
"An adaptive probabilistic poly-time adversary `A` may corrupt up to `f` validators"), so a
proposer honest when it proposes may be corrupt by `voting(t)` and can send a second,
individually valid slot-`t` proposal. Synchrony puts both in every active validator's view by
the vote reading, the vote phase picks *any* qualifying proposal chain, so the honest votes
split — and with them split, nothing pins later fork choices to the first chain. Constraint (1)
does not close it: its stated purpose is to stop the adversary corrupting *voters* "immediately
after the voting phase", not the proposer before one.

The paper's proofs never use the propose-round reading — Lemma 4 says "let `t` be a slot with
an honest proposer `v_p`", unqualified, and its base case argues from *the* proposal, singular.

*Repair*: read Definition 5 at `voting(t)`, or "honest throughout slot `t`". That is what
`theorem3_reorgResilient` assumes and what every Algorithm-5 result here assumes of a proposer.
**Status: argued.** Log entry: "Fifteenth authors'-note finding: Definition 5's honesty window
is one round too early".

### `valid([propose, …])` is never defined — 3rd

Only checkpoint-link validity is defined. The proposal predicate is needed, and needed to
include a proposer-identity check: without one, a chain the adversary withholds from the
proposer can outgrow `chC_p` and lift `chfrozen` above anything bounded by `chp`, which breaks
the paper's own base-case equality `chfrozen^{vote(t)} = chC_p`. Structural signing makes the
check sound — a sender field cannot be forged and relay preserves the signer.

*Repair*: `ValidProposal2` in `Spec/Components.lean`, with the identity check. **Status:
mechanized** (Lemmas 2–3 survive with a one-conjunct adjustment on the certificate path). Log
entry: "Lemma 4 is proved" (the finding is stated inside it).

### Definition 8 / Lemma 10's condition 1 is false as literally worded — 9th

Algorithm 5's `fastconfirm` GJ-branch emits `(GJ(V).ch, ∅)`, an *uncertified* nonempty `chC`,
in every slot without a fast-confirm quorum. The validity Algorithm 5 inherits from Algorithm 2
demands a certificate, so **Algorithm 5 rejects its own honest proposals** in exactly the
partial-participation regime that branch exists to serve; and such proposals differ from their
Algorithm-2 counterparts in `chC`/`QC`, so Definition 8's dynamic equivalence — and Lemma 10's
condition 1 with it — does not hold as written.

*Repair*: `ValidProposal5` adds a third certificate rung, `qc = none ∧ chC = gjp.ch ∧
JustifiedIn n V gjp`, and Definition 8 is read up to that. **Status: mechanized.** Log entry:
"Ninth authors'-note finding, and `ValidProposal5`".

### "Property 1" is cited but never stated — 6th

Theorem 2's proof says "Due to Lemma 6 and Property 1, `chp` includes all of the transactions
in `txpool^{propose(t_p)}`"; the string "Property 1" occurs nowhere else in the paper.

The intended content is recoverable: it is `Extend`'s specification (p.4, "The Protocol") —
for `ch.p < t`, `Extend(ch, t)` extends `ch` to length `t` and includes all of
`txpool^{propose(t)}`, and is *unspecified* for `ch.p ≥ t`. The pairing with Lemma 6 then
decodes as: Lemma 6 (`MFC^{propose(t)}.p < t`) is what puts the fork-choice output inside
`Extend`'s specified domain. **Status: resolved** — nothing had to be assumed, and the
development mirrors the decoding exactly: `slotsIncreasing_extend` requires
`proposedAt ch < t`. Log entry: "Sixth authors'-note finding: 'Property 1' is cited but never
stated".

---

## Lemmas

### Lemma 5 is false unless the κ-deep rule runs only once active — 5th

The κ-deep confirmation rule reads the *frozen* snapshots. A validator that slept through
`merge(t−1)` and wakes at `vote(t)` reads stale ones, so the adversary can feed it a merge-view
"quorum" for a long junk chain before it sleeps — a corrupt proposal can append many junk
blocks at once, and `n/3` honest plus `f` corrupt clears `2n/3` — let the network drop that
fork, and the woken validator writes `kappaPrefix κ (junk)` into `Ch`, incomparable with every
later `MFC`.

*Repair*: the `chi` update sits behind the joining check `activeAt ≤ r`, the same check that
already conditions the vote *send*. Then a `chi`-updating vote tick implies activity, activity
implies the freeze is fresh, and freshness is what the paper's Case 1.1 silently assumes.
**Status: mechanized** (spec change). Log entry: "The κ-deep rule runs only once active".

### Lemma 5's κ-window arithmetic and Lemma 6 need chains to be slot-sorted — 4th

The paper's chain model grows one block per slot with strictly increasing slots built in; a
free list of `⟨slot, txs⟩` blocks has no such guarantee, and without a structural check a
corrupt proposer feeds honest voters a slot-garbled chain.

*Repair*: `Components.slotsIncreasing` (pairwise `<` on consecutive block slots) joins
`ValidProposal2` and the handler's `proposedNow` filter. **Status: mechanized** (spec change).
Log entry: "Chains must be slot-sorted: `slotsIncreasing`".

### Lemma 10 is false for the natural reading of the vote phase's proposal pick — 10th

The vote phase says to vote for *a* qualifying proposal. Read as "the first one found"
(`findSome?` over the view), the choice is arrival-order dependent, and the two algorithms'
picks can differ under equivocation — which makes Lemma 10 false.

*Decision*: keep the paper's indefinite article, i.e. a nondeterministic pick (`votePicks`),
rather than hard-code a fall-back behaviour no arrival-order implementation has. **Status:
mechanized** under the nondeterministic reading. Log entry: "Tenth finding: the vote phase's
proposal pick is order-dependent".

### Lemma 18's finalization half does not follow from its hypotheses — 13th

Lemma 18 concludes that `chp` is justified at slot `t+1` *and finalized at slot `t+2`*.
Finalizing `(chp, t+1)` by the paper's definition needs a supermajority **link** out of it, so
the slot-`(t+2)` fin-votes must agree on their *target* as well as their source — and the proof
argues only the source ("all honest validators vote with source `(chp, t+1)`"). The target is
each voter's own available chain, and a **corrupt slot-`(t+1)` proposer** can split the honest
slot-`(t+1)` votes so that different views fast-confirm different chains (`n/2` honest plus
`f < n/3` corrupt clears `2n/3` either way), leaving the available chains, and so the targets,
different. Lemma 18 assumes nothing about the slot-`(t+1)` proposer.

*Repair taken* (user decision): count fin-votes by **source**, not by a common target —
`FinalizedIn C` is `C` justified plus `2n ≤ 3·|sourceVoters V C (C.c+1)|`. Under it Lemma 18
holds with one honest proposer, as stated. Counting sources is also what the slashing
conditions support: accountable safety survived with one added lemma whose witness is
parametric in each voter's own target. **Status: mechanized.** Log entry: "Thirteenth
authors'-note finding".

---

## Theorems

### Theorem 2's liveness is false without Algorithm 5's line-23 condition — 7th

Algorithm 2's fast-confirm write is a plain `Ch_i ← fastcand`, where Algorithm 5's counterpart
(line 23) reads `if chAva ⋡ fastcand then chAva ← fastcand`. Without the condition the write
**regresses** the confirmed chain, and Theorem 2's liveness is false. Concretely, with
`|H_s| = 2n/3 − f` honest actives — Constraint (1) allows it for any `f < n/3` — all honest
slot-`s` votes extend the window's proposal `chp` (Lemma 4) while the `f` corrupt vote for an
old strict prefix `P ⊊ chp`. Then `support(P) = |H_s| + f = 2n/3` is a quorum and nothing above
`P` clears `2n/3 − f`, so `fastcand = P`, and line 29 pulls `Ch` back below a chain the κ-deep
rule had already pushed to `⪰ chp`. At `r_i = fconf(s)` the confirmed chain then misses
`txpool^r`, against Definition 2.

The gap is easy to miss twice over: the paper's "fast confirmation does not interfere"
paragraph proves only *comparability* — the quorum's `> n/3` honest members extend both chains —
and it is invisible in Lemma 7, whose `|H| ≥ 2n/3` hypothesis makes `chp` itself
quorum-supported. Safety never notices either way, since `P ⪯ chp`.

*Repair* (user decision, "write it like line 23 of Algorithm 5"): Algorithm 2 gets the
condition. **Status: mechanized** (spec change). Log entry: "Seventh authors'-note finding, and
a spec change: Algorithm 2's line 29".

### Theorem 6's Case 2 inherits the thirteenth finding, and Theorem 6's hypotheses cannot repair it — 14th

Theorem 6 assumes honest proposers at `t` and `t+1` and splits on `GJ^{propose(t)}_p.c`. Its
Case 2 applies Lemma 18 *at slot `t+1`*, so under the paper's link-based finalization the
slot-`(t+3)` fin-votes would need an honest proposer at `t+2` — which Theorem 6 does not assume.
The attack is the thirteenth finding's, one slot later.

*Retired* by the same source-counting change: Lemma 18 then needs only its own slot's honest
proposer, and Case 2 follows from Theorem 6's stated hypotheses. One residue remains, and it is
about the paper's round bound rather than its hypotheses: Case 2 finalizes `(chp', t+2)`, so its
conclusion holds from `fconf(t+4)`, while the paper states `r ≥ 4Δ(t+3) + 2Δ` for all three
cases. The paper's own Case 2 has the same shape, so the single bound looks optimistic by a
slot. **Status: mechanized** (Case 2 is proved; the round-bound observation is *argued*). Log
entry: "Fourteenth authors'-note finding".

---

## The two proposal folds

### The folds' asymmetric conditions can freeze divergent chains — 11th

Algorithm 5 nests its certificate write inside the justification condition where Algorithm 2's
fold performs it on validity alone. A certified proposal carrying an *unjustified* checkpoint
then freezes divergent chains in the two algorithms, which surfaces in no-majority
configurations as divergent *votes* — against Lemma 10's condition 1.

*Decision* (user, option A): split the condition, so the `chfrozen ← chC_p` write sits behind
`valid ∧ chfrozen ⪯ chC_p` alone — exactly Algorithm 2's condition — while the `GJ_frozen`
writes stay behind justification. Every certificate write is then common to both folds. The
noted alternative was weakening Definition 9 instead. **Status: mechanized** (spec change). Log
entry: "Eleventh finding resolved: option A, the split condition".

### Line 33's relation is on checkpoints, not chains — 12th, resolved

Read off page 11 with the glyph codes, the block is: line 33 `GJ_p ≥ GJ^frozen_i`, line 35
`if ch^frozen_i ⋡ GJ_p.ch`, line 37 `if ch^frozen_i ⪯ ch_Cp`. So the relation on **checkpoints**
is `≥` while the two on **chains** are `⪰`/`⪯`; the paper does not mean chain extension at line
33, and the slot-only rendering (`acc.gjFrozen.c ≤ gjp.c`) is right. **Status: resolved, no spec
change.** One consequence stands: the paper's Lemma 17 Case 2 needs
`GJ^{frozen,merge}_i.ch ⪯ chC_p`, which `GJ_p ≥ GJ^{frozen,merge}_i` does not give; it is
bridged here with `justified_chains_comparable`. Log entry: "Twelfth finding resolved by the
pseudocode itself".

---

## Not a finding, recorded to avoid confusion

**Definition 2 (Live protocol) quantifies over validators *active* in the later round** — the
paper's `H_r`, and §2.1 is explicit that "awake, asleep, and active apply only to honest
validators". The formalization had rendered liveness over *awake* validators, which is
strictly stronger and false of any protocol with a joining delay. The paper is right and the
rendering was wrong; `LiveActive` in `Spec/Security.lean` now follows the paper. Log entry:
"Definition 2 is over the paper's `H_r`, and majorum now says so".
