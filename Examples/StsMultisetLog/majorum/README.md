# Majorum, in Lean — what is proved and what is not

A formalization of *Majorum* (arXiv:2601.03862v1) over the framework's flat multiset-log flavour. Lib `MajorumExample`, checked by
`make majorum` from the repository root.

This file is the honest inventory. [FINDINGS.md](FINDINGS.md) collects the places where the
paper itself needed repair, in the paper's order. The working log — decisions, dead ends, Lean
gotchas — is [CONTEXT.md](CONTEXT.md); the paper-facing statements are in
[Analysis/Lemmas.lean](Analysis/Lemmas.lean) and
[Analysis/Theorems.lean](Analysis/Theorems.lean), each a one-line delegation so
they can be read against the paper without reading a proof.

## What is proved

| Paper result | Face |
|---|---|
| Lemmas 2–7 (Appendix A, Algorithm 2) | `lemma2` … `lemma7` |
| Lemmas 8–9 (Appendix B, accountable safety) | `lemma8`, `lemma9` |
| Lemmas 10–14 (Appendix C.1, the transfer and availability) | `lemma10` … `lemma14` |
| Lemmas 15–18 (Appendix C.2, finality) | `lemma15` … `lemma18` |
| Theorem 1 (reorg resilience, Algorithm 2) | `theorem1` |
| Theorem 2 (dynamic availability, Algorithm 2) | `theorem2` |
| Theorem 3 (reorg resilience, Algorithm 5) | `theorem3`, `theorem3_reorgResilient` |
| Theorem 4 (dynamic availability, Algorithm 5) | `theorem4`, `theorem4_dynamicallyAvailable` |
| Theorem 5 (accountable safety) | `theorem5` |
| Theorem 6 (liveness) | `theorem6_liveness_of_low` / `_case1` / `_case2`, each with a `_txpool_` companion |
| Theorem 7 (secure ebb-and-flow) | `theorem7` |

`make majorum` runs a textual check that no `sorry`, `admit` or `native_decide` appears
anywhere under `Examples/StsMultisetLog/majorum`, then builds the lib. There are no `axiom` declarations of
our own.

## Not proved: Lemma 1

**Lemma 1 has no face and cannot have one.** It is the proposer-election lemma — *"with
overwhelming probability … there exists at least one pair of consecutive slots in which honest
proposers are elected"* — and there is no probability layer in the model. It enters as a
hypothesis in two shapes, and everything downstream is conditional on them:

- `MfcEquiv.HonestProposalWindow5` — one honest proposal per `κ` slots. Carried by
  essentially every Algorithm-5 result.
- `EbbAndFlow5.HonestProposerPairs W` — honest proposers at two consecutive slots, within `W`
  slots of any given time. Theorem 6 needs the pair; Theorem 7 needs the window, because
  without a bound on the wait there is no confirmation time to state.

## Not proved: three statements that have no instance

`Analysis/Theorems.lean` renders each paper theorem twice: as an abstract `def … : Prop` in
the paper's own vocabulary, and (where proved) as a theorem. Three of the abstract ones have
no instance:

- **`ThmLiveness`** (Theorem 6) — **not provable as written.** It assumes one honest proposal
  and fixes the round at `4Δ(t+3) + 2Δ`, while Cases 1 and 2 of the proof both need the
  slot-`(t+1)` proposer honest too, and Case 2 only lands at `fconf(t+4)`. Closing it means
  changing what it says.
- **`ThmReorgResilienceGA`** (Theorem 1) — hard-codes `Q.proposing`, the propose round, so the
  fifteenth finding's repair (below) is not expressible in it.
- **`ThmDynamicAvailabilityGA`** (Theorem 2) — quantifies over executions under four named
  assumptions where `theorem2` needs `SettingGA`'s full bundle, and being message-type
  agnostic it cannot name the honest-proposal window the proof consumes.

The other four abstract renderings do have instances: `ThmAccountableSafety` (`theorem5`),
`ThmReorgResilienceFFG`, `ThmDynamicAvailabilityFFG` and `ThmEbbAndFlow` (`theorem7`).

## Proved, but not the paper's claim

Everything here is the **deterministic shadow** of the paper's statements. Read as the paper's
claims, the theorems below are weaker; two are weaker in ways specific to them.

- **`w.o.p.` is dropped** everywhere it appears, and `negl(λ)`, `negl(κ)` with it. Theorem 5
  is the exception: Definition 6 carries no probability layer, so `theorem5` *is* the paper's
  claim.
- **`O(κ)` and `O(Δ)` became explicit parameters** — `tconf`, `slack`, `W`. A statement
  quantified over those is not one asserting a bound of the right order exists.
- **Signatures are idealized**; accountable safety's "cryptographic proof" is a function from
  the message log to a set of validators (`culprits5`).
- **Theorem 3 uses a stricter honesty window than Definition 5.** The definition asks reorg
  resilience of a chain proposed by a validator honest at `propose(t)`; `theorem3_reorgResilient`
  asks it of one honest at `voting(t)`. The propose-round version is **false** — the adversary
  is adaptive, so a proposer honest when it proposes can be corrupted before the vote round and
  equivocate, splitting the honest votes. This is the fifteenth authors'-note finding; the
  argument is written out in [CONTEXT.md](CONTEXT.md) but is *not* mechanized (no Lean
  counterexample).
- **Theorem 6's Case 2 concludes a slot later than the paper.** It finalizes `(chp', t+2)`, so
  its conclusion holds from `fconf(t+4)`, where the paper states one bound `4Δ(t+3) + 2Δ` for
  all three of its cases. The paper's own Case 2 applies Lemma 18 at slot `t+1`, which has the
  same shape, so the single bound looks optimistic by a slot rather than this rendering being
  weak — but that is an observation, not a proof.

## Where the model deviates from the paper's pseudocode

Each was a deliberate decision, recorded with alternatives in [CONTEXT.md](CONTEXT.md). They
mean the theorems are about *this* protocol, which is not quite the paper's:

- **Finalization counts fin-votes by source, not by a common target.** `FinalizedIn C` asks
  for `C` justified plus a supermajority of fin-votes *out of* `C` into slot `C.c + 1`, each
  with whatever target it chose, where the paper asks for a supermajority *link* — one shared
  target. Without this,
  Lemma 18's finalization half and Theorem 6's Case 2 are false as the paper states them (the
  thirteenth and fourteenth findings).
- **Algorithm 5's certificate write sits behind validity alone**, matching Algorithm 2's fold,
  where the paper nests it inside the justification condition (the eleventh finding).
- **Algorithm 2's fast-confirm write got Algorithm 5's line-23 condition**; without it
  Theorem 2's liveness is false (the seventh finding).
- **The vote phase's proposal pick is nondeterministic**, following the paper's indefinite
  article rather than fixing an arrival order (the tenth finding).

## Not checked: axiom dependencies

a sibling protocol model, a sibling protocol model and another formalization each compile an
`AxiomAudit.lean` that pins which axioms the named results depend on. **Majorum has none.** So
"no new axioms" here means only that the sources declare no `axiom` and the build has no
`sorry` — not that anything checks the results rest on the three standard Mathlib axioms.
Adding an audit over the faces in `Analysis/Lemmas.lean` and `Analysis/Theorems.lean` is the
obvious next hardening step.
