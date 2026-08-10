import Examples.StsMultisetLog.majorum.Spec.Assumptions
import Examples.StsMultisetLog.majorum.Spec.Security
import Examples.StsMultisetLog.majorum.Spec.Algorithm5
import Examples.StsMultisetLog.majorum.Spec.Components
import Examples.StsMultisetLog.majorum.Spec.Algorithm2
import Examples.StsMultisetLog.majorum.Analysis.Proofs.Mfc
import Examples.StsMultisetLog.majorum.Analysis.Proofs.Provenance
import Examples.StsMultisetLog.majorum.Analysis.Proofs.Provenance2
import Examples.StsMultisetLog.majorum.Analysis.Proofs.Analysis2
import Examples.StsMultisetLog.majorum.Analysis.Proofs.Finality
import Examples.StsMultisetLog.majorum.Analysis.Lemmas
import Examples.StsMultisetLog.majorum.Analysis.Theorems

/-!
# Majorum, as an `StsMultisetLog`-framework model

Source: **arXiv:2601.03862v1** —
*Majorum: Ebb-and-Flow Consensus with Dynamic Quorums*, D'Amato, Saltini, Tran, Vonlanthen
and Zanolini, arXiv:2601.03862v1, 7 Jan 2026, to appear at FC'26. Statements cite its
numbered theorems and definitions, which are stable, rather than lines of the Overleaf
working copy at the paper's own source — that copy was the original source and
agrees with v1 on every statement rendered here, but it is not included here and its line
numbers move.

**Proved** (2026-08-06): Lemmas 2–7 and Theorems 1–2 for Algorithm 2, under `SettingGA`
plus the de-probabilized Lemma 1 (`HonestProposalWindow`) and `1 ≤ κ`; Appendix B —
Lemmas 8–9, the finality component's accountable-safety counting, assumption-free
(`f ∈ [0, n]`); and **Appendix C.1 in full for Algorithm 5** — Lemmas 10–14 and
Theorems 3–4 (reorg resilience and dynamic availability), which carry the Appendix-A
results across to the full protocol through the MFC-equivalent Algorithm-2 run Lemma 10
constructs. Appendix C.2 (partial synchrony) is under way: **Lemmas 15–16 and Theorem 5** are proved,
along with Theorem 6's safety half and Definition 7's finalized-prefixes-available
conjunct. What remains of the paper is Appendix C.2's liveness chain — Lemmas 17–18,
Theorem 6's liveness half and Theorem 7 — whose statements are the `Prop`s in
`Analysis/Theorems.lean`.

## Layout

The **spec** — the protocol and its model — lives in `Spec/`; the **paper-facing
results** in `Analysis/`, one theorem per numbered lemma/theorem, each proved by a
single call so the lists read without proof noise; the proof layer sits under
`Analysis/Proofs/`.

* `Spec/Assumptions` — the à la carte hypothesis groups (and `SettingGA`, the bundled
  Appendix-A setting). Majorum proves its theorems under *different* assumptions, so
  there is deliberately no single model predicate.
* `Spec/Security` — Definitions 4–7: dynamic availability, reorg resilience, accountable
  safety, secure ebb-and-flow. Definitions 1–3 (safe, live, secure) are
  protocol-independent and live in `Framework.StsMultisetLog.Execution`.
* `Spec/Algorithm5` — **Algorithm 5 itself**: Majorum as a `Framework.StsMultisetLog.Protocol`,
  with the fork-choice and finality machinery abstracted into `Components`.
* `Spec/Components` — the functions the algorithms call, defined: chains as lists of
  blocks (with the `⪯`/`≺` prefix notation), the three vote filters, `MFC`
  (Algorithm 1), `fastconfirmsimple`, `kappaPrefix`, and justification, finalization,
  `GJ` and `GF` (§4).
* `Spec/Algorithm2` — the probabilistically-safe TOB-SVD variant with fast
  confirmations, the dynamically available component on its own. **The proved lemmas
  and theorems are about this algorithm**; its messages are Algorithm 5's with the
  paper's "·" placeholder in the finality fields, chosen nondeterministically.
* `Analysis/Proofs/Mfc` — the view-local proof layer: vote filters, sender-counted majorities, what
  `MFC` returns, and the chain-structure suite for the κ-arithmetic.
* `Analysis/Proofs/Provenance` — execution-level helpers for Algorithm 5, and the protocol-generic
  pieces (`emitted_of_mem_sent`, `exists_time_eq`, …).
* `Analysis/Proofs/Provenance2` — the execution layer for Algorithm 2: provenance, the joining-check
  machinery, the honest-chain invariant, the Lemma-2 halves, each lemma's base case,
  and the Lemma-5/Theorem-2 engines.
* `Analysis/Proofs/Analysis2` — the Appendix-A results assembled in full: the real proofs of the
  numbered lemmas and theorems, including Theorem 2's split faces
  (`theorem2_safety`, `theorem2_liveness`, `theorem2_liveness_txpool`).
* `Analysis/Proofs/Finality` — Appendix B in full: Lemmas 8–9, `slash_of_links` and the
  E1/E2 evidence machinery, all view-local.
* `Analysis/Proofs/Simulation`, `Analysis/Proofs/Transfer`, `Analysis/Proofs/Equivalence`,
  `Analysis/Proofs/MfcEquiv` — Appendix C.1's transfer layer: the Algorithm-2 run built by
  replaying an Algorithm-5 run's schedule (`simulate`), its compliance, Definitions 8–9,
  and Lemmas 10–13. `MfcEquiv` holds Lemma 10's grand induction.
* `Analysis/Proofs/Finality5` — Appendix C.2: the fin-vote invariants (Lemma 15), the
  accountable-safety assembly (Theorem 5), and the finalized chain's order facts (Lemma 16,
  safety, and the prefix relation to the available chain).
* `Analysis/Proofs/Availability5` — Appendix C.1's results about Algorithm 5 itself:
  Lemma 14 and Theorems 3–4, over the order facts for `chainava` (`chAva_comparable`,
  `chAva_mono`) that the paper's proofs use silently.
* `Analysis/Lemmas` — **one theorem per numbered lemma of the paper**, and nothing else;
  proofs are one call into `Proofs/Analysis2`.
* `Analysis/Theorems` — the paper's theorems: the proved ones (`theorem1`, `theorem2`,
  one-call proofs) and the remaining statements as `Prop`s.

**Read the caveats in `Spec/Security.lean` before trusting the `Prop` statements.**
The probability qualifier lives in `HonestProposalWindow` for the proved results and is
silently dropped in the unproved `Prop` renderings; asymptotic bounds (`O(κ)`, `O(Δ)`)
become explicit parameters.
-/
