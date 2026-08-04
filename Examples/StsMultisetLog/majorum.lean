import Examples.StsMultisetLog.majorum.Spec.Assumptions
import Examples.StsMultisetLog.majorum.Spec.Security
import Examples.StsMultisetLog.majorum.Spec.Algorithm5
import Examples.StsMultisetLog.majorum.Spec.Components
import Examples.StsMultisetLog.majorum.Spec.Algorithm2
import Examples.StsMultisetLog.majorum.Mfc
import Examples.StsMultisetLog.majorum.Provenance
import Examples.StsMultisetLog.majorum.Provenance2
import Examples.StsMultisetLog.majorum.Analysis2
import Examples.StsMultisetLog.majorum.Paper.Lemmas
import Examples.StsMultisetLog.majorum.Paper.Theorems

/-!
# Majorum, as an the framework's flat multiset-log flavour-framework model

Source: **arXiv:2601.03862v1** —
*Majorum: Ebb-and-Flow Consensus with Dynamic Quorums*, D'Amato, Saltini, Tran, Vonlanthen
and Zanolini, arXiv:2601.03862v1, 7 Jan 2026, to appear at FC'26. Statements cite its
numbered theorems and definitions, which are stable, rather than lines of the Overleaf
working copy at the paper's own source — that copy was the original source and
agrees with v1 on every statement rendered here, but it is not included here and its line
numbers move.

**Proved** (2026-08-04): Lemmas 2–7 and Theorems 1–2 for Algorithm 2, under `SettingGA`
plus the de-probabilized Lemma 1 (`HonestProposalWindow`) and `1 ≤ κ`. The rest of the
paper's theorems remain `Prop`-valued statements.

## Layout

The **spec** — the protocol and its model — lives in `Spec/`; the **paper-facing
results** in `Paper/`, one theorem per numbered lemma/theorem, each proved by a single
call so the lists read without proof noise; everything in between is the proof layer.

* `Spec/Assumptions` — the à la carte hypothesis groups (and `SettingGA`, the bundled
  Appendix-A setting). Majorum proves its theorems under *different* assumptions, so
  there is deliberately no single model predicate.
* `Spec/Security` — Definitions 4–7: dynamic availability, reorg resilience, accountable
  safety, secure ebb-and-flow. Definitions 1–3 (safe, live, secure) are
  protocol-independent and live in `the framework's flat multiset-log flavour.Execution`.
* `Spec/Algorithm5` — **Algorithm 5 itself**: Majorum as a `the framework's flat multiset-log flavour.Protocol`,
  with the fork-choice and finality machinery abstracted into `Components`.
* `Spec/Components` — the functions the algorithms call, defined: chains as lists of
  blocks (with the `⪯`/`≺` prefix notation), the three vote filters, `MFC`
  (Algorithm 1), `fastconfirmsimple`, `kappaPrefix`, and justification, finalization,
  `GJ` and `GF` (§4).
* `Spec/Algorithm2` — the probabilistically-safe TOB-SVD variant with fast
  confirmations, the dynamically available component on its own. **The proved lemmas
  and theorems are about this algorithm**; its messages are Algorithm 5's with the
  paper's "·" placeholder in the finality fields, chosen nondeterministically.
* `Mfc` — the view-local proof layer: vote filters, sender-counted majorities, what
  `MFC` returns, and the chain-structure suite for the κ-arithmetic.
* `Provenance` — execution-level helpers for Algorithm 5, and the protocol-generic
  pieces (`emitted_of_mem_sent`, `exists_time_eq`, …).
* `Provenance2` — the execution layer for Algorithm 2: provenance, the joining-check
  machinery, the honest-chain invariant, the Lemma-2 halves, each lemma's base case,
  and the Lemma-5/Theorem-2 engines.
* `Analysis2` — the Appendix-A results assembled in full: the real proofs of the
  numbered lemmas and theorems, including Theorem 2's split faces
  (`theorem2_safety`, `theorem2_liveness`, `theorem2_liveness_txpool`).
* `Paper/Lemmas` — **one theorem per numbered lemma of the paper**, and nothing else;
  proofs are one call into `Analysis2`.
* `Paper/Theorems` — the paper's theorems: the proved ones (`theorem1`, `theorem2`,
  one-call proofs) and the remaining statements as `Prop`s.

**Read the caveats in `Spec/Security.lean` before trusting the `Prop` statements.**
The probability qualifier lives in `HonestProposalWindow` for the proved results and is
silently dropped in the unproved `Prop` renderings; asymptotic bounds (`O(κ)`, `O(Δ)`)
become explicit parameters.
-/
