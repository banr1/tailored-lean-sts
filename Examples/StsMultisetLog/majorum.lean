import Examples.StsMultisetLog.majorum.Assumptions
import Examples.StsMultisetLog.majorum.Security
import Examples.StsMultisetLog.majorum.Theorems
import Examples.StsMultisetLog.majorum.Protocol
import Examples.StsMultisetLog.majorum.Components
import Examples.StsMultisetLog.majorum.Algorithm2
import Examples.StsMultisetLog.majorum.Mfc
import Examples.StsMultisetLog.majorum.Provenance
import Examples.StsMultisetLog.majorum.Provenance2
import Examples.StsMultisetLog.majorum.Lemmas

/-!
# Majorum, as an `Sts2`-framework specification

Statements only, for now: the paper's security definitions and all seven of its theorems,
written as `Prop`s over the framework's flat multiset-log flavour. No protocol, no proofs.

Source: **arXiv:2601.03862v1** —
*Majorum: Ebb-and-Flow Consensus with Dynamic Quorums*, D'Amato, Saltini, Tran, Vonlanthen
and Zanolini, arXiv:2601.03862v1, 7 Jan 2026, to appear at FC'26. Statements cite its
numbered theorems and definitions, which are stable, rather than lines of the Overleaf
working copy at the paper's own source — that copy was the original source and
agrees with v1 on every statement rendered here, but it is not included here and its line
numbers move.

* `Assumptions` — the à la carte hypothesis groups. Majorum proves its theorems under
  *different* assumptions, so there is deliberately no single model predicate.
* `Security` — Definitions 4–7: dynamic availability, reorg resilience, accountable safety,
  secure ebb-and-flow. Definitions 1–3 (safe, live, secure) are protocol-independent and
  live in `the framework's flat multiset-log flavour.Execution`.
* `Theorems` — the seven theorem statements.
* `Components` — the functions Algorithm 5 calls, defined: chains as lists of blocks, the
  three vote filters, `MFC` (Algorithm 1), `fastconfirmsimple` (Algorithm 2), and
  justification, finalization, `GJ` and `GF` (§4). `algorithm5` is Majorum with all of them
  supplied.
* `Mfc` — view-local helpers: the vote filters, sender-counted majorities, and what `MFC`
  returns (`base_le_mfc`, `le_mfc_of_majority`).
* `Provenance` — execution-level helpers: everything in the log entered at a step, honest
  votes come from their sender's tick at their slot's vote reading, one honest validator
  casts one vote per slot, and an honest voter is active (`mem_active_of_honest_vote`).
* `Algorithm2` — the probabilistically-safe TOB-SVD variant with fast confirmations, the
  dynamically available component on its own. **Lemma 2 and Theorems 1–2 are about this
  algorithm**, not Algorithm 5; its messages are Algorithm 5's with the paper's "·"
  placeholder in the finality fields, and its proposal validity includes the certificate
  check against the receiver's view.
* `Lemmas` — **one theorem per numbered lemma of the paper**, and nothing else; empty until
  Lemma 2 closes.
* `Protocol` — **Algorithm 5 itself**: Majorum as a `the framework's flat multiset-log flavour.Protocol`. The four
  phase actions, the message formats and every state update, with the fork-choice and
  finality machinery abstracted into `Components`.

**Read the caveats in `Security.lean` before trusting any of this.** Four of the seven
theorems hold only *with overwhelming probability*, which cannot be said here; asymptotic
bounds (`O(κ)`, `O(Δ)`) become explicit parameters; and the two algorithms are not modelled,
so the statements are parameterised by a model rather than asserted of a protocol.
-/
