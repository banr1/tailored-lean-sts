import Examples.StsMultisetLog.majorum.Assumptions
import Examples.StsMultisetLog.majorum.Security
import Examples.StsMultisetLog.majorum.Theorems

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

**Read the caveats in `Security.lean` before trusting any of this.** Four of the seven
theorems hold only *with overwhelming probability*, which cannot be said here; asymptotic
bounds (`O(κ)`, `O(Δ)`) become explicit parameters; and the two algorithms are not modelled,
so the statements are parameterised by a model rather than asserted of a protocol.
-/
