import Examples.StsMultisetLog.majorum.Assumptions
import Examples.StsMultisetLog.majorum.Security
import Examples.StsMultisetLog.majorum.Theorems

/-!
# Majorum, as an `Sts2`-framework specification

Statements only, for now: the paper's security definitions and all seven of its theorems,
written as `Prop`s over the framework's flat multiset-log flavour. No protocol, no proofs.

Source: the paper's own source — not included here, so the
statements below cite labels (`thm:liveness-chfin`, `def:reorg-resilience`, …) rather than
page numbers. The protocol is called 3SF in the paper; the paper's macro file binds `\protocol`
to *Majorum*, and the citing paper's source cites it as `damato2026majorum`.

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
