# sts-framework — six flavours of a protocol framework

A protocol-independent framework for message-passing distributed protocols: rounds, signed
messages, views, the adversary's schedule, `Protocol`/`Config`/`Step`, executions, and the
network and sleepiness assumptions. Protocol models are *instances* of it.

There are six flavours. Each isolates **one** design choice, and they are deliberately
independent: no flavour imports another, nothing is shared between them, and duplication is
the point — a flavour must stay free to diverge. Consumers pick one.

| Flavour | The one thing it changes | Status | Consumers |
|---|---|---|---|
| `Sts2MX` | M reorganized — `Spec/` states, `Analysis/` proves, `Examples/` demonstrates; the long applied types drawn from section `variable`s | **active** | a consumer, a second consumer |
| `Sts2M` | the message log is a multiset, so a step's reaction is recoverable from it | frozen | a second consumer |
| `Sts2A` | `Step` is an `inductive` with a derived `Enabled` | frozen | — |
| `Sts2C` | the reaction is carried in the label, as a payload over the action | frozen | — |
| `Sts2D` | a fourth variant of the step relation | frozen | — |
| `Sts2Orig` | the original attempt, before the one-choice-at-a-time forks | frozen | — |

*Frozen* means the experiment concluded and its result is recorded in
[CONTEXT.md](CONTEXT.md) — the A/C/M comparison ended in a tie on proof effort, and M was
chosen. Frozen flavours are kept as baselines, not deleted: the comparison is the evidence for
a decision, and it outlives the code.

## Using it

Module roots are the flavour names, so imports read `import Sts2MX` or
`import Sts2MX.Spec.Protocol`. Namespaces are `Framework.<Flavour>`, unchanged from before the
extraction, so `open Framework.Sts2MX` is still how you bring the vocabulary into scope.

    make                 # list targets
    make cache           # fetch prebuilt Mathlib artifacts
    make Sts2MX          # sorry/admit check + build of one flavour

**Pins must match your consumers.** A required package sits in the same build graph, so its
toolchain must equal the consumer's, and Lake resolves one Mathlib rev per dependency name
across the graph — a mismatch fails the consumer's build, not this one. Both are pinned here to
`leanprover/lean4:v4.32.2` and Mathlib `v4.32.2`, and they move together.

## Provenance

Extracted on 2026-08-10 from the origin repository, with the framework's own history: 51
commits, from "Promote the framework to a top-level Framework/ directory" onwards. Paths were
flattened in the same pass (`Framework/Sts2MX/…` → `Sts2MX/…`), so entries in `CONTEXT.md`
written before that date name the old paths.
