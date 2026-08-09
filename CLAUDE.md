# sts-framework

Six flavours of a protocol-independent framework for message-passing distributed protocols,
in Lean 4. One directory per flavour, plus a root module per flavour (`Sts2MX.lean`). Module
roots are the flavour names; namespaces are `Framework.<Flavour>`. See
[README.md](README.md) for what each flavour changes, its status, and its consumers.

## The rule that shapes everything here

**Flavours are independent. No flavour imports another, nothing is shared between them, and
duplication is intentional.** Do not consolidate them, do not extract a common core, and do
not "fix" divergence between two flavours' copies of the same file — the divergence is the
experiment. If a flavour needs something another one has, copy it.

**Freeze, do not delete.** When an experiment concludes, record the result in
[CONTEXT.md](CONTEXT.md) and mark the flavour frozen in the README. The comparison is the
evidence for a design decision and outlives the code that produced it.

**A flavour with consumers is no longer an experiment.** `Sts2MX` and `Sts2M` are imported by
protocols in the origin repository. Changing their API means announcing it and porting the
consumers in the same change; changing a frozen flavour with no consumers means nothing to
anyone.

## Proof discipline

No `sorry`, no `admit`, no new `axiom`s, no `native_decide`: if a statement cannot be proved,
do not state it, and do not let a claim escape the kernel. `make <flavour>` enforces this
textually (mentions inside backticks are exempt) and by building.

## Commands

    make                 # list targets
    make cache           # fetch prebuilt Mathlib artifacts before a first build
    make Sts2MX          # sorry/admit check + build of one flavour
    make Sts2MX-build    # build only
    lake env lean Sts2MX/Spec/Protocol.lean   # check a single file

There is deliberately **no** target that checks every flavour: they share nothing, so a sweep
mostly reproves what the one flavour you touched already covered.

## Pins

`lean-toolchain` (Lean 4.32.2) and Mathlib's `rev` in `lakefile.toml` must match each other
**and every consumer**: a required package shares the consumer's build graph, where Lake
resolves one rev per dependency name. Bump the two together and tell the consumers.

## Keeping context across sessions

Durable context lives in [CONTEXT.md](CONTEXT.md). **Keep it current as work progresses** — it
exists so that nothing is lost when the conversation is compacted or a session ends. Write to
it, without being asked, whenever: a design decision is made (with the alternatives rejected,
and why); an approach fails or turns out to be a dead end — the negative results are the most
expensive thing to rediscover; a Lean-specific workaround or idiom is needed; or a flavour's
status changes.

Entries written before 2026-08-10 came from the origin repository's log and name the pre-
extraction paths (`Framework/Sts2M/`, `Framework.Sts2MX`). Read them with that substitution
rather than trusting the paths.

## A habit worth keeping

Before porting a consumer from one flavour to another, diff the two flavours' declaration
*names*. Majorum's port from `Sts2M` to `Sts2MX` was a one-pass job because the two declare
the same 104 names — checked in one command beforehand. It is a portability report, not a
conformance check: the sets are allowed to diverge.
