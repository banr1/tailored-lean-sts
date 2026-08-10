# sts-framework

Five flavours of a protocol-independent framework for message-passing distributed protocols,
in Lean 4. One directory per flavour, plus a root module per flavour (`StsMultisetLog.lean`). Module
roots are the flavour names; namespaces are `Framework.<Flavour>`. See
[README.md](README.md) for what each flavour is and its status.

## The rule that shapes everything here

**Flavours are independent. No flavour imports another, nothing is shared between them, and
duplication is intentional.** Do not consolidate them, do not extract a common core, and do
not "fix" divergence between two flavours' copies of the same file — the divergence is the
experiment. If a flavour needs something another one has, copy it.

**Freeze, do not delete.** When an experiment concludes, record the result in
[CONTEXT.md](CONTEXT.md) and say in the README what design that flavour isolates. The
comparison is the evidence for a design decision and outlives the code that produced it.

**The suggested flavour is no longer an experiment.** That is `StsMultisetLog`, the one the
README points newcomers at. Treat its API as fixed: renaming or retyping anything it exports is
a change that has to be announced, with the affected declarations listed in the reply. The other
four have already answered their question, so changing their *design* helps nobody — leave that
as the record it is.

## Proof discipline

No `sorry`, no `admit`, no new `axiom`s, no `native_decide`: if a statement cannot be proved,
do not state it, and do not let a claim escape the kernel. `make <flavour>` enforces this
textually (mentions inside backticks are exempt) and by building.

## Commands

    make                 # list targets
    make cache           # fetch prebuilt Mathlib artifacts before a first build
    make StsMultisetLog          # sorry/admit check + build of one flavour
    make StsMultisetLog-build    # build only
    lake env lean StsMultisetLog/Spec/Protocol.lean   # check a single file

There is deliberately **no** target that checks every flavour: they share nothing, so a sweep
mostly reproves what the one flavour you touched already covered.

## Pins

`lean-toolchain` (Lean 4.32.2) and Mathlib's `rev` in `lakefile.toml` must match each other, and
bumping either is never a local decision: a package that is *required* somewhere joins that
build graph, which resolves one rev per dependency name and builds under one toolchain. Bump the
two together, and say in the reply that the pins moved.

## Keeping context across sessions

Durable context lives in [CONTEXT.md](CONTEXT.md). **Keep it current as work progresses** — it
exists so that nothing is lost when the conversation is compacted or a session ends. Write to
it, without being asked, whenever: a design decision is made (with the alternatives rejected,
and why); an approach fails or turns out to be a dead end — the negative results are the most
expensive thing to rediscover; a Lean-specific workaround or idiom is needed; or a flavour's
status changes.

Entries written before 2026-08-10 predate both the split into this package and the renaming of
the flavours, so they use the old paths (`Framework/Sts2M/`) and the old letter names. Read them
through the mapping at the top of [CONTEXT.md](CONTEXT.md) rather than trusting the names and
paths as written; the historical entries are deliberately left alone, since rewriting them would
falsify the record they exist to keep.

## Local instructions

Machine-local instructions live in [CLAUDE_LOCAL.md](CLAUDE_LOCAL.md), which is gitignored.
Read it as part of this file:

@CLAUDE_LOCAL.md

## A habit worth keeping

Before porting anything from one flavour to another, diff the two flavours' declaration
*names*. One such port, from the flat multiset-log flavour to the layered fork that has since
replaced it, was a one-pass job because the two declared the same 104 names — checked in one
command beforehand. It is a portability report, not a conformance check: the sets are allowed to
diverge.
