import Examples.StsMultisetLog.majorum.Provenance

/-!
# The paper's lemmas

**Convention (2026-08-03): one theorem here per numbered lemma of
arXiv:2601.03862v1, and nothing else.** Supporting material lives in `Mfc.lean`
(view-local: filters, majorities, `MFC`) and `Provenance.lean` (execution-level:
provenance, activation, the containment); the paper's *theorems* are stated in
`Theorems.lean` as `Prop`s awaiting proof.

Nothing qualifies yet. The state of **Lemma 2**, the first target: its **propose-round
half is fully proved** — `Provenance.le_mfc_at_propose`: under `ActiveVotesExtend` (the
lemma's hypothesis, over the log), the fork-choice of any validator active in slot `t+1`
returns an extension of `ch` at `propose(t+1)`, over any base `b ⪯ ch`. What separates
that from `lemma2` is the vote-round half: `MFC^{vote(t+1)} ⪰ ch` needs the `vFrozen`
variant of delivery (easy — the merge snapshot is late enough) and comparability of
`chfrozen` with `ch` through `merge` and `processProposals`, which brings back the
deferred certificate check (item 4) and the justified-checkpoint layer behind it.
-/
