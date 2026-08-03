import Examples.StsMultisetLog.majorum.Provenance2

/-!
# The paper's lemmas

**Convention (2026-08-03): one theorem here per numbered lemma of
arXiv:2601.03862v1, and nothing else.** Supporting material lives in `Mfc.lean`
(view-local: filters, majorities, `MFC`), `Provenance.lean` (execution-level, Algorithm
5) and `Provenance2.lean` (execution-level, Algorithm 2); the paper's *theorems* are
stated in `Theorems.lean` as `Prop`s awaiting proof.

Nothing qualifies yet. The state of **Lemma 2**, the first target — a statement about
**Algorithm 2** (Appendix A): its **propose-round half is fully proved** for Algorithm
2's protocol — `Provenance2.le_mfc_at_propose2`: under `ActiveVotesExtend2` (the lemma's
hypothesis, over the log), the fork-choice of any validator active in slot `t+1` returns
an extension of `ch` at `propose(t+1)`, over any base `b ⪯ ch`. The vote-round half is
in progress along the CONTEXT.md roadmap of 2026-08-03; the same-round-delivery problem
that would have made it false was resolved by making `fil1Exp` an equality filter (keep
exactly the previous slot's votes), so the voter counting is structural rather than
timing-based.
-/
