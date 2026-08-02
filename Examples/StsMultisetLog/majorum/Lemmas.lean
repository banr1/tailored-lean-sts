import Examples.StsMultisetLog.majorum.Provenance

/-!
# The paper's lemmas

**Convention (2026-08-03): one theorem here per numbered lemma of
arXiv:2601.03862v1, and nothing else.** Supporting material lives in `Mfc.lean`
(view-local: filters, majorities, `MFC`) and `Provenance.lean` (execution-level:
provenance, activation, the containment); the paper's *theorems* are stated in
`Theorems.lean` as `Prop`s awaiting proof.

Nothing qualifies yet. The state of **Lemma 2**, the first target: its view-local half,
its provenance layer, and its containment (`mem_active_of_honest_vote`) are proved; what
remains is Synchrony delivery of the slot-`t` votes into the view at `propose(t+1)`,
filter survival, and the counting assembly — none of which needs further assumptions. When
those close, `lemma2` appears here and this docstring shrinks to a table of contents.
-/
