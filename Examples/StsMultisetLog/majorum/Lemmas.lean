import Examples.StsMultisetLog.majorum.Provenance2

/-!
# The paper's lemmas

**Convention (2026-08-03): one theorem here per numbered lemma of
arXiv:2601.03862v1, and nothing else.** Supporting material lives in `Mfc.lean`
(view-local: filters, majorities, `MFC`), `Provenance.lean` (execution-level, Algorithm
5) and `Provenance2.lean` (execution-level, Algorithm 2); the paper's *theorems* are
stated in `Theorems.lean` as `Prop`s awaiting proof.

**Lemma 2** (`lemma2` below) is proved, for Algorithm 2 — the algorithm the lemma is
about (Appendix A). The paper states three conclusions: `MFC^{propose(t+1)}_i ⪰ ch`
(`Provenance2.le_mfc_at_propose2`), `MFC^{vote(t+1)}_i ⪰ ch`
(`Provenance2.le_mfc_at_vote2`), and "which implies that, in slot `t+1`, all validators
in `H_vote(t+1)` send vote messages for chains extending `ch`" — the operative clause,
the one Lemma 3's induction consumes, and the statement of `lemma2`: the lemma's
hypothesis `ActiveVotesExtend2`, reproduced one slot later.

**Lemma 3** (`lemma3` below) is proved: a fast confirmation in slot `t` makes every
later slot's actives vote extensions of the confirmed chain — base case from the frozen
fast-confirmation (no majority needed), inductive step `lemma2`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 400

namespace Majorum

open the framework's flat multiset-log flavour

variable {Node Tx : Type} [DecidableEq Node] [DecidableEq Tx] [Fintype Node]
  {Q : Params} {S : Schedule Node} {kappa : Nat} {pool : Nat → Tx} {proposer : Nat → Node}

/-- Algorithm 2, its quorum threshold instantiated with the structural validator count.
    The paper's "·" — the blank finality fields — is nondeterministic in the protocol
    itself: each tick fills it with any value. -/
local notation "Pr2" => protocol2 Q (Fintype.card Node) kappa pool proposer

/-- **Lemma 2** (`Lemma 2, arXiv:2601.03862v1 p.8`, for Algorithm 2). If, in slot `t`,
    all validators in `H_vote(t)` send vote messages for chains extending `ch`, then, in
    slot `t+1`, all validators in `H_vote(t+1)` send vote messages for chains extending
    `ch`.

    Hypotheses: `SettingGA`, the bundled setting of the whole Appendix-A analysis. The
    proof: a validator active in slot `t+1` ticks at `voting(t+1)` with the joining check
    open (`activeAt_le_voting` — the framework's wake event fires only on sleep→awake
    transitions, so no wake inside the activity window can close it), and the vote that
    tick sends extends this tick's fork-choice (`handler2_vote_send`), which extends `ch`
    by `le_mfc_at_vote2`. -/
theorem lemma2 {x : Exec Pr2 S} (H : SettingGA Q S x)
    {t : Nat} (ht : 1 ≤ t) {ch : Chain Tx} (hvotes : ActiveVotesExtend2 x t ch) :
    ActiveVotesExtend2 x (t + 1) ch := by
  obtain ⟨⟨hmc, -, hsync, -, -, hdiv, hdil⟩, hstepw, hwpt, hone, ⟨hsyn, -⟩, hslp,
    ⟨hcb, hfn⟩, hgst⟩ := H
  exact activeVotesExtend_of_le_mfc hsync hstepw hdiv hdil fun p hp j hj =>
    le_mfc_at_vote2 hsync hstepw hdil hwpt hone hmc hsyn hslp hcb hfn hgst ht hvotes hp hj

/-- **Lemma 3** (`Lemma 3, arXiv:2601.03862v1 p.15`, for Algorithm 2). If a validator
    fast confirms a chain `ch` in slot `t` — its `fconf(t)` view holds a `2n/3` quorum
    for `ch`, so `fastconfirmsimple` returns `(ch, Q)` with `Q ≠ ∅` — then, for any slot
    `t' > t`, all validators in `H_vote(t')` send vote messages for chains extending
    `ch`.

    Stated without the paper's honesty of the confirmer: views are sound in this model
    (everything in any view is in the log), so the hypothesis is only *stronger* without
    it. Induction on `t'`: the base case is
    `Provenance2.activeVotesExtend_of_fastconfirm` — the quorum reaches every active's
    `merge(t)` view by synchrony, and the frozen chain rides through `processProposals2`
    (monotone) into the fork-choice's base — and the inductive step is `lemma2`. -/
theorem lemma3 {x : Exec Pr2 S} (H : SettingGA Q S x)
    {t : Nat} (ht : 1 ≤ t) {ch : Chain Tx}
    (hconf : ∃ (i : Nat) (w : Node) (cert : QCert Node Tx),
      x[i].time = Q.slotLength * t + 2 * Q.delta ∧
      fastConfirmSimple (Fintype.card Node) (x[i][w].view) t = (ch, some cert))
    {t' : Nat} (ht' : t < t') :
    ActiveVotesExtend2 x t' ch := by
  obtain ⟨iw, w, cert, htiw, hfc⟩ := hconf
  induction t', ht' using Nat.le_induction with
  | base =>
      obtain ⟨⟨hmc, -, hsync, -, -, hdiv, hdil⟩, hstepw, hwpt, hone, ⟨hsyn, -⟩, hslp,
        ⟨hcb, hfn⟩, hgst⟩ := H
      exact activeVotesExtend_of_fastconfirm hsync hstepw hdiv hdil hone hmc hsyn hcb hfn
        (le_refl _) htiw hfc
  | succ m hm ih => exact lemma2 H (by omega) ih

end Majorum
