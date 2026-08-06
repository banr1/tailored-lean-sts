import Examples.StsMultisetLog.majorum.Analysis.Proofs.Provenance2

/-!
# The Appendix-A analysis of Algorithm 2, assembled

The paper's numbered lemmas and theorems for Algorithm 2, **in full**: statements over
`SettingGA` with the quorum threshold instantiated at the structural validator count,
and the real proofs — destructuring the setting and composing the `Provenance2`
machinery.

The *paper-facing* lists live in `Analysis/Lemmas.lean` and `Analysis/Theorems.lean`:
identical statements whose proofs are a single call into this file, so the lists read
without proof noise. Full statement documentation lives there; the docstrings here
describe the assembly.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 400

namespace Majorum.Analysis2

open the framework's flat multiset-log flavour

variable {Node Tx : Type} [DecidableEq Node] [DecidableEq Tx] [Fintype Node]
  {Q : Params} {S : Schedule Node} {kappa : Nat} {pool : Nat → Tx} {proposer : Nat → Node}

/-- Algorithm 2, its quorum threshold instantiated with the structural validator count.
    The paper's "·" — the blank finality fields — is nondeterministic in the protocol
    itself: each tick fills it with any value. -/
local notation "Pr2" => protocol2 Q (Fintype.card Node) kappa pool proposer

/-- Lemma 2, assembled — `activeVotesExtend_of_le_mfc` over `le_mfc_at_vote2`.
    Documented in `Analysis/Lemmas.lean`. -/
theorem lemma2 {x : Exec Pr2 S} (H : SettingGA Q S x)
    {t : Nat} (ht : 1 ≤ t) {ch : Chain Tx} (hvotes : ActiveVotesExtend2 x t ch) :
    ActiveVotesExtend2 x (t + 1) ch := by
  obtain ⟨⟨hmc, -, hsync, -, -, hdiv, hdil⟩, hstepw, hwpt, hone, ⟨hsyn, -⟩, hslp,
    ⟨hcb, hfn⟩, hgst⟩ := H
  exact activeVotesExtend_of_le_mfc hsync hstepw hdiv hdil fun p hp j hj =>
    le_mfc_at_vote2 hsync hstepw hdil hwpt hone hmc hsyn hslp hcb hfn hgst ht hvotes hp hj

/-- Lemma 3, assembled — `Nat.le_induction` with `activeVotesExtend_of_fastconfirm` at
    the base and Lemma 2's step.
    Documented in `Analysis/Lemmas.lean`. -/
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

/-- Lemma 4, assembled — `Nat.le_induction` with `activeVotesExtend_of_propose` at the
    base and Lemma 2's step.
    Documented in `Analysis/Lemmas.lean`. -/
theorem lemma4 {x : Exec Pr2 S} (H : SettingGA Q S x) {t : Nat} (ht : 1 ≤ t)
    {vp : Node} {chp chC : Chain Tx} {qc : Option (QCert Node Tx)}
    {ck : Checkpoint (Chain Tx)} {i : Nat}
    (hsent : (⟨vp, Msg.propose chp chC qc ck t⟩ :
      SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ x[i].sent)
    (hhon_i : vp ∉ S.adv ((x[i].time : Int)))
    (hhon_t : vp ∉ S.adv (Q.voting (t : Int)))
    {t' : Nat} (ht' : t ≤ t') :
    ActiveVotesExtend2 x t' chp := by
  induction t', ht' using Nat.le_induction with
  | base =>
      obtain ⟨⟨hmc, -, hsync, -, -, hdiv, hdil⟩, hstepw, hwpt, hone, ⟨hsyn, hrel⟩, hslp,
        ⟨hcb, hfn⟩, hgst⟩ := H
      exact activeVotesExtend_of_propose hsync hstepw hdiv hdil hone hwpt hmc hsyn hrel
        hslp hcb hfn (le_refl _) hgst ht hsent hhon_i hhon_t
  | succ m hm ih => exact lemma2 H (by omega) ih

/-- Lemma 4's base case with the voted chain pinned: at the proposal's own slot the votes
    are exactly `chp`, not merely extensions of it. Only the base case admits this — from
    slot `t+1` on, the fork choice may have grown. -/
theorem activeVotesEq {x : Exec Pr2 S} (H : SettingGA Q S x) {t : Nat} (ht : 1 ≤ t)
    {vp : Node} {chp chC : Chain Tx} {qc : Option (QCert Node Tx)}
    {ck : Checkpoint (Chain Tx)} {i : Nat}
    (hsent : (⟨vp, Msg.propose chp chC qc ck t⟩ :
      SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ x[i].sent)
    (hhon_i : vp ∉ S.adv ((x[i].time : Int)))
    (hhon_t : vp ∉ S.adv (Q.voting (t : Int))) :
    ActiveVotesEq2 x t chp := by
  obtain ⟨⟨hmc, -, hsync, -, -, hdiv, hdil⟩, hstepw, hwpt, hone, ⟨hsyn, hrel⟩, hslp,
    ⟨hcb, hfn⟩, hgst⟩ := H
  exact activeVotesEq_of_propose hsync hstepw hdiv hdil hone hwpt hmc hsyn hrel
    hslp hcb hfn (le_refl _) hgst ht hsent hhon_i hhon_t

/-- Lemma 5, assembled — `chi_le_mfc`, the strong induction on the index of the last
    confirmed-chain write.
    Documented in `Analysis/Lemmas.lean`. -/
theorem lemma5 {x : Exec Pr2 S} (H : SettingGA Q S x) (hκ : 1 ≤ kappa)
    (hwin : HonestProposalWindow x)
    {a : Nat} {vi : Node} {b : Nat} {vj : Node} {sj : Nat} (hsj : 1 ≤ sj)
    (hact : vj ∈ Active Q S (sj : Int)) :
    (x[b].time = Q.slotLength * sj → x[a].time ≤ Q.slotLength * sj →
      x[a][vi].st.chi ⪯ mfc (x[b][vj].view) (x[b][vj].view)
        (fastConfirmSimple (Fintype.card Node) (x[b][vj].view) (sj - 1)).1 sj) ∧
    (x.lbl b = .tick vj (Q.slotLength * sj + Q.delta) →
      x[a].time ≤ Q.slotLength * sj + Q.delta →
      x[a][vi].st.chi ⪯
        mfc (processProposals2 (Fintype.card Node) proposer (x[b][vj].view) sj
            (x[b][vj].st)).vFrozen (x[b][vj].view)
          (processProposals2 (Fintype.card Node) proposer (x[b][vj].view) sj
            (x[b][vj].st)).chFrozen sj) := by
  obtain ⟨⟨hmc, -, hsync, -, -, hdiv, hdil⟩, hstepw, hwpt, hone, ⟨hsyn, hrel⟩, hslp,
    ⟨hcb, hfn⟩, hgst⟩ := H
  obtain ⟨s0, rfl⟩ : ∃ s0, sj = s0 + 1 := ⟨sj - 1, by omega⟩
  have hact' : vj ∈ Active Q S ((s0 : Int) + 1) := by
    have hcast : (((s0 + 1 : Nat)) : Int) = (s0 : Int) + 1 := by push_cast; omega
    rw [← hcast]
    exact hact
  have h := chi_le_mfc hsync hstepw hdiv hdil hone hwpt hmc hsyn hrel hslp hcb hfn
    (le_refl _) hgst hκ hwin a vi b vj s0
  have hδ := Q.deltaPos
  have hvot1 : Q.voting ((s0 : Int) + 1)
      = ((Q.slotLength * (s0 + 1) + Q.delta : Nat) : Int) := by
    unfold Params.voting
    push_cast
    omega
  refine ⟨fun htb hab => ?_, fun hjb hab => by simpa using h.2 hact' hjb hab⟩
  have hawk : x.Awake b vj := by
    show vj ∈ S.awake ((x[b].time : Int))
    rw [htb]
    refine mem_awakeThroughout.mp hact' _ ?_ ?_ <;> rw [hvot1] <;> push_cast <;>
      have hsl : Q.slotLength = 4 * Q.delta := rfl <;> omega
  simpa using h.1 hawk htb hab

/-- Lemma 6, assembled — `mfc_propose_ok`'s second projection.
    Documented in `Analysis/Lemmas.lean`. -/
theorem lemma6 {x : Exec Pr2 S} (H : SettingGA Q S x) {t : Nat} (ht : 1 ≤ t)
    {a : Nat} {w : Node} (hta : x[a].time = Q.slotLength * t) (hAwa : x.Awake a w) :
    proposedAt (mfc (x[a][w].view) (x[a][w].view)
      (fastConfirmSimple (Fintype.card Node) (x[a][w].view) (t - 1)).1 t) < t := by
  obtain ⟨⟨hmc, -, hsync, -, -, hdiv, hdil⟩, hstepw, hwpt, hone, ⟨hsyn, -⟩, hslp,
    ⟨hcb, hfn⟩, hgst⟩ := H
  obtain ⟨t0, rfl⟩ : ∃ t0, t = t0 + 1 := ⟨t - 1, by omega⟩
  have h := (mfc_propose_ok hsync hstepw hdiv hdil hone hwpt hmc hsyn hslp hcb hfn
    (le_refl _) hgst hta hAwa).2
  simpa using Nat.lt_succ_of_le h

/-- Lemma 7, assembled — Lemma 4 at its own slot, then `le_chi_at_fconf`.
    Documented in `Analysis/Lemmas.lean`. -/
theorem lemma7 {x : Exec Pr2 S} (H : SettingGA Q S x) {t : Nat} (ht : 1 ≤ t)
    (hbig : 2 * Fintype.card Node ≤ 3 * (Active Q S (t : Int)).card)
    {vp : Node} {chp chC : Chain Tx} {qc : Option (QCert Node Tx)}
    {ck : Checkpoint (Chain Tx)} {i : Nat}
    (hsent : (⟨vp, Msg.propose chp chC qc ck t⟩ :
      SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ x[i].sent)
    (hhon_i : vp ∉ S.adv ((x[i].time : Int)))
    (hhon_t : vp ∉ S.adv (Q.voting (t : Int)))
    {vi : Node} {j : Nat}
    (hj : x.lbl j = .tick vi (Q.slotLength * t + 2 * Q.delta)) :
    chp ⪯ x[j + 1][vi].st.chi := by
  have hvotes := lemma4 H ht hsent hhon_i hhon_t (le_refl t)
  obtain ⟨⟨hmc, -, hsync, -, -, hdiv, hdil⟩, hstepw, hwpt, hone, ⟨hsyn, hrel⟩, hslp,
    ⟨hcb, hfn⟩, hgst⟩ := H
  exact le_chi_at_fconf hsync hstepw hone hmc hsyn hcb hfn (le_refl _) hvotes hbig hj

/-- Theorem 1, assembled — Sleepiness inhabits a later slot's active set, a vote tick
    is produced there, Lemma 4's machinery and Lemma 5 bound the proposal and the
    confirmed chain by its fork choice, and prefixes of one chain are comparable.
    Documented in `Analysis/Theorems.lean`. -/
theorem theorem1 {x : Exec Pr2 S} (H : SettingGA Q S x) (hκ : 1 ≤ kappa)
    (hwin : HonestProposalWindow x)
    {tp : Nat} (htp : 1 ≤ tp) {vp : Node} {chp chC : Chain Tx}
    {qc : Option (QCert Node Tx)} {ck : Checkpoint (Chain Tx)} {i : Nat}
    (hsent : (⟨vp, Msg.propose chp chC qc ck tp⟩ :
      SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ x[i].sent)
    (hhon_i : vp ∉ S.adv ((x[i].time : Int)))
    (hhon_t : vp ∉ S.adv (Q.voting (tp : Int)))
    (a : Nat) (vi : Node) :
    chp ⪯ x[a][vi].st.chi ∨ x[a][vi].st.chi ⪯ chp := by
  obtain ⟨⟨hmc, -, hsync, -, -, hdiv, hdil⟩, hstepw, hwpt, hone, ⟨hsyn, hrel⟩, hslp,
    ⟨hcb, hfn⟩, hgst⟩ := id H
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  have hmono := hstepw.timeMonotone
  have hSL0 : 0 < Q.slotLength := by omega
  -- a slot past both the proposal and `ri`
  set s0 := max tp (x[a].time / Q.slotLength) with hs0def
  have htps0 : tp ≤ s0 := le_max_left _ _
  have hs01 : 1 ≤ s0 := le_trans htp htps0
  -- `H_vote(s0+1)` is inhabited
  have hgstok : (Q.gst : Int) ≤ Q.proposing ((s0 : Int) + 1 + 1) := by
    rw [hgst]
    unfold Params.proposing
    push_cast
    exact mul_nonneg (Int.natCast_nonneg _) (by omega)
  have hcount := hslp ((s0 : Int) + 1 + 1) hgstok
  rw [show ((s0 : Int) + 1 + 1 - 1) = (s0 : Int) + 1 by omega] at hcount
  have hpos : 0 < (Active Q S ((s0 : Int) + 1) \
      S.adv (Q.voting ((s0 : Int) + 1 + 1))).card := by omega
  obtain ⟨vj, hvjmem⟩ := Finset.card_pos.mp hpos
  have hvj : vj ∈ Active Q S ((s0 : Int) + 1) := (Finset.mem_sdiff.mp hvjmem).1
  -- its vote tick at `voting(s0+1)`
  have hvot1 : Q.voting ((s0 : Int) + 1)
      = ((Q.slotLength * (s0 + 1) + Q.delta : Nat) : Int) := by
    unfold Params.voting
    push_cast
    omega
  obtain ⟨i₁, hi₁⟩ := hdiv (Q.slotLength * (s0 + 1) + Q.delta)
  obtain ⟨i₀, hi₀, hti₀⟩ := exists_time_eq hstepw hi₁
  have hAw0 : x.Awake i₀ vj := by
    show vj ∈ S.awake ((x[i₀].time : Int))
    rw [hti₀]
    refine mem_awakeThroughout.mp hvj _ ?_ ?_ <;> rw [hvot1] <;> omega
  obtain ⟨j, htj, hlblj⟩ := hdil (Q.slotLength * (s0 + 1) + Q.delta) vj ⟨i₀, hti₀, hAw0⟩
  -- Lemma 4's side: the proposal is below the tick's fork choice
  have hAVE : ActiveVotesExtend2 x s0 chp :=
    ave_of_honest_proposal hsync hstepw hdiv hdil hone hwpt hmc hsyn hrel hslp hcb hfn
      (le_refl _) hgst htp hsent hhon_i hhon_t htps0
  have h4 := le_mfc_at_vote2 hsync hstepw hdil hwpt hone hmc hsyn hslp hcb hfn hgst
    hs01 hAVE hvj hlblj
  -- Lemma 5's side: the confirmed chain is below the same fork choice
  have hact : vj ∈ Active Q S (((s0 + 1 : Nat)) : Int) := by
    have hcast : (((s0 + 1 : Nat)) : Int) = (s0 : Int) + 1 := by push_cast; omega
    rw [hcast]
    exact hvj
  have hab : x[a].time ≤ Q.slotLength * (s0 + 1) + Q.delta := by
    have hdm := Nat.div_add_mod (x[a].time) Q.slotLength
    have hml := Nat.mod_lt (x[a].time) hSL0
    have hq1 : Q.slotLength * (x[a].time / Q.slotLength + 1)
        ≤ Q.slotLength * (s0 + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have hexp : Q.slotLength * (x[a].time / Q.slotLength + 1)
        = Q.slotLength * (x[a].time / Q.slotLength) + Q.slotLength := Nat.mul_succ ..
    omega
  have h5 := (lemma5 (a := a) (vi := vi) (b := j) (vj := vj) H hκ hwin
    (show 1 ≤ s0 + 1 by omega) hact).2 hlblj hab
  exact comparable_of_common_extension h4 h5

/-- **Theorem 2, the safety half** (`Theorem 2, arXiv:2601.03862v1 p.17`, for
    Algorithm 2). Any two validators' confirmed chains, at any two points of the
    execution, are comparable — the paper's "we now show safety" paragraph: pick a slot
    `tk` past both rounds, Constraint (1) makes `H_vote(tk)` inhabited, and Lemma 5
    bounds both confirmed chains by the same validator's fork choice there.

    Stated (and named) as a *half*: the paper's Theorem 2 is dynamic availability,
    safety **and liveness** with `Tconf = 8κΔ + Δ` — the liveness half is
    `theorem2_liveness` / `theorem2_liveness_txpool` below. Honesty of neither
    validator is assumed, as in Lemma 5. -/
theorem theorem2_safety {x : Exec Pr2 S} (H : SettingGA Q S x) (hκ : 1 ≤ kappa)
    (hwin : HonestProposalWindow x) (a : Nat) (vi : Node) (b : Nat) (vj : Node) :
    x[a][vi].st.chi ⪯ x[b][vj].st.chi ∨ x[b][vj].st.chi ⪯ x[a][vi].st.chi := by
  obtain ⟨⟨hmc, -, hsync, -, -, hdiv, hdil⟩, hstepw, hwpt, hone, ⟨hsyn, hrel⟩, hslp,
    ⟨hcb, hfn⟩, hgst⟩ := id H
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  have hmono := hstepw.timeMonotone
  have hSL0 : 0 < Q.slotLength := by omega
  -- a slot past both rounds
  set s0 := max (x[a].time / Q.slotLength) (x[b].time / Q.slotLength) with hs0def
  have hs0a : x[a].time / Q.slotLength ≤ s0 := le_max_left _ _
  have hs0b : x[b].time / Q.slotLength ≤ s0 := le_max_right _ _
  clear_value s0
  -- `H_vote(s0+1)` is inhabited
  have hgstok : (Q.gst : Int) ≤ Q.proposing ((s0 : Int) + 1 + 1) := by
    rw [hgst]
    unfold Params.proposing
    push_cast
    exact mul_nonneg (Int.natCast_nonneg _) (by omega)
  have hcount := hslp ((s0 : Int) + 1 + 1) hgstok
  rw [show ((s0 : Int) + 1 + 1 - 1) = (s0 : Int) + 1 by omega] at hcount
  have hpos : 0 < (Active Q S ((s0 : Int) + 1) \
      S.adv (Q.voting ((s0 : Int) + 1 + 1))).card := by omega
  obtain ⟨vk, hvkmem⟩ := Finset.card_pos.mp hpos
  have hvk : vk ∈ Active Q S ((s0 : Int) + 1) := (Finset.mem_sdiff.mp hvkmem).1
  -- its vote tick at `voting(s0+1)`
  have hvot1 : Q.voting ((s0 : Int) + 1)
      = ((Q.slotLength * (s0 + 1) + Q.delta : Nat) : Int) := by
    unfold Params.voting
    push_cast
    omega
  obtain ⟨i₁, hi₁⟩ := hdiv (Q.slotLength * (s0 + 1) + Q.delta)
  obtain ⟨i₀, hi₀, hti₀⟩ := exists_time_eq hstepw hi₁
  have hAw0 : x.Awake i₀ vk := by
    show vk ∈ S.awake ((x[i₀].time : Int))
    rw [hti₀]
    refine mem_awakeThroughout.mp hvk _ ?_ ?_ <;> rw [hvot1] <;> omega
  obtain ⟨j, htj, hlblj⟩ := hdil (Q.slotLength * (s0 + 1) + Q.delta) vk ⟨i₀, hti₀, hAw0⟩
  have hact : vk ∈ Active Q S (((s0 + 1 : Nat)) : Int) := by
    have hcast : (((s0 + 1 : Nat)) : Int) = (s0 : Int) + 1 := by push_cast; omega
    rw [hcast]
    exact hvk
  -- both confirmed chains sit below `vk`'s fork choice there
  have htime : ∀ c : Nat, c ∈ ({a, b} : Set Nat) →
      x[c].time / Q.slotLength ≤ s0 → x[c].time ≤ Q.slotLength * (s0 + 1) + Q.delta := by
    intro c _ hcs
    have hdm := Nat.div_add_mod (x[c].time) Q.slotLength
    have hml := Nat.mod_lt (x[c].time) hSL0
    have hq1 : Q.slotLength * (x[c].time / Q.slotLength + 1)
        ≤ Q.slotLength * (s0 + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have hexp : Q.slotLength * (x[c].time / Q.slotLength + 1)
        = Q.slotLength * (x[c].time / Q.slotLength) + Q.slotLength := Nat.mul_succ ..
    omega
  have h5a := (lemma5 (a := a) (vi := vi) (b := j) (vj := vk) H hκ hwin
    (show 1 ≤ s0 + 1 by omega) hact).2 hlblj
    (htime a (Or.inl rfl) hs0a)
  have h5b := (lemma5 (a := b) (vi := vj) (b := j) (vj := vk) H hκ hwin
    (show 1 ≤ s0 + 1 by omega) hact).2 hlblj
    (htime b (Or.inr rfl) hs0b)
  exact comparable_of_common_extension h5a h5b

/-- **Theorem 2, the liveness half** (`Theorem 2, arXiv:2601.03862v1 p.17`, for
    Algorithm 2), the chain fact: past any slot `t`, once `2κ` slots and a round have
    gone by, every validator active at that round confirms a chain extending some
    honest proposal from the window `[t+1, t+κ]`.

    This is the paper's `Tconf = 8κΔ + Δ` claim: `hri` reads
    `ri > vote(t + 2κ) = 4Δt + 8κΔ + Δ ≥ r + Tconf` for any round `r` of slot `t` (the
    strict `<` is the one-round shift of `ActiveAtRound`, see its docstring). The
    honest window slot exists by `HonestProposalWindow` — Lemma 1, where the paper says
    "there is a high probability of finding a slot `tp ∈ [t+1, t+κ]` hosted by an
    honest proposer". The transaction-pool conclusion is `theorem2_liveness_txpool`. -/
theorem theorem2_liveness {x : Exec Pr2 S} (H : SettingGA Q S x) (hκ : 1 ≤ kappa)
    (hwin : HonestProposalWindow x) {t : Nat}
    {a : Nat} {vi : Node} (hact : ActiveAtRound Q S vi (x[a].time))
    (hri : Q.slotLength * (t + 2 * kappa) + Q.delta < x[a].time) :
    ∃ tp, t + 1 ≤ tp ∧ tp ≤ t + kappa ∧
      ∃ (ip : Nat) (vp : Node) (chp chC : Chain Tx) (qc : Option (QCert Node Tx))
        (ck : Checkpoint (Chain Tx)),
        (⟨vp, Msg.propose chp chC qc ck tp⟩ :
          SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ x[ip].sent ∧
        vp ∉ S.adv ((x[ip].time : Int)) ∧ vp ∉ S.adv (Q.voting (tp : Int)) ∧
        chp ⪯ x[a][vi].st.chi := by
  obtain ⟨⟨hmc, -, hsync, -, -, hdiv, hdil⟩, hstepw, hwpt, hone, ⟨hsyn, hrel⟩, hslp,
    ⟨hcb, hfn⟩, hgst⟩ := id H
  obtain ⟨tp, htp0, htp1, htp2, ip, vp, chp, chC, qc, ck, hsent, hh1, hh2⟩ :=
    hwin (t + kappa + 1) (by omega)
  refine ⟨tp, by omega, by omega, ip, vp, chp, chC, qc, ck, hsent, hh1, hh2, ?_⟩
  refine le_chi_of_honest_proposal hsync hstepw hdiv hdil hone hwpt hmc hsyn hrel hslp
    hcb hfn (le_refl _) hgst hκ hwin htp0 hsent hh1 hh2 hact ?_
  have hmul : Q.slotLength * (tp + kappa) ≤ Q.slotLength * (t + 2 * kappa) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-- **Theorem 2, the liveness half, with the transaction pool** — Definition 2's
    shape. The mempool is interpreted at the statement level (decision of 2026-08-04,
    `CONTEXT.md`): `poolSet r` is the pool's content at round `r` over some transaction
    type `τ`, `memTx` reads the abstract block payloads, `hmonoP` is the paper's
    "ever-growing set", and `hcover` renders `Extend`'s contract — the body an honest
    slot-`s` proposer packs covers the pool at `propose(s)` (the "Property 1" the
    paper's proof cites but never states). Any transaction pooled by a round of slot
    `t` is then in a block of every sufficiently-later active validator's confirmed
    chain. -/
theorem theorem2_liveness_txpool {x : Exec Pr2 S} {τ : Type}
    (memTx : τ → Tx → Prop) (poolSet : Time → Set τ)
    (hmonoP : ∀ r r' : Time, r ≤ r' → poolSet r ⊆ poolSet r')
    (hcover : ∀ s : Nat, ∀ tx ∈ poolSet (Q.slotLength * s), memTx tx (pool s))
    (H : SettingGA Q S x) (hκ : 1 ≤ kappa) (hwin : HonestProposalWindow x)
    {t : Nat} {a : Nat} {vi : Node} (hact : ActiveAtRound Q S vi (x[a].time))
    (hri : Q.slotLength * (t + 2 * kappa) + Q.delta < x[a].time)
    {r : Time} (hr : r ≤ Q.slotLength * (t + 1)) :
    ∀ tx ∈ poolSet r, ∃ b ∈ x[a][vi].st.chi, memTx tx b.txs := by
  obtain ⟨tp, htp1, htp2, ip, vp, chp, chC, qc, ck, hsent, hh1, hh2, hle⟩ :=
    theorem2_liveness H hκ hwin hact hri (t := t)
  obtain ⟨⟨hmc, -, hsync, -, -, hdiv, hdil⟩, hstepw, -, -, -, -, -, -⟩ := id H
  obtain ⟨-, k, -, -, -, -, hchp_ext, -, -⟩ :=
    propose_provenance2 hsync hmc hstepw.timeMonotone hsent hh1 rfl
  intro tx htx
  refine ⟨⟨tp, pool tp⟩, ?_, ?_⟩
  · -- the proposal's own block sits in the confirmed chain
    have hmem : (⟨tp, pool tp⟩ : Block Tx) ∈ chp := by
      rw [hchp_ext]
      unfold extend
      simp
    have hsub : chp ⊆ x[a][vi].st.chi := by
      have h := hle
      rw [chainLe_iff_prefix] at h
      exact h.subset
    exact hsub hmem
  · -- and its body covers the pool at `propose(tp)`, hence at `r`
    refine hcover tp tx (hmonoP r (Q.slotLength * tp) ?_ htx)
    have hmul : Q.slotLength * (t + 1) ≤ Q.slotLength * tp :=
      Nat.mul_le_mul_left _ (by omega)
    omega

/-- Theorem 2, assembled: the conjunction of `theorem2_safety` and
    `theorem2_liveness_txpool` — dynamic availability as Definition 4 composes it.
    Documented in `Analysis/Theorems.lean`. -/
theorem theorem2 {x : Exec Pr2 S} {τ : Type}
    (memTx : τ → Tx → Prop) (poolSet : Time → Set τ)
    (hmonoP : ∀ r r' : Time, r ≤ r' → poolSet r ⊆ poolSet r')
    (hcover : ∀ s : Nat, ∀ tx ∈ poolSet (Q.slotLength * s), memTx tx (pool s))
    (H : SettingGA Q S x) (hκ : 1 ≤ kappa) (hwin : HonestProposalWindow x) :
    (∀ (a : Nat) (vi : Node) (b : Nat) (vj : Node),
      x[a][vi].st.chi ⪯ x[b][vj].st.chi ∨ x[b][vj].st.chi ⪯ x[a][vi].st.chi) ∧
    (∀ (t a : Nat) (vi : Node), ActiveAtRound Q S vi (x[a].time) →
      Q.slotLength * (t + 2 * kappa) + Q.delta < x[a].time →
      ∀ r : Time, r ≤ Q.slotLength * (t + 1) →
      ∀ tx ∈ poolSet r, ∃ b ∈ x[a][vi].st.chi, memTx tx b.txs) :=
  ⟨fun a vi b vj => theorem2_safety H hκ hwin a vi b vj,
   fun t a vi hact hri r hr =>
     theorem2_liveness_txpool memTx poolSet hmonoP hcover H hκ hwin (t := t) hact hri hr⟩

end Majorum.Analysis2
