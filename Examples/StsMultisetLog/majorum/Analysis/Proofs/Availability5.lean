import Examples.StsMultisetLog.majorum.Analysis.Proofs.MfcEquiv

/-!
# Appendix C.1: Algorithm 5's dynamic availability

The synchronous half of the paper's Appendix C, past the transfer lemmas: **Theorem 3**
(reorg resilience), **Lemma 14** (fast liveness) and **Theorem 4** (dynamic availability),
all for Algorithm 5. Everything here is stated at the structural validator count, as in
`Analysis2.lean`, and reaches Algorithm 2's results through Lemma 10's MFC-equivalent run.

The paper proves these by rewriting Appendix A's proofs with `Chain` replaced by
`chainava` and Lemmas 4/5 replaced by Lemmas 12/13. Two places need more than a
substitution, both caused by Algorithm 5's extra `chainava` write — the fast-confirm
round's `chainava ← fastcand`, where `fastcand` may be the *greatest justified* chain
rather than a fast-confirmed one:

* the **order facts** the substitution takes for granted. `chAva_comparable` (any two
  available chains of a run are comparable) and `chAva_mono` (a validator's available
  chain only grows) are proved here once, the first from Lemma 10's dominance plus
  Algorithm 2's own safety, the second from it. The paper reads them off the pseudocode,
  where they are not visible: the `GJ`-branch write can move `chainava` sideways for all
  the pseudocode says.
* the **`GJ` branch itself**, in Lemma 14. The paper's Lemma 14 says its proof "follows
  the one for Lemma 7", which skips this branch; the paper does treat it in Theorem 4's
  proof ("consider the following additional case"). Here it is discharged by the same
  argument in both: a justified chain descends to some honest validator's available chain
  (`justified_to_voteChAva`), which Theorem 3 puts in order with the proposal, and the
  branch's own guard closes it.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 400

namespace Majorum.Availability5

open the framework's flat multiset-log flavour Classical

variable {Node Tx : Type} [DecidableEq Node] [DecidableEq Tx] [Fintype Node]
  {Q : Params} {S : Schedule Node} {kappa : Nat} {pool : Nat → Tx} {proposer : Nat → Node}

/-- Algorithm 5, its quorum threshold instantiated with the structural validator count. -/
local notation "Pr5" =>
  protocol (components (Fintype.card Node) kappa pool proposer) Q

local notation "M" => Msg (Chain Tx) (QCert Node Tx)

/-! ### The available chain is a total order, and grows -/

/-- **Theorem 4's safety half**: any two available chains of an Algorithm-5 run are
    comparable, at any two points and validators. Each is dominated by a confirmed chain
    of the MFC-equivalent Algorithm-2 run (Definition 9's conditions 2.3/2.4), those two
    are comparable by Algorithm 2's own safety (Theorem 2), and chains below one chain are
    comparable. -/
theorem chAva_comparable {x5 : Exec Pr5 S} (H5 : SettingGA Q S x5) (hκ : 1 ≤ kappa)
    (hwin5 : MfcEquiv.HonestProposalWindow5 (kappa := kappa) x5)
    (a : Nat) (vi : Node) (b : Nat) (vj : Node) :
    chainLe x5[a][vi].st.chAva x5[b][vj].st.chAva ∨
      chainLe x5[b][vj].st.chAva x5[a][vi].st.chAva := by
  obtain ⟨H2, heq⟩ := MfcEquiv.lemma10 rfl H5 hκ hwin5
  obtain ⟨c, w, -, h1⟩ := heq.2.2.2.2 a vi
  obtain ⟨d, w', -, h2⟩ := heq.2.2.2.2 b vj
  rcases Analysis2.theorem2_safety H2 hκ (MfcEquiv.window_transfer H5 hwin5) c w d w'
    with h | h
  · exact comparable_of_common_extension (chainLe_trans h1 h) h2
  · exact comparable_of_common_extension h1 (chainLe_trans h2 h)

/-- A guarded maximum fold never descends below its starting point. -/
private theorem foldl_max_ge (Mb : Chain Tx) :
    ∀ (l : List (Chain Tx)) (acc : Chain Tx),
      chainLe acc (l.foldl (fun acc ch =>
        if (components (Fintype.card Node) kappa pool proposer).prefixLe ch Mb then
          (components (Fintype.card Node) kappa pool proposer).maxCh acc ch
        else acc) acc) := by
  intro l
  induction l with
  | nil => exact fun acc => chainLe_refl _
  | cons c l ih =>
      intro acc
      rw [List.foldl_cons]
      refine chainLe_trans ?_ (ih _)
      by_cases hg : (components (Fintype.card Node) kappa pool proposer).prefixLe c Mb
      · rw [if_pos hg]
        show chainLe acc (if chainLe acc c then c else acc)
        split_ifs with h
        · exact h
        · exact chainLe_refl _
      · rw [if_neg hg]
        exact chainLe_refl _

/-- The vote round's `chainava` write is a maximum over candidates, starting from the old
    value: it never descends. -/
theorem chAva_le_voteChAva (x5 : Exec Pr5 S) (k : Nat) (w : Node) (t : Time) :
    chainLe x5[k][w].st.chAva
      (MfcEquiv.voteChAva (kappa := kappa) (pool := pool) x5 k w t) := by
  unfold MfcEquiv.voteChAva
  rw [show (processProposals (components (Fintype.card Node) kappa pool proposer)
      x5[k][w].view (t / Q.slotLength) x5[k][w].st).chAva = x5[k][w].st.chAva from
    MfcEquiv.processProposals_chAva _ _ _ _]
  exact foldl_max_ge _ _ _

/-- **A validator's available chain only grows.** The vote-round write is a maximum over
    the old value; the fast-confirm write fires only when the new value does *not* sit
    below the old one, and `chAva_comparable` then puts the old below the new. -/
theorem chAva_mono {x5 : Exec Pr5 S} (H5 : SettingGA Q S x5) (hκ : 1 ≤ kappa)
    (hwin5 : MfcEquiv.HonestProposalWindow5 (kappa := kappa) x5)
    (p : Node) {m m' : Nat} (h : m ≤ m') :
    chainLe x5[m][p].st.chAva x5[m'][p].st.chAva := by
  induction m', h using Nat.le_induction with
  | base => exact chainLe_refl _
  | succ k hk ih =>
      refine chainLe_trans ih ?_
      rcases MfcEquiv.chAva_step5 (x5 := x5) (m := k) (p := p) with
        hkeep | ⟨ti, -, -, hset⟩ | ⟨ti, -, hneg, hset⟩
      · rw [hkeep]
        exact chainLe_refl _
      · rw [hset]
        exact chAva_le_voteChAva x5 k p _
      · rcases chAva_comparable H5 hκ hwin5 k p (k + 1) p with h1 | h2
        · exact h1
        · exfalso
          rw [hset] at h2
          exact hneg h2

/-! ### Theorem 3: reorg resilience -/

set_option maxHeartbeats 1000000 in
/-- **Theorem 3** (reorg resilience for Algorithm 5). An honestly proposed chain never
    conflicts with any validator's available chain. The paper's Theorem-1 proof with
    Lemma 4 replaced by Lemma 12 and Lemma 5 by Lemma 13: pick a slot past both the
    proposal and the round in question, Constraint (1) inhabits its active set,
    `Diligent` produces a vote tick there, and both chains sit below that tick's fork
    choice. -/
theorem theorem3 {x5 : Exec Pr5 S} (H5 : SettingGA Q S x5) (hκ : 1 ≤ kappa)
    (hwin5 : MfcEquiv.HonestProposalWindow5 (kappa := kappa) x5)
    {tp : Nat} (htp : 1 ≤ tp) {vp : Node} {chp chC : Chain Tx}
    {qc : Option (QCert Node Tx)} {ck : Checkpoint (Chain Tx)} {i : Nat}
    (hsent : (⟨vp, Msg.propose chp chC qc ck tp⟩ : SignedMsg Node M) ∈ x5[i].sent)
    (hhon_i : vp ∉ S.adv ((x5[i].time : Int)))
    (hhon_t : vp ∉ S.adv (Q.voting (tp : Int)))
    (a : Nat) (vi : Node) :
    chainLe chp x5[a][vi].st.chAva ∨ chainLe x5[a][vi].st.chAva chp := by
  obtain ⟨H2, heq⟩ := MfcEquiv.lemma10 rfl H5 hκ hwin5
  have hwin2 := MfcEquiv.window_transfer H5 hwin5
  obtain ⟨⟨hmc, -, hsync, -, -, hdiv, hdil⟩, hstepw, hwpt, hone, ⟨hsyn, hrel⟩, hslp,
    ⟨hcb, hfn⟩, hgst⟩ := id H5
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  have hmono := hstepw.timeMonotone
  have hSL0 : 0 < Q.slotLength := by omega
  -- a slot past both the proposal and `a`'s round
  set s0 := max tp (x5[a].time / Q.slotLength) with hs0def
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
  have hAw0 : x5.Awake i₀ vj := by
    show vj ∈ S.awake ((x5[i₀].time : Int))
    rw [hti₀]
    refine mem_awakeThroughout.mp hvj _ ?_ ?_ <;> rw [hvot1] <;> omega
  obtain ⟨j, htj, hlblj⟩ := hdil (Q.slotLength * (s0 + 1) + Q.delta) vj ⟨i₀, hti₀, hAw0⟩
  -- Lemma 12: the proposal sits below that tick's fork choice
  have h12 := (MfcEquiv.lemma12 rfl heq H5 H2 htp hsent hhon_i hhon_t).2 s0 htps0
  have hchp := h12.2 j vj hvj hlblj
  -- Lemma 13: so does the available chain
  have h13 := (MfcEquiv.lemma13 rfl heq H5 H2 hκ hwin2 a vi j vj s0 hvj).2 hlblj ?_
  · exact comparable_of_common_extension hchp h13
  · have hdm := Nat.div_add_mod (x5[a].time) Q.slotLength
    have hml := Nat.mod_lt (x5[a].time) hSL0
    have hq1 : Q.slotLength * (x5[a].time / Q.slotLength + 1)
        ≤ Q.slotLength * (s0 + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have hexp : Q.slotLength * (x5[a].time / Q.slotLength + 1)
        = Q.slotLength * (x5[a].time / Q.slotLength) + Q.slotLength := Nat.mul_succ ..
    omega

/-! ### Lemma 14: fast liveness -/

/-- The fast-confirm round's `chainava` write, read off the handler. -/
theorem chAva_at_fconf5 {x5 : Exec Pr5 S} {j : Nat} {p : Node} {t : Nat}
    (hlbl : x5.lbl j = .tick p (Q.slotLength * t + 2 * Q.delta)) :
    x5[j + 1][p].st.chAva =
      if chainLe ((components (Fintype.card Node) kappa pool proposer).fastConfirm
          x5[j][p].view t).1 x5[j][p].st.chAva then
        x5[j][p].st.chAva
      else ((components (Fintype.card Node) kappa pool proposer).fastConfirm
        x5[j][p].view t).1 := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  have hmodf : (Q.slotLength * t + 2 * Q.delta) % Q.slotLength = 2 * Q.delta :=
    fconf_reading_mod Q t
  have hget : x5[j + 1][p].st
      = (handlerCore (components (Fintype.card Node) kappa pool proposer) Q
        (pick5 x5 j p (Q.slotLength * t + 2 * Q.delta)) p
        (Q.slotLength * t + 2 * Q.delta) x5[j][p].view x5[j][p].st).state := by
    rw [show x5[j + 1] = _ from exec5_succ (x5 := x5) j, hlbl]
    simp only [applyNodeStepResult_getElem, setClock_getElem, if_pos rfl, if_true]
    rfl
  rw [hget]
  simp only [handlerCore, apply_ite NodeStepResult.state]
  rw [if_neg (by omega), if_neg (by omega), if_pos (fconf_reading_mod Q t)]
  dsimp only
  rw [MfcEquiv.components_prefixLe, fconf_reading_div Q t]

set_option maxHeartbeats 1000000 in
/-- **The fast-confirmed chain of a slot whose actives all voted above `chp` extends
    `chp`.** The counting is view-local (`fastConfirmSimple_length_ge`); the comparability
    step is Algorithm 2's (`supported_comparable`), reached because the two runs' views
    have the same vote skeleton, which is all `fastconfirmsimple` and the support sets
    read. -/
theorem le_fcs_of_votes {x5 : Exec Pr5 S} (H5 : SettingGA Q S x5) (hκ : 1 ≤ kappa)
    (hwin5 : MfcEquiv.HonestProposalWindow5 (kappa := kappa) x5)
    {t : Nat} {chp : Chain Tx}
    (hvotes : MfcEquiv.ActiveVotesExtend5 (kappa := kappa) (pool := pool) x5 t chp)
    (hbig : 2 * Fintype.card Node ≤ 3 * (Active Q S (t : Int)).card)
    {vi : Node} {j : Nat}
    (hlbl : x5.lbl j = .tick vi (Q.slotLength * t + 2 * Q.delta)) :
    chainLe chp (fastConfirmSimple (Fintype.card Node) x5[j][vi].view t).1 ∧
      (chp ≠ [] → (fastConfirmSimple (Fintype.card Node) x5[j][vi].view t).2.isSome) := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  obtain ⟨H2, heq⟩ := MfcEquiv.lemma10 rfl H5 hκ hwin5
  obtain ⟨⟨hmc, -, hsync, -, -, hdiv, hdil⟩, hstepw, hwpt, hone, ⟨hsyn, hrel⟩, hslp,
    ⟨hcb, hfn⟩, hgst⟩ := id H5
  have hmono := hstepw.timeMonotone
  have htj : x5[j].time = Q.slotLength * t + 2 * Q.delta :=
    MfcEquiv.tick_reading5 hsync hlbl
  have hAwj : x5.Awake j vi := by
    have hstep := x5.step j
    rw [hlbl] at hstep
    have h := hstep.1
    simp only [spec] at h
    exact h
  -- every slot-`t` active's vote is in the view and supports `chp`
  have hsub : Active Q S (t : Int) ⊆ (((votes x5[j][vi].view).filter (fun sm =>
      msgSlot sm.msg = t ∧ chainLe chp (msgChain sm.msg))).image SignedMsg.sender) := by
    intro w hw
    obtain ⟨iv, e, esrc, etgt, htiv, hsent, hext⟩ := hvotes w hw
    have hview : (⟨w, Msg.vote e esrc etgt t⟩ : SignedMsg Node M) ∈ x5[j][vi].view := by
      refine hsyn iv j vi _ hsent ?_ hAwj
      rw [htiv, htj]
      have hg0 : Q.gst = 0 := hgst
      omega
    refine Finset.mem_image.mpr ⟨⟨w, Msg.vote e esrc etgt t⟩, ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨?_, rfl, hext⟩
    simp only [votes, Finset.mem_filter]
    exact ⟨hview, trivial⟩
  have hsupp : 2 * Fintype.card Node ≤ 3 * (((votes x5[j][vi].view).filter (fun sm =>
      msgSlot sm.msg = t ∧ chainLe chp (msgChain sm.msg))).image
        SignedMsg.sender).card := by
    have h := Finset.card_le_card hsub
    omega
  -- the two runs' views have the same vote skeleton
  have hskel : voteSkel x5[j][vi].view = voteSkel ((simulate x5)[j][vi].view) :=
    voteSkel_eq_of_corr (MfcEquiv.viewCorr_of_tableDynEq hone hmc H5.wellformed.2.1 hmono
      (MfcEquiv.table_and_dominance rfl H5 hκ hwin5 j j (le_refl j)).1 vi)
  have hfcs : fastConfirmSimple (Fintype.card Node) x5[j][vi].view t
      = fastConfirmSimple (Fintype.card Node) ((simulate x5)[j][vi].view) t :=
    fastConfirmSimple_congr hskel _ t
  by_cases hchp0 : chp = []
  · subst hchp0
    exact ⟨chainLe_nil _, fun h => absurd rfl h⟩
  · -- `chp` is a candidate, so the fast confirmation is at least as long …
    have hcand : chp ∈ candidates x5[j][vi].view ([] : Chain Tx) := by
      have hpos : 0 < (((votes x5[j][vi].view).filter (fun sm =>
          msgSlot sm.msg = t ∧ chainLe chp (msgChain sm.msg))).image
            SignedMsg.sender).card := by
        have hc := Fintype.card_pos_iff.mpr ⟨vi⟩
        omega
      rw [Finset.card_pos] at hpos
      obtain ⟨q, hq⟩ := hpos
      obtain ⟨sm, hsm, -⟩ := Finset.mem_image.mp hq
      rw [Finset.mem_filter] at hsm
      exact mem_candidates_of_extends hsm.1 hsm.2.2
    have hlen := fastConfirmSimple_length_ge (n := Fintype.card Node) hchp0 hcand hsupp
    have hpos : 0 < chp.length := by
      cases hb : chp with
      | nil => exact absurd hb hchp0
      | cons _ _ => simp [hb]
    -- … and comparable with it, by the simulated run's quorum intersection
    have hle : chainLe chp (fastConfirmSimple (Fintype.card Node) x5[j][vi].view t).1 := by
      rcases fastConfirmSimple_fst_cases (n := Fintype.card Node) x5[j][vi].view t
        with h0 | hsuppF
      · exfalso
        rw [h0] at hlen
        simp only [List.length_nil] at hlen
        omega
      · refine chainLe_of_comparable _ _ ?_ hlen
        have hs1 : 2 * Fintype.card Node ≤ 3 * (((votes ((simulate x5)[j][vi].view)).filter
            (fun sm => msgSlot sm.msg = t ∧ chainLe chp (msgChain sm.msg))).image
              SignedMsg.sender).card := by
          rw [support_skel, ← hskel, ← support_skel]
          exact hsupp
        have hs2 : 2 * Fintype.card Node ≤ 3 * (((votes ((simulate x5)[j][vi].view)).filter
            (fun sm => msgSlot sm.msg = t ∧
              chainLe (fastConfirmSimple (Fintype.card Node) x5[j][vi].view t).1
                (msgChain sm.msg))).image SignedMsg.sender).card := by
          rw [support_skel, ← hskel, ← support_skel]
          exact hsuppF
        exact supported_comparable H2.wellformed.2.2.1 H2.oneTick H2.wellformed.1
          H2.wellformed.2.2.2.1 H2.resilience.1 H2.resilience.2 (le_refl _) hs1 hs2
    refine ⟨hle, fun _ => ?_⟩
    cases hsnd : (fastConfirmSimple (Fintype.card Node) x5[j][vi].view t).2 with
    | none =>
        exfalso
        have h0 := fastConfirmSimple_none_fst hsnd
        rw [h0] at hlen
        simp only [List.length_nil] at hlen
        omega
    | some _ => rfl

set_option maxHeartbeats 1000000 in
/-- **Lemma 14** (fast liveness for Algorithm 5). In a slot whose active set holds at least
    `2n/3` validators, an honest proposal's chain is below the available chain of every
    validator at the end of its fast-confirm tick.

    The paper's Lemma-7 proof with `Chain` replaced by `chainava`, plus the branch that
    substitution hides: `fastcand` is the *greatest justified* chain when that chain does
    not extend the fast-confirmed one, and then `chp ⪯ fastcand` needs an argument. The
    justified chain descends to some honest validator's available chain
    (`justified_to_voteChAva`); Theorem 3 puts `chp` in order with that chain; and every
    order that would leave `chp` outside the justified chain also puts the justified chain
    below the fast-confirmed one, against the branch's own guard. -/
theorem lemma14 {x5 : Exec Pr5 S} (H5 : SettingGA Q S x5) (hκ : 1 ≤ kappa)
    (hwin5 : MfcEquiv.HonestProposalWindow5 (kappa := kappa) x5)
    {t : Nat} (ht : 1 ≤ t)
    (hbig : 2 * Fintype.card Node ≤ 3 * (Active Q S (t : Int)).card)
    {vp : Node} {chp chC : Chain Tx} {qc : Option (QCert Node Tx)}
    {ck : Checkpoint (Chain Tx)} {i : Nat}
    (hsent : (⟨vp, Msg.propose chp chC qc ck t⟩ : SignedMsg Node M) ∈ x5[i].sent)
    (hhon_i : vp ∉ S.adv ((x5[i].time : Int)))
    (hhon_t : vp ∉ S.adv (Q.voting (t : Int)))
    {vi : Node} {j : Nat}
    (hlbl : x5.lbl j = .tick vi (Q.slotLength * t + 2 * Q.delta)) :
    chainLe chp x5[j + 1][vi].st.chAva := by
  obtain ⟨H2, heq⟩ := MfcEquiv.lemma10 rfl H5 hκ hwin5
  obtain ⟨⟨hmc, -, hsync, hmono, -, -, -⟩, -, -, -, -, -, ⟨hcb, hfn⟩, -⟩ := id H5
  -- Lemma 12: every slot-`t` active voted above `chp`
  have hvotes := (MfcEquiv.lemma12 rfl heq H5 H2 ht hsent hhon_i hhon_t).1 t (le_refl t)
  obtain ⟨hfcs_le, -⟩ := le_fcs_of_votes H5 hκ hwin5 hvotes hbig hlbl
  -- the merge value tops `chp`, on either branch
  have hfc : chainLe chp ((components (Fintype.card Node) kappa pool proposer).fastConfirm
      x5[j][vi].view t).1 := by
    unfold Components.fastConfirm
    rw [MfcEquiv.components_fastConfirmSimple, MfcEquiv.components_gj,
      MfcEquiv.components_prefixLe]
    dsimp only
    by_cases hg : chainLe (gj (Fintype.card Node) x5[j][vi].view).ch
        (fastConfirmSimple (Fintype.card Node) x5[j][vi].view t).1
    · rw [if_pos hg]
      exact hfcs_le
    · rw [if_neg hg]
      dsimp only
      -- the `GJ` branch: the justified chain descends to an available chain
      rcases MfcEquiv.justified_to_voteChAva hsync hmc hmono hcb hfn (le_refl _)
          (i := j) (gj (Fintype.card Node) x5[j][vi].view).c _ rfl j vi (le_refl j)
          (gj_justified (Fintype.card Node) x5[j][vi].view) with hnil | hdesc
      · exact absurd (by rw [hnil]; exact chainLe_nil _) hg
      · obtain ⟨k', w, t', hk'j, hlbl', hmod', hgate', hle⟩ := hdesc
        rw [← MfcEquiv.vote_tick_chAva hlbl' hmod' hgate'] at hle
        rcases theorem3 H5 hκ hwin5 ht hsent hhon_i hhon_t (k' + 1) w with hchpA | hAchp
        · rcases comparable_of_common_extension hle hchpA with hgjchp | hchpgj
          · exact absurd (chainLe_trans hgjchp hfcs_le) hg
          · exact hchpgj
        · exact absurd (chainLe_trans (chainLe_trans hle hAchp) hfcs_le) hg
  rw [chAva_at_fconf5 hlbl]
  split_ifs with hwrite
  · exact chainLe_trans hfc hwrite
  · exact hfc

end Majorum.Availability5
