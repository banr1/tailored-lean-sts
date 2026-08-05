import Examples.StsMultisetLog.majorum.Analysis.Proofs.Availability5

/-!
# Appendix C.2: Algorithm 5 under partial synchrony

The finalized chain's side of Appendix C: **Lemma 15** (honest validators are never
slashed), **Theorem 5** (accountable safety), **Lemma 16** (the finalized chain grows),
**Lemmas 17–18** (the honest proposal's votes, and re-justification), **Theorem 6**
(liveness of the finalized chain) and **Theorem 7** (secure ebb-and-flow).

Unlike Appendix C.1, this half is not a transfer: Algorithm 2 has no finality component, so
nothing here comes through Lemma 10. What it rests on instead is Appendix B — the
view-local accountable-safety counting of Lemmas 8–9 — plus the *behavioural* invariants of
Algorithm 5's own fin-votes, which is what Lemma 15 is about.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 400

namespace Majorum.Finality5

open the framework's flat multiset-log flavour Classical

variable {Node Tx : Type} [DecidableEq Node] [DecidableEq Tx] [Fintype Node]
  {Q : Params} {S : Schedule Node} {kappa : Nat} {pool : Nat → Tx} {proposer : Nat → Node}

/-- Algorithm 5, its quorum threshold instantiated with the structural validator count. -/
local notation "Pr5" =>
  protocol (components (Fintype.card Node) kappa pool proposer) Q

local notation "M" => Msg (Chain Tx) (QCert Node Tx)

/-! ### The greatest justified checkpoint is greatest -/

/-- The slot-maximising fold dominates every member of its set. -/
theorem greatestBySlot_c_max {V : Finset (Checkpoint (Chain Tx))}
    {C : Checkpoint (Chain Tx)} (hC : C ∈ V) : C.c ≤ (greatestBySlot V).c := by
  unfold greatestBySlot
  have hmono : ∀ (l : List (Checkpoint (Chain Tx))) (b : Checkpoint (Chain Tx)),
      b.c ≤ (l.foldl (fun best C => if best.c ≤ C.c then C else best) b).c := by
    intro l
    induction l with
    | nil => exact fun b => le_refl _
    | cons a l ih =>
        intro b
        rw [List.foldl_cons]
        refine le_trans ?_ (ih _)
        by_cases hle : b.c ≤ a.c
        · rw [if_pos hle]
          exact hle
        · rw [if_neg hle]
  have hkey : ∀ (l : List (Checkpoint (Chain Tx))) (b : Checkpoint (Chain Tx)),
      C ∈ l → C.c ≤ (l.foldl (fun best C => if best.c ≤ C.c then C else best) b).c := by
    intro l
    induction l with
    | nil => exact fun b hC => absurd hC (List.not_mem_nil)
    | cons a l ih =>
        intro b hCmem
        rw [List.foldl_cons]
        rcases List.mem_cons.mp hCmem with rfl | hCl
        · refine le_trans ?_ (hmono l _)
          by_cases hle : b.c ≤ C.c
          · rw [if_pos hle]
          · rw [if_neg hle]
            omega
        · exact ih _ hCl
  exact hkey _ _ (Finset.mem_toList.mpr hC)

/-- A justified checkpoint is one of the view's checkpoints: genesis is there by
    construction, and a link's target is named by the votes the link counts — of which
    there is at least one, the quorum being nonempty. -/
theorem justified_mem_checkpoints {n : Nat} (hn : 0 < n) {V : View Node M}
    {C : Checkpoint (Chain Tx)} (h : JustifiedIn n V C) : C ∈ checkpoints V := by
  induction h with
  | genesis => exact Finset.mem_insert_self _ _
  | @link C₀ C₁ _ hlink _ =>
      -- the link's voter set is nonempty, and its votes name `C₁`
      have hpos : 0 < (linkVoters V C₀ C₁).card := by
        have := hlink.2.2
        omega
      rw [Finset.card_pos] at hpos
      obtain ⟨q, hq⟩ := hpos
      unfold linkVoters at hq
      obtain ⟨sm, hsm, -⟩ := Finset.mem_image.mp hq
      rw [Finset.mem_filter] at hsm
      refine Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨sm, hsm.1, ?_⟩)
      obtain ⟨e, src, tgt, s, hmsg⟩ := exists_vote_of_mem_votes hsm.1
      have hst : src = C₀ ∧ tgt = C₁ := by
        have h2 := hsm.2
        rw [hmsg] at h2
        exact ⟨h2.1, h2.2⟩
      rw [hmsg]
      simp only []
      rw [hst.2]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-- **`GJ` is the greatest justified checkpoint by slot**, which the paper writes as `≥`
    on checkpoints. -/
theorem le_gj_c_of_justified {n : Nat} (hn : 0 < n) {V : View Node M}
    {C : Checkpoint (Chain Tx)} (h : JustifiedIn n V C) : C.c ≤ (gj n V).c := by
  refine greatestBySlot_c_max ?_
  rw [Finset.mem_filter]
  exact ⟨justified_mem_checkpoints hn h, h⟩

/-! ### The frozen greatest-justified checkpoint climbs -/

/-- The proposal fold never lowers the frozen checkpoint's slot: its write is behind
    `acc.gjFrozen.c ≤ gjp.c`. -/
theorem processProposals_gjFrozen_c_mono (C : Components Node (Chain Tx) (QCert Node Tx))
    (V : View Node M) (t : Nat) (s : NodeState Node (Chain Tx) (QCert Node Tx)) :
    s.gjFrozen.c ≤ (processProposals C V t s).gjFrozen.c := by
  unfold processProposals
  generalize V.toList = l
  induction l generalizing s with
  | nil => exact le_refl _
  | cons a l ih =>
      rw [List.foldl_cons]
      refine le_trans ?_ (ih _)
      obtain ⟨asd, amsg⟩ := a
      cases amsg with
      | vote ch src tgt t' => exact le_refl _
      | propose chp chC qc gjp t' =>
          dsimp only
          simp only [apply_ite NodeState.gjFrozen, ite_self]
          split_ifs with hcond
          · exact hcond.2.2.2
          · exact le_refl _

/-- The vote tick's state write, on the frozen checkpoint: the fold's value, whether or not
    the joining check is open. -/
theorem vote_tick_gjFrozen5 {x5 : Exec Pr5 S} {k : Nat} {w : Node} {t : Time}
    (hlbl : x5.lbl k = .tick w t) (hmod : t % Q.slotLength = Q.delta) :
    x5[k + 1][w].st.gjFrozen
      = (processProposals (components (Fintype.card Node) kappa pool proposer)
        x5[k][w].view (t / Q.slotLength) x5[k][w].st).gjFrozen := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  have hget : x5[k + 1][w].st
      = (handlerCore (components (Fintype.card Node) kappa pool proposer) Q
        (pick5 x5 k w t) w t x5[k][w].view x5[k][w].st).state := by
    rw [show x5[k + 1] = _ from exec5_succ (x5 := x5) k, hlbl]
    simp only [applyNodeStepResult_getElem, setClock_getElem, if_pos rfl, if_true]
    rfl
  rw [hget]
  simp only [handlerCore, apply_ite NodeStepResult.state]
  rw [if_neg (by omega), if_pos hmod]
  simp only [apply_ite NodeState.gjFrozen, ite_self]

set_option maxHeartbeats 1000000 in
/-- **One step never lowers the frozen checkpoint's slot.** The vote tick writes the
    proposal fold's value, which is behind the `≤`-guard; the merge tick writes `GJ` of the
    current view, which dominates the old frozen checkpoint because that one is justified
    there (`gjFrozen_justified`) and `GJ` is greatest. -/
theorem gjFrozen_c_step5 {x5 : Exec Pr5 S} (hfn : 3 * Q.f < Fintype.card Node)
    {m : Nat} {p : Node} :
    x5[m][p].st.gjFrozen.c ≤ x5[m + 1][p].st.gjFrozen.c := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  have hcard : 0 < Fintype.card Node := by omega
  have h5 : x5[m + 1] = _ := exec5_succ (x5 := x5) m
  cases h : x5.lbl m with
  | advance t =>
      rw [h5, h]
      try exact le_refl _
  | tick q t =>
      by_cases hq : q = p
      · subst hq
        have hget : x5[m + 1][q].st
            = (handlerCore (components (Fintype.card Node) kappa pool proposer) Q
              (pick5 x5 m q t) q t x5[m][q].view x5[m][q].st).state := by
          rw [h5, h]
          simp only [applyNodeStepResult_getElem, setClock_getElem, if_pos rfl, if_true]
          rfl
        rw [hget]
        simp only [handlerCore, apply_ite NodeStepResult.state,
          apply_ite NodeState.gjFrozen, ite_self]
        by_cases hph0 : t % Q.slotLength = 0
        · rw [if_pos hph0]
          try simp only [apply_ite NodeState.gjFrozen, ite_self]
          try exact le_refl _
        · rw [if_neg hph0]
          by_cases hph1 : t % Q.slotLength = Q.delta
          · rw [if_pos hph1]
            try simp only [apply_ite NodeState.gjFrozen, ite_self]
            exact processProposals_gjFrozen_c_mono _ _ _ _
          · rw [if_neg hph1]
            by_cases hph2 : t % Q.slotLength = 2 * Q.delta
            · rw [if_pos hph2]
              try exact le_refl _
            · rw [if_neg hph2]
              by_cases hph3 : t % Q.slotLength = 3 * Q.delta
              · rw [if_pos hph3]
                -- the merge: `GJ` of the current view dominates the frozen checkpoint
                exact le_gj_c_of_justified hcard
                  (MfcEquiv.gjFrozen_justified (kappa := kappa) (pool := pool) m q)
              · rw [if_neg hph3]
                try exact le_refl _
      · rw [h5, h]
        simp only [applyNodeStepResult_getElem, setClock_getElem, if_neg hq]
        try exact le_refl _
  | deliver q msg =>
      rw [h5, h]
      by_cases hq : q = p
      · subst hq
        simp only [applyNodeStepResult_getElem, receive_getElem, if_pos rfl, if_true]
        try exact le_refl _
      · simp only [applyNodeStepResult_getElem, receive_getElem, if_neg hq]
        try exact le_refl _
  | wake q =>
      rw [h5, h]
      by_cases hq : q = p
      · subst hq
        simp only [applyNodeStepResult_getElem, if_pos rfl, if_true]
        try exact le_refl _
      · simp only [applyNodeStepResult_getElem, if_neg hq]
        try exact le_refl _
  | custom q ev => exact ev.elim
  | adversarial q msg =>
      rw [h5, h]
      try exact le_refl _

/-- The frozen checkpoint's slot never falls, across any span. -/
theorem gjFrozen_c_mono {x5 : Exec Pr5 S} (hfn : 3 * Q.f < Fintype.card Node)
    (p : Node) {m m' : Nat} (h : m ≤ m') :
    x5[m][p].st.gjFrozen.c ≤ x5[m'][p].st.gjFrozen.c := by
  induction m', h using Nat.le_induction with
  | base => exact le_refl _
  | succ k hk ih => exact le_trans ih (gjFrozen_c_step5 hfn)

/-! ### Lemma 15: honest validators are never slashed -/

set_option maxHeartbeats 1000000 in
/-- **An honest fin-vote's fields**: its target's checkpoint slot is the vote's own slot,
    and its source is the frozen greatest-justified checkpoint the tick wrote — the two
    facts the slashing conditions read. -/
theorem vote_fields5 {x5 : Exec Pr5 S} (hsync : SynchronizedClocks x5)
    (hmc : S.MonotoneCorruption) (hmono : TimeMonotone x5) {i : Nat}
    {sm : SignedMsg Node M} {e : Chain Tx} {src tgt : Checkpoint (Chain Tx)} {s : Nat}
    (hmem : sm ∈ x5[i].sent) (hhon : sm.sender ∉ S.adv ((x5[i].time : Int)))
    (hmsg : sm.msg = .vote e src tgt s) :
    tgt.c = s ∧ ∃ k, k < i ∧ x5[k].time = Q.slotLength * s + Q.delta ∧
      x5[k + 1][sm.sender].st.gjFrozen = src := by
  obtain ⟨k, hki, hlbl, htime, -, -, pick, -, hsend⟩ :=
    vote_provenance hsync hmc hmono hmem hhon hmsg
  have hcontent := MfcEquiv.handler_vote_fin_content (voting_reading_mod Q s) hsend
  rw [voting_reading_div Q s] at hcontent
  have heq := hmsg.symm.trans hcontent
  rw [Msg.vote.injEq] at heq
  obtain ⟨-, hsrc, htgt, -⟩ := heq
  refine ⟨?_, k, hki, htime, ?_⟩
  · rw [htgt]
    split_ifs <;> rfl
  · rw [vote_tick_gjFrozen5 hlbl (voting_reading_mod Q s), voting_reading_div Q s, ← hsrc]

set_option maxHeartbeats 1000000 in
/-- **Lemma 15** (`Lemma 15, arXiv:2601.03862v1 p.22`). An honest validator is never
    slashable — on any evidence drawn from what was actually sent.

    The paper's two observations, in Lean: an honest validator sends one vote per slot
    (`honest_vote_unique`) and its target's checkpoint slot *is* that slot, which rules out
    **E1**; and its source is the frozen greatest-justified checkpoint, whose slot never
    falls (`gjFrozen_c_mono`, over the proposal fold's `≤`-guard and `GJ`'s maximality at
    merges), which rules out **E2** — a later vote cannot reach back past an earlier
    one's source. -/
theorem lemma15 {x5 : Exec Pr5 S} (H5 : SettingGA Q S x5) {r : Nat} {w : Node}
    (hhon : w ∉ S.adv ((x5[r].time : Int)))
    {V : View Node M} (hsub : ∀ sm ∈ V, sm ∈ x5[r].sent) :
    ¬ SlashableIn V w := by
  obtain ⟨⟨hmc, -, hsync, hmono, -, -, -⟩, hstepw, -, hone, -, -, ⟨hcb, hfn⟩, -⟩ := id H5
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  rintro ⟨sm1, hsm1V, sm2, hsm2V, hs1, hs2, e1, e2, C1, C2, C3, C4, t1, t2,
    hm1, hm2, hE⟩
  have hsm1 : sm1 ∈ x5[r].sent := hsub _ hsm1V
  have hsm2 : sm2 ∈ x5[r].sent := hsub _ hsm2V
  have hh1 : sm1.sender ∉ S.adv ((x5[r].time : Int)) := by rw [hs1]; exact hhon
  have hh2 : sm2.sender ∉ S.adv ((x5[r].time : Int)) := by rw [hs2]; exact hhon
  obtain ⟨htgt1, k1, hk1r, htime1, hsrc1⟩ := vote_fields5 hsync hmc hmono hsm1 hh1 hm1
  obtain ⟨htgt2, k2, hk2r, htime2, hsrc2⟩ := vote_fields5 hsync hmc hmono hsm2 hh2 hm2
  rcases hE with ⟨hne, hsame⟩ | ⟨h31, h12, h24⟩
  · -- E1: same target slot, so the same slot, so the same message
    have hslots : t2 = t1 := by
      rw [← htgt1, ← htgt2, hsame]
    subst hslots
    have hsmeq : sm2 = sm1 :=
      honest_vote_unique hsync hone hmc hmono hsm1 hsm2 hh1 hh2 (by rw [hs1, hs2]) hm1 hm2
    rw [hsmeq, hm1] at hm2
    rw [Msg.vote.injEq] at hm2
    exact hne (by rw [hm2.2.1, hm2.2.2.1])
  · -- E2: the later vote's source cannot precede the earlier vote's source
    have ht12 : t1 < t2 := by
      rw [htgt1] at h12
      rw [htgt2] at h24
      omega
    have hk : k1 + 1 ≤ k2 := by
      rcases Nat.lt_or_ge k1 k2 with h | h
      · omega
      · exfalso
        have hle := time_le_of_le hmono h
        rw [htime1, htime2] at hle
        have hmul : Q.slotLength * (t1 + 1) ≤ Q.slotLength * t2 :=
          Nat.mul_le_mul_left _ ht12
        have hexp : Q.slotLength * (t1 + 1) = Q.slotLength * t1 + Q.slotLength :=
          Nat.mul_succ ..
        omega
    have hchain : C1.c ≤ C3.c := by
      rw [← hsrc1, ← hsrc2]
      rw [show sm1.sender = sm2.sender from by rw [hs1, hs2]] at *
      exact le_trans (gjFrozen_c_mono hfn sm2.sender hk) (gjFrozen_c_step5 hfn)
    omega

end Majorum.Finality5
