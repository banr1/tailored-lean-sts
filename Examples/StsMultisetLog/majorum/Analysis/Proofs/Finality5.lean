import Examples.StsMultisetLog.majorum.Analysis.Proofs.Availability5
import Examples.StsMultisetLog.majorum.Spec.Security

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
    proposal fold's value, which is behind the `≤` condition; the merge tick writes `GJ` of the
    current view, which dominates the old frozen checkpoint because that one is justified
    there (`gjFrozen_justified`) and `GJ` is greatest. -/
theorem gjFrozen_c_step5 {x5 : Exec Pr5 S} (hcard : 0 < Fintype.card Node)
    {m : Nat} {p : Node} :
    x5[m][p].st.gjFrozen.c ≤ x5[m + 1][p].st.gjFrozen.c := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
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
theorem gjFrozen_c_mono {x5 : Exec Pr5 S} (hcard : 0 < Fintype.card Node)
    (p : Node) {m m' : Nat} (h : m ≤ m') :
    x5[m][p].st.gjFrozen.c ≤ x5[m'][p].st.gjFrozen.c := by
  induction m', h using Nat.le_induction with
  | base => exact le_refl _
  | succ k hk ih => exact le_trans ih (gjFrozen_c_step5 hcard)

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
    falls (`gjFrozen_c_mono`, over the proposal fold's `≤` condition and `GJ`'s maximality at
    merges), which rules out **E2** — a later vote cannot reach back past an earlier
    one's source. -/
theorem lemma15 {x5 : Exec Pr5 S} (hsync : SynchronizedClocks x5) (hmono : TimeMonotone x5)
    (hone : OneTickPerReading x5) (hmc : S.MonotoneCorruption)
    (hcard : 0 < Fintype.card Node) {r : Nat} {w : Node}
    (hhon : w ∉ S.adv ((x5[r].time : Int)))
    {V : View Node M} (hsub : ∀ sm ∈ V, sm ∈ x5[r].sent) :
    ¬ SlashableIn V w := by
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
      exact le_trans (gjFrozen_c_mono hcard sm2.sender hk) (gjFrozen_c_step5 hcard)
    omega

/-! ### Theorem 5: accountable safety -/

/-- Supermajority links survive a growing view: the voter set only grows. -/
theorem link_mono {n : Nat} {V V' : View Node M} (hVV' : V ⊆ V')
    {C C' : Checkpoint (Chain Tx)} (h : link n V C C') : link n V' C C' := by
  refine ⟨h.1, h.2.1, le_trans h.2.2 ?_⟩
  have hsub : linkVoters V C C' ⊆ linkVoters V' C C' := by
    unfold linkVoters
    exact Finset.image_subset_image (Finset.filter_subset_filter _ (by
      unfold votes
      exact Finset.filter_subset_filter _ hVV'))
  have := Finset.card_le_card hsub
  omega

/-- Finalization survives a growing view. -/
theorem finalizedIn_mono {n : Nat} {V V' : View Node M} (hVV' : V ⊆ V')
    {C : Checkpoint (Chain Tx)} (h : FinalizedIn n V C) : FinalizedIn n V' C :=
  ⟨justifiedIn_mono hVV' h.1, h.2.choose, h.2.choose_spec.1,
    link_mono hVV' h.2.choose_spec.2⟩

/-- **`GF` is finalized, or is still genesis**: the slot-maximising fold starts at
    `(B_genesis, 0)` and otherwise only adopts finalized checkpoints. -/
theorem gf_finalized_or_genesis (n : Nat) (V : View Node M) :
    gf n V = ⟨[], 0⟩ ∨ FinalizedIn n V (gf n V) := by
  unfold gf greatestBySlot
  have hfold : ∀ (l : List (Checkpoint (Chain Tx))) (b : Checkpoint (Chain Tx)),
      (b = ⟨[], 0⟩ ∨ FinalizedIn n V b) → (∀ C ∈ l, FinalizedIn n V C) →
      ((l.foldl (fun best C => if best.c ≤ C.c then C else best) b) = ⟨[], 0⟩ ∨
        FinalizedIn n V (l.foldl (fun best C => if best.c ≤ C.c then C else best) b)) := by
    intro l
    induction l with
    | nil => exact fun b hb _ => hb
    | cons a l ih =>
        intro b hb hmem
        rw [List.foldl_cons]
        refine ih _ ?_ (fun C hC => hmem C (List.mem_cons_of_mem a hC))
        by_cases hle : b.c ≤ a.c
        · rw [if_pos hle]
          exact Or.inr (hmem a List.mem_cons_self)
        · rw [if_neg hle]
          exact hb
  refine hfold _ _ (Or.inl rfl) ?_
  intro C hC
  have := Finset.mem_toList.mp hC
  rw [Finset.mem_filter] at this
  exact this.2

/-- The common prefix is a prefix of its second argument. -/
theorem commonPrefix_le_right : ∀ a b : Chain Tx, chainLe (commonPrefix a b) b := by
  intro a
  induction a with
  | nil => exact fun b => chainLe_nil b
  | cons x xs ih =>
      intro b
      cases b with
      | nil => exact chainLe_nil []
      | cons y ys =>
          show chainLe (if x = y then x :: commonPrefix xs ys else []) (y :: ys)
          split_ifs with hxy
          · subst hxy
            have h := ih ys
            simp only [chainLe, List.isPrefixOf_cons_cons_self]
            exact h
          · exact chainLe_nil _

/-- The proposal fold leaves the finalized chain alone. -/
theorem processProposals_chFin (C : Components Node (Chain Tx) (QCert Node Tx))
    (V : View Node M) (t : Nat) (s : NodeState Node (Chain Tx) (QCert Node Tx)) :
    (processProposals C V t s).chFin = s.chFin := by
  unfold processProposals
  generalize V.toList = l
  induction l generalizing s with
  | nil => rfl
  | cons a l ih =>
      rw [List.foldl_cons, ih]
      obtain ⟨asd, amsg⟩ := a
      cases amsg with
      | vote ch src tgt t' => rfl
      | propose chp chC qc gjp t' =>
          dsimp only
          simp only [apply_ite NodeState.chFin, ite_self]

set_option maxHeartbeats 1000000 in
/-- **Every validator's finalized chain is a prefix of a finalized checkpoint's chain in
    its own view** — genesis until something is finalized. The paper states this as
    "`chainfin^r_i` is any chain finalized according to `V^r_i`", reading it off the three
    lines that write the field; here it is an induction over the execution, with
    `finalizedIn_mono` carrying each write forward through the growing view. -/
theorem chFin_finalized5 {x5 : Exec Pr5 S} (i : Nat) (p : Node) :
    x5[i][p].st.chFin = [] ∨
      ∃ (ch : Chain Tx) (c : Nat),
        FinalizedIn (Fintype.card Node) x5[i][p].view ⟨ch, c⟩ ∧
        chainLe x5[i][p].st.chFin ch := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  induction i with
  | zero =>
      left
      show ((x5.cfg 0)[p]).st.chFin = []
      rw [x5.init.2.1 p]
      rfl
  | succ i ih =>
      -- the field is written only at vote and fast-confirm ticks, to `GF`'s chain or below
      have hstep : x5[i + 1][p].st.chFin = x5[i][p].st.chFin ∨
          chainLe x5[i + 1][p].st.chFin (gf (Fintype.card Node) x5[i][p].view).ch := by
        have h5 : x5[i + 1] = _ := exec5_succ (x5 := x5) i
        cases h : x5.lbl i with
        | advance t => exact Or.inl (by rw [h5, h]; try rfl)
        | tick q t =>
            by_cases hq : q = p
            · subst hq
              have hget : x5[i + 1][q].st
                  = (handlerCore (components (Fintype.card Node) kappa pool proposer) Q
                    (pick5 x5 i q t) q t x5[i][q].view x5[i][q].st).state := by
                rw [h5, h]
                simp only [applyNodeStepResult_getElem, setClock_getElem, if_pos rfl,
                  if_true]
                rfl
              rw [hget]
              simp only [handlerCore, apply_ite NodeStepResult.state]
              by_cases hph0 : t % Q.slotLength = 0
              · rw [if_pos hph0]
                refine Or.inl ?_
                simp only [apply_ite NodeState.chFin, ite_self]
                try rfl
              · rw [if_neg hph0]
                by_cases hph1 : t % Q.slotLength = Q.delta
                · rw [if_pos hph1]
                  by_cases hgate : x5[i][q].st.activeAt ≤ t
                  · rw [if_pos hgate]
                    exact Or.inr (commonPrefix_le_right _ _)
                  · rw [if_neg hgate]
                    refine Or.inl ?_
                    exact processProposals_chFin _ _ _ _
                · rw [if_neg hph1]
                  by_cases hph2 : t % Q.slotLength = 2 * Q.delta
                  · rw [if_pos hph2]
                    dsimp only
                    exact Or.inr (chainLe_refl _)
                  · rw [if_neg hph2]
                    by_cases hph3 : t % Q.slotLength = 3 * Q.delta
                    · rw [if_pos hph3]
                      refine Or.inl ?_
                      dsimp only
                    · rw [if_neg hph3]
                      refine Or.inl ?_
                      dsimp only
            · refine Or.inl ?_
              rw [h5, h]
              simp only [applyNodeStepResult_getElem, setClock_getElem, if_neg hq]
              try rfl
        | deliver q msg =>
            refine Or.inl ?_
            rw [h5, h]
            by_cases hq : q = p
            · subst hq
              simp only [applyNodeStepResult_getElem, receive_getElem, if_pos rfl, if_true]
              try rfl
            · simp only [applyNodeStepResult_getElem, receive_getElem, if_neg hq]
              try rfl
        | wake q =>
            refine Or.inl ?_
            rw [h5, h]
            by_cases hq : q = p
            · subst hq
              simp only [applyNodeStepResult_getElem, if_pos rfl, if_true]
              try rfl
            · simp only [applyNodeStepResult_getElem, if_neg hq]
              try rfl
        | custom q ev => exact ev.elim
        | adversarial q msg => exact Or.inl (by rw [h5, h]; try rfl)
      have hview : x5[i][p].view ⊆ x5[i + 1][p].view := view_mono (Pr' := Pr5) i p
      rcases hstep with hkeep | hnew
      · rw [hkeep]
        rcases ih with h0 | ⟨ch, c, hfin, hle⟩
        · exact Or.inl h0
        · exact Or.inr ⟨ch, c, finalizedIn_mono hview hfin, hle⟩
      · rcases gf_finalized_or_genesis (Fintype.card Node) x5[i][p].view with hgen | hfin
        · left
          rw [hgen] at hnew
          -- a prefix of genesis is genesis
          have h := hnew
          rw [chainLe_iff_prefix] at h
          exact List.eq_nil_of_prefix_nil h
        · exact Or.inr ⟨(gf (Fintype.card Node) x5[i][p].view).ch,
            (gf (Fintype.card Node) x5[i][p].view).c,
            finalizedIn_mono hview hfin, hnew⟩

/-- **The identification procedure** of Definition 6, for Algorithm 5: the validators whose
    own fin-votes, among the messages sent, violate E1 or E2. It reads the log and nothing
    else, as the definition demands. -/
noncomputable def culprits5 (L : Multiset (SignedMsg Node M)) : Finset Node :=
  Finset.univ.filter (fun w => SlashableIn L.toFinset w)

theorem mem_culprits5 {L : Multiset (SignedMsg Node M)} {w : Node} :
    w ∈ culprits5 L ↔ SlashableIn L.toFinset w := by
  unfold culprits5
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- The log never forgets, across any span. -/
theorem mem_sent_mono {x5 : Exec Pr5 S} {i k : Nat} (h : i ≤ k)
    {sm : SignedMsg Node M} (hm : sm ∈ x5[i].sent) : sm ∈ x5[k].sent := by
  induction k, h using Nat.le_induction with
  | base => exact hm
  | succ k hk ih =>
      exact Multiset.mem_of_le (sent_mono (x5.step k)) ih

set_option maxHeartbeats 1000000 in
/-- **Theorem 5** (accountable safety for Algorithm 5). If two honest validators' finalized
    chains conflict then, from the messages sent, at least `n/3` validators can be named,
    and no validator is ever named while honest.

    The first conjunct is Lemma 9 (Appendix B's counting) applied to the finalized
    checkpoints that `chFin_finalized5` produces from the two validators' own views, whose
    messages the log contains; the second is Lemma 15. No corruption bound is assumed —
    the paper's `f ∈ [0, n]` — only that the execution is well-formed and that there is at
    least one validator. -/
theorem theorem5 {x5 : Exec Pr5 S} (hsync : SynchronizedClocks x5) (hmono : TimeMonotone x5)
    (hone : OneTickPerReading x5) (hmc : S.MonotoneCorruption)
    (hcard : 0 < Fintype.card Node) :
    AccountableSafety (fun p c => c[p].st.chFin) (fun a b => chainLe a b)
      culprits5 (Fintype.card Node / 3) x5 := by
  constructor
  · -- a conflict names a third of the validators
    intro i j p q hp hq hconf k hk
    have hij : i ≤ k := le_trans (le_max_left i j) hk
    have hjk : j ≤ k := le_trans (le_max_right i j) hk
    have hc1 : ¬ chainLe x5[i][p].st.chFin x5[j][q].st.chFin := hconf.1
    have hc2 : ¬ chainLe x5[j][q].st.chFin x5[i][p].st.chFin := hconf.2
    -- neither chain is genesis: genesis conflicts with nothing
    rcases chFin_finalized5 (kappa := kappa) (pool := pool) (proposer := proposer) i p
      with h0 | ⟨ch1, c1, hfin1, hle1⟩
    · exact absurd (by rw [h0]; exact chainLe_nil _) hc1
    rcases chFin_finalized5 (kappa := kappa) (pool := pool) (proposer := proposer) j q
      with h0 | ⟨ch2, c2, hfin2, hle2⟩
    · exact absurd (by rw [h0]; exact chainLe_nil _) hc2
    -- Lemma 9's counting, over the two views
    obtain ⟨W, hW3, hWslash⟩ :=
      Finality.lemma9 (n := Fintype.card Node) (le_refl _) hfin1 hle1 hfin2 hle2
        hc1 hc2
    -- every named validator is slashable on the log
    have hsub : W ⊆ culprits5 x5[k].sent := by
      intro w hw
      obtain ⟨sm1, hsm1, sm2, hsm2, hs1, hs2, e1, e2, C1, C2, C3, C4, t1, t2,
        hm1, hm2, hE⟩ := hWslash w hw
      refine mem_culprits5.mpr ⟨sm1, ?_, sm2, ?_, hs1, hs2, e1, e2, C1, C2, C3, C4,
        t1, t2, hm1, hm2, hE⟩
      · rcases Finset.mem_union.mp hsm1 with h | h
        · exact Multiset.mem_toFinset.mpr (mem_sent_mono hij (views_sound x5 i p _ h))
        · exact Multiset.mem_toFinset.mpr (mem_sent_mono hjk (views_sound x5 j q _ h))
      · rcases Finset.mem_union.mp hsm2 with h | h
        · exact Multiset.mem_toFinset.mpr (mem_sent_mono hij (views_sound x5 i p _ h))
        · exact Multiset.mem_toFinset.mpr (mem_sent_mono hjk (views_sound x5 j q _ h))
    have hcards := Finset.card_le_card hsub
    omega
  · -- and no honest validator is ever named
    intro k w hw
    by_contra hhon
    exact lemma15 hsync hmono hone hmc hcard hhon
      (fun sm hsm => Multiset.mem_toFinset.mp hsm) (mem_culprits5.mp hw)

/-! ### Finalized and justified checkpoints nest -/

set_option maxHeartbeats 1000000 in
/-- **A finalized checkpoint's chain is a prefix of every justified checkpoint at or above
    its slot** — Lemma 8 with the slashing disjunct killed: its `n/3` culprits would all be
    adversarial (Lemma 15), and `f < n/3` leaves no room. This is where Appendix C.2 uses
    the corruption bound, and it is the step the paper writes as "Lemma 8 and `f < n/3`
    imply …". -/
theorem justified_nest {x5 : Exec Pr5 S} (hsync : SynchronizedClocks x5)
    (hmono : TimeMonotone x5) (hone : OneTickPerReading x5) (hmc : S.MonotoneCorruption)
    (hcb : S.CorruptionBounded Q.f) (hfn : 3 * Q.f < Fintype.card Node)
    {k : Nat} {V1 V2 : View Node M}
    (hV1 : ∀ sm ∈ V1, sm ∈ x5[k].sent) (hV2 : ∀ sm ∈ V2, sm ∈ x5[k].sent)
    {chf chj : Chain Tx} {cf cj : Nat}
    (hf : FinalizedIn (Fintype.card Node) V1 ⟨chf, cf⟩)
    (hj : JustifiedIn (Fintype.card Node) V2 ⟨chj, cj⟩) (hle : cf ≤ cj) :
    chainLe chf chj := by
  have hcard : 0 < Fintype.card Node := by omega
  rcases Finality.lemma8 (n := Fintype.card Node) (le_refl _) hf hj hle with hok | ⟨W, hW3, hWs⟩
  · exact hok
  · exfalso
    -- every named validator is adversarial at `k`, and there are too many of them
    have hsub : W ⊆ S.adv ((x5[k].time : Int)) := by
      intro w hw
      by_contra hhon
      refine lemma15 hsync hmono hone hmc hcard hhon ?_ (hWs w hw)
      intro sm hsm
      rcases Finset.mem_union.mp hsm with h | h
      · exact hV1 sm h
      · exact hV2 sm h
    have h1 := Finset.card_le_card hsub
    have h2 := hcb ((x5[k].time : Int))
    omega

/-! ### Lemma 16: the finalized chain grows -/

/-- A justified checkpoint of slot `0` is genesis: a link's target sits strictly above its
    source, so nothing but genesis is justified that early. -/
theorem justified_zero_is_genesis {n : Nat} {V : View Node M}
    {C : Checkpoint (Chain Tx)} (h : JustifiedIn n V C) (hc : C.c = 0) :
    C = ⟨[], 0⟩ := by
  cases h with
  | genesis => rfl
  | @link C₀ _ hj hlink =>
      exfalso
      have h1 := hlink.1
      omega

/-- The common prefix is a prefix of its first argument. -/
theorem commonPrefix_le_left : ∀ a b : Chain Tx, chainLe (commonPrefix a b) a := by
  intro a
  induction a with
  | nil => exact fun b => chainLe_nil []
  | cons x xs ih =>
      intro b
      cases b with
      | nil => exact chainLe_nil _
      | cons y ys =>
          show chainLe (if x = y then x :: commonPrefix xs ys else []) (x :: xs)
          split_ifs with hxy
          · have h := ih ys
            simp only [chainLe, List.isPrefixOf_cons_cons_self]
            exact h
          · exact chainLe_nil _

/-- Anything below both chains is below their common prefix. -/
theorem le_commonPrefix : ∀ {c : Chain Tx} (a b : Chain Tx), chainLe c a → chainLe c b →
    chainLe c (commonPrefix a b) := by
  intro c
  induction c with
  | nil => exact fun a b _ _ => chainLe_nil _
  | cons z zs ih =>
      intro a b ha hb
      cases a with
      | nil => exact absurd ha (by simp [chainLe])
      | cons x xs =>
          cases b with
          | nil => exact absurd hb (by simp [chainLe])
          | cons y ys =>
              rw [chainLe_iff_prefix] at ha hb
              obtain ⟨hzx, hzs⟩ := List.cons_prefix_cons.mp ha
              obtain ⟨hzy, hzs'⟩ := List.cons_prefix_cons.mp hb
              subst hzx
              subst hzy
              show chainLe (z :: zs) (if z = z then z :: commonPrefix xs ys else [])
              rw [if_pos rfl]
              simp only [chainLe, List.isPrefixOf_cons_cons_self]
              exact ih xs ys (chainLe_iff_prefix.mpr hzs) (chainLe_iff_prefix.mpr hzs')

/-- `GJ`'s chain dominates `GF`'s: the finalized checkpoint is justified and no higher, so
    the two nest. -/
theorem gf_le_gj {x5 : Exec Pr5 S} (hsync : SynchronizedClocks x5)
    (hmono : TimeMonotone x5) (hone : OneTickPerReading x5) (hmc : S.MonotoneCorruption)
    (hcb : S.CorruptionBounded Q.f) (hfn : 3 * Q.f < Fintype.card Node)
    {k : Nat} {p : Node} :
    chainLe (gf (Fintype.card Node) x5[k][p].view).ch
      (gj (Fintype.card Node) x5[k][p].view).ch := by
  have hcard : 0 < Fintype.card Node := by omega
  rcases gf_finalized_or_genesis (Fintype.card Node) x5[k][p].view with hgen | hfin
  · rw [hgen]
    exact chainLe_nil _
  · refine justified_nest hsync hmono hone hmc hcb hfn
      (fun sm hsm => views_sound x5 k p _ hsm) (fun sm hsm => views_sound x5 k p _ hsm)
      (chf := (gf (Fintype.card Node) x5[k][p].view).ch)
      (cf := (gf (Fintype.card Node) x5[k][p].view).c)
      (chj := (gj (Fintype.card Node) x5[k][p].view).ch)
      (cj := (gj (Fintype.card Node) x5[k][p].view).c) hfin (gj_justified _ _) ?_
    exact le_gj_c_of_justified hcard hfin.1

/-- `GJ`'s chain is below the merge value on either branch of `fastconfirm`: the quorum
    branch requires exactly that, and the other branch *is* `GJ`'s chain. -/
theorem gj_le_fastConfirm (V : View Node M) (t : Nat) :
    chainLe (gj (Fintype.card Node) V).ch
      ((components (Fintype.card Node) kappa pool proposer).fastConfirm V t).1 := by
  unfold Components.fastConfirm
  rw [MfcEquiv.components_fastConfirmSimple, MfcEquiv.components_gj,
    MfcEquiv.components_prefixLe]
  dsimp only
  by_cases hg : chainLe (gj (Fintype.card Node) V).ch
      (fastConfirmSimple (Fintype.card Node) V t).1
  · rw [if_pos hg]
    exact hg
  · rw [if_neg hg]
    exact chainLe_refl _

set_option maxHeartbeats 1000000 in
/-- **One step of the finalized chain**, with what the same step does to the available
    chain: both stand still, or the vote round writes the common prefix of the (grown)
    available chain and `GF`'s chain, or the fast-confirm round writes `GF`'s chain while
    the available chain comes to dominate `GJ`'s. -/
theorem chFin_step5 {x5 : Exec Pr5 S} {m : Nat} {p : Node} :
    (x5[m + 1][p].st.chFin = x5[m][p].st.chFin ∧
        x5[m + 1][p].st.chAva = x5[m][p].st.chAva) ∨
    (x5[m + 1][p].st.chFin
        = commonPrefix x5[m + 1][p].st.chAva (gf (Fintype.card Node) x5[m][p].view).ch ∧
      chainLe x5[m][p].st.chAva x5[m + 1][p].st.chAva) ∨
    (x5[m + 1][p].st.chFin = (gf (Fintype.card Node) x5[m][p].view).ch ∧
      chainLe (gj (Fintype.card Node) x5[m][p].view).ch x5[m + 1][p].st.chAva) := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  have h5 : x5[m + 1] = _ := exec5_succ (x5 := x5) m
  cases h : x5.lbl m with
  | advance t =>
      refine Or.inl ⟨?_, ?_⟩ <;> rw [h5, h] <;> try rfl
  | tick q t =>
      by_cases hq : q = p
      · subst hq
        have hget : x5[m + 1][q].st
            = (handlerCore (components (Fintype.card Node) kappa pool proposer) Q
              (pick5 x5 m q t) q t x5[m][q].view x5[m][q].st).state := by
          rw [h5, h]
          simp only [applyNodeStepResult_getElem, setClock_getElem, if_pos rfl, if_true]
          rfl
        simp only [handlerCore, apply_ite NodeStepResult.state] at hget
        by_cases hph0 : t % Q.slotLength = 0
        · rw [if_pos hph0] at hget
          refine Or.inl ⟨?_, ?_⟩ <;> rw [hget] <;>
            simp only [apply_ite NodeState.chFin, apply_ite NodeState.chAva, ite_self]
        · rw [if_neg hph0] at hget
          by_cases hph1 : t % Q.slotLength = Q.delta
          · rw [if_pos hph1] at hget
            by_cases hgate : x5[m][q].st.activeAt ≤ t
            · rw [if_pos hgate] at hget
              refine Or.inr (Or.inl ⟨?_, ?_⟩)
              · rw [hget]
                try rfl
              · rw [hget]
                exact Availability5.chAva_le_voteChAva x5 m q t
            · rw [if_neg hgate] at hget
              refine Or.inl ⟨?_, ?_⟩ <;> rw [hget]
              · exact processProposals_chFin _ _ _ _
              · exact MfcEquiv.processProposals_chAva _ _ _ _
          · rw [if_neg hph1] at hget
            by_cases hph2 : t % Q.slotLength = 2 * Q.delta
            · rw [if_pos hph2] at hget
              refine Or.inr (Or.inr ⟨?_, ?_⟩)
              · rw [hget]
                try rfl
              · rw [hget]
                dsimp only
                split_ifs with hgu
                · exact chainLe_trans (gj_le_fastConfirm _ _) hgu
                · exact gj_le_fastConfirm _ _
            · rw [if_neg hph2] at hget
              by_cases hph3 : t % Q.slotLength = 3 * Q.delta
              · rw [if_pos hph3] at hget
                refine Or.inl ⟨?_, ?_⟩ <;> rw [hget] <;> try rfl
              · rw [if_neg hph3] at hget
                refine Or.inl ⟨?_, ?_⟩ <;> rw [hget] <;> try rfl
      · refine Or.inl ⟨?_, ?_⟩ <;> rw [h5, h] <;>
          simp only [applyNodeStepResult_getElem, setClock_getElem, if_neg hq] <;> try rfl
  | deliver q msg =>
      refine Or.inl ⟨?_, ?_⟩ <;> rw [h5, h] <;> by_cases hq : q = p <;>
        first
          | (subst hq
             simp only [applyNodeStepResult_getElem, receive_getElem, if_pos rfl, if_true]
             try rfl)
          | (simp only [applyNodeStepResult_getElem, receive_getElem, if_neg hq]
             try rfl)
  | wake q =>
      refine Or.inl ⟨?_, ?_⟩ <;> rw [h5, h] <;> by_cases hq : q = p <;>
        first
          | (subst hq
             simp only [applyNodeStepResult_getElem, if_pos rfl, if_true]
             try rfl)
          | (simp only [applyNodeStepResult_getElem, if_neg hq]
             try rfl)
  | custom q ev => exact ev.elim
  | adversarial q msg =>
      refine Or.inl ⟨?_, ?_⟩ <;> rw [h5, h] <;> try rfl

set_option maxHeartbeats 1000000 in
/-- **A validator's finalized chain is below `GF`'s chain in any later view of its own**:
    the chain it finalized is a prefix of a checkpoint finalized back then, which is still
    finalized later, and `GF` is the greatest such — so the two nest. -/
theorem chFin_le_gf5 {x5 : Exec Pr5 S} (hsync : SynchronizedClocks x5)
    (hmono : TimeMonotone x5) (hone : OneTickPerReading x5) (hmc : S.MonotoneCorruption)
    (hcb : S.CorruptionBounded Q.f) (hfn : 3 * Q.f < Fintype.card Node)
    {i m : Nat} (him : i ≤ m) (p : Node) :
    chainLe x5[i][p].st.chFin (gf (Fintype.card Node) x5[m][p].view).ch := by
  have hcard : 0 < Fintype.card Node := by omega
  rcases chFin_finalized5 (kappa := kappa) (pool := pool) (proposer := proposer) i p
    with h0 | ⟨ch, c, hfin, hle⟩
  · rw [h0]
    exact chainLe_nil _
  · -- the checkpoint is still finalized in the later view
    have hview : x5[i][p].view ⊆ x5[m][p].view := view_mono_le (Pr' := Pr5) him p
    have hfin' : FinalizedIn (Fintype.card Node) x5[m][p].view ⟨ch, c⟩ :=
      finalizedIn_mono hview hfin
    -- and `GF` dominates it in slot
    have hmem : (⟨ch, c⟩ : Checkpoint (Chain Tx))
        ∈ (checkpoints x5[m][p].view).filter
          (fun C => FinalizedIn (Fintype.card Node) x5[m][p].view C) := by
      rw [Finset.mem_filter]
      exact ⟨justified_mem_checkpoints hcard hfin'.1, hfin'⟩
    have hcle : c ≤ (gf (Fintype.card Node) x5[m][p].view).c := by
      have h := greatestBySlot_c_max hmem
      unfold gf
      exact h
    refine chainLe_trans hle ?_
    -- `GF` is finalized, or genesis — and then the checkpoint is genesis too
    rcases gf_finalized_or_genesis (Fintype.card Node) x5[m][p].view with hgen | hgfin
    · rw [hgen] at hcle ⊢
      have hc0 : c = 0 := by
        simp only [] at hcle
        omega
      have := justified_zero_is_genesis hfin'.1 hc0
      rw [show ch = (⟨ch, c⟩ : Checkpoint (Chain Tx)).ch from rfl, this]
      exact chainLe_refl _
    · exact justified_nest hsync hmono hone hmc hcb hfn
        (fun sm hsm => views_sound x5 m p _ hsm) (fun sm hsm => views_sound x5 m p _ hsm)
        hfin' hgfin.1 hcle

set_option maxHeartbeats 1000000 in
/-- **The finalized chain is a prefix of the available chain** — Definition 7's third
    conjunct, as a state invariant. The vote round writes a common prefix *of* the available
    chain; the fast-confirm round writes `GF`'s chain, which nests below `GJ`'s, which the
    merge value dominates, which the write then adopts. -/
theorem chFin_le_chAva5 {x5 : Exec Pr5 S} (hsync : SynchronizedClocks x5)
    (hmono : TimeMonotone x5) (hone : OneTickPerReading x5) (hmc : S.MonotoneCorruption)
    (hcb : S.CorruptionBounded Q.f) (hfn : 3 * Q.f < Fintype.card Node)
    (i : Nat) (p : Node) : chainLe x5[i][p].st.chFin x5[i][p].st.chAva := by
  induction i with
  | zero =>
      show chainLe ((x5.cfg 0)[p]).st.chFin ((x5.cfg 0)[p]).st.chAva
      rw [x5.init.2.1 p]
      exact chainLe_refl _
  | succ i ih =>
      rcases chFin_step5 (x5 := x5) (m := i) (p := p) with
        ⟨hf, ha⟩ | ⟨hf, -⟩ | ⟨hf, hgja⟩
      · rw [hf, ha]
        exact ih
      · rw [hf]
        exact commonPrefix_le_left _ _
      · rw [hf]
        exact chainLe_trans (gf_le_gj hsync hmono hone hmc hcb hfn) hgja

set_option maxHeartbeats 1000000 in
/-- **Lemma 16** (`Lemma 16, arXiv:2601.03862v1 p.23`). A validator's finalized chain only
    grows.

    The paper argues by contradiction on the first violating round; here it is a plain
    induction over the step, and the two writes are bounded separately: the fast-confirm
    write is `GF`'s chain, above the old finalized chain by `chFin_le_gf5`; the vote write is
    a common prefix, and the old finalized chain sits below both of its arguments — below
    `GF`'s chain by the same lemma, and below the new available chain because it is below the
    old one (`chFin_le_chAva5`), which the vote round's maximum keeps.

    This route needs no synchrony and no merge-in-between argument, which is what the
    paper's Case 1 spends its length on. -/
theorem lemma16 {x5 : Exec Pr5 S} (hsync : SynchronizedClocks x5)
    (hmono : TimeMonotone x5) (hone : OneTickPerReading x5) (hmc : S.MonotoneCorruption)
    (hcb : S.CorruptionBounded Q.f) (hfn : 3 * Q.f < Fintype.card Node)
    (p : Node) {r r' : Nat} (h : r ≤ r') :
    chainLe x5[r][p].st.chFin x5[r'][p].st.chFin := by
  induction r', h using Nat.le_induction with
  | base => exact chainLe_refl _
  | succ m hm ih =>
      rcases chFin_step5 (x5 := x5) (m := m) (p := p) with
        ⟨hf, -⟩ | ⟨hf, hava⟩ | ⟨hf, -⟩
      · rw [hf]
        exact ih
      · rw [hf]
        refine le_commonPrefix _ _ ?_ (chFin_le_gf5 hsync hmono hone hmc hcb hfn hm p)
        exact chainLe_trans ih
          (chainLe_trans (chFin_le_chAva5 hsync hmono hone hmc hcb hfn m p) hava)
      · rw [hf]
        exact chFin_le_gf5 hsync hmono hone hmc hcb hfn hm p

/-! ### Theorem 6's safety half -/

set_option maxHeartbeats 1000000 in
/-- **The finalized chain is safe**: any two validators' finalized chains are comparable,
    at any two points of the execution. Each prefixes a checkpoint finalized in its own
    view; the two checkpoints nest (`justified_nest`, at whichever has the larger slot);
    and prefixes of one chain are comparable. -/
theorem chFin_comparable {x5 : Exec Pr5 S} (hsync : SynchronizedClocks x5)
    (hmono : TimeMonotone x5) (hone : OneTickPerReading x5) (hmc : S.MonotoneCorruption)
    (hcb : S.CorruptionBounded Q.f) (hfn : 3 * Q.f < Fintype.card Node)
    (i : Nat) (p : Node) (j : Nat) (q : Node) :
    chainLe x5[i][p].st.chFin x5[j][q].st.chFin ∨
      chainLe x5[j][q].st.chFin x5[i][p].st.chFin := by
  have hcard : 0 < Fintype.card Node := by omega
  rcases chFin_finalized5 (kappa := kappa) (pool := pool) (proposer := proposer) i p
    with h0 | ⟨ch1, c1, hfin1, hle1⟩
  · exact Or.inl (by rw [h0]; exact chainLe_nil _)
  rcases chFin_finalized5 (kappa := kappa) (pool := pool) (proposer := proposer) j q
    with h0 | ⟨ch2, c2, hfin2, hle2⟩
  · exact Or.inr (by rw [h0]; exact chainLe_nil _)
  -- both views' messages are in the log at the later index
  have hk1 : ∀ sm ∈ x5[i][p].view, sm ∈ x5[max i j].sent := fun sm hsm =>
    mem_sent_mono (le_max_left i j) (views_sound x5 i p _ hsm)
  have hk2 : ∀ sm ∈ x5[j][q].view, sm ∈ x5[max i j].sent := fun sm hsm =>
    mem_sent_mono (le_max_right i j) (views_sound x5 j q _ hsm)
  rcases Nat.le_total c1 c2 with hc | hc
  · have hnest := justified_nest hsync hmono hone hmc hcb hfn hk1 hk2 hfin1 hfin2.1 hc
    exact comparable_of_common_extension (chainLe_trans hle1 hnest) hle2
  · have hnest := justified_nest hsync hmono hone hmc hcb hfn hk2 hk1 hfin2 hfin1.1 hc
    exact comparable_of_common_extension hle1 (chainLe_trans hle2 hnest)

/-! ### Lemma 17: the honest proposal fixes every active's frozen checkpoint -/

/-- Once a fold's tracked field reaches `J`, no step whose writes are all `J` can move it
    off again. -/
theorem foldl_keeps {α β : Type} {f : β → α → β} {pr : β → Checkpoint (Chain Tx)}
    {J : Checkpoint (Chain Tx)} :
    ∀ (l : List α) (acc : β),
      (∀ (acc' : β) (a : α), a ∈ l → (pr acc').c ≤ J.c →
        pr (f acc' a) = pr acc' ∨ pr (f acc' a) = J) →
      pr acc = J → pr (l.foldl f acc) = J := by
  intro l
  induction l with
  | nil => exact fun acc _ h => h
  | cons a l ih =>
      intro acc hstep hacc
      rw [List.foldl_cons]
      refine ih _ (fun acc' b hb => hstep acc' b (List.mem_cons_of_mem a hb)) ?_
      rcases hstep acc a List.mem_cons_self (by rw [hacc]) with h | h
      · rw [h, hacc]
      · exact h

/-- **A fold pinned to one value**: every step either stands still or writes `J`, the seed
    sits no higher than `J`, and one designated element writes `J` — so the fold ends at
    `J`. -/
theorem foldl_absorbing {α β : Type} {f : β → α → β} {pr : β → Checkpoint (Chain Tx)}
    {J : Checkpoint (Chain Tx)} {l : List α}
    (hstep : ∀ (acc : β) (a : α), a ∈ l → (pr acc).c ≤ J.c →
      pr (f acc a) = pr acc ∨ pr (f acc a) = J)
    {a₀ : α} (ha₀ : a₀ ∈ l)
    (hfire : ∀ acc : β, (pr acc).c ≤ J.c → pr (f acc a₀) = J)
    {s : β} (hs : (pr s).c ≤ J.c) :
    pr (l.foldl f s) = J := by
  induction l generalizing s with
  | nil => cases ha₀
  | cons a l ih =>
      rw [List.foldl_cons]
      have hstep' : ∀ (acc : β) (b : α), b ∈ l → (pr acc).c ≤ J.c →
          pr (f acc b) = pr acc ∨ pr (f acc b) = J :=
        fun acc b hb => hstep acc b (List.mem_cons_of_mem a hb)
      rcases List.mem_cons.mp ha₀ with rfl | ha₀l
      · exact foldl_keeps l _ hstep' (hfire s hs)
      · refine ih hstep' ha₀l ?_
        rcases hstep s a List.mem_cons_self hs with h | h
        · rw [h]
          exact hs
        · rw [h]

set_option maxHeartbeats 1000000 in
/-- **The proposal fold adopts the one checkpoint its slot's proposals carry.** If every
    valid slot-`t` proposal in the view names the same justified checkpoint `J`, one such
    proposal is in the view, and the seed does not already sit above `J`, then the fold's
    frozen checkpoint *is* `J`. This is what makes every active validator of an
    honest-proposer slot freeze the *same* checkpoint — Lemma 17's conclusion. -/
theorem processProposals_gjFrozen_eq {V : View Node M} {t : Nat}
    {s : NodeState Node (Chain Tx) (QCert Node Tx)} {J : Checkpoint (Chain Tx)}
    (hJj : JustifiedIn (Fintype.card Node) V J) (hseed : s.gjFrozen.c ≤ J.c)
    (huniq : ∀ sm ∈ V, ∀ chp chC qc gjp, sm.msg = .propose chp chC qc gjp t →
      ValidProposal5 (Fintype.card Node) proposer V sm → gjp = J)
    {sm₀ : SignedMsg Node M} (hsm₀ : sm₀ ∈ V) {chp₀ chC₀ : Chain Tx}
    {qc₀ : Option (QCert Node Tx)}
    (hmsg₀ : sm₀.msg = .propose chp₀ chC₀ qc₀ J t)
    (hvalid₀ : ValidProposal5 (Fintype.card Node) proposer V sm₀) :
    (processProposals (components (Fintype.card Node) kappa pool proposer) V t s).gjFrozen
      = J := by
  unfold processProposals
  refine foldl_absorbing (pr := NodeState.gjFrozen) ?_ (Finset.mem_toList.mpr hsm₀) ?_ hseed
  · -- every step stands still or writes `J`
    intro acc a ha hacc
    have haV : a ∈ V := Finset.mem_toList.mp ha
    obtain ⟨asd, amsg⟩ := a
    cases amsg with
    | vote ch src tgt t' => exact Or.inl rfl
    | propose chp chC qc gjp t' =>
        dsimp only
        simp only [apply_ite NodeState.gjFrozen, ite_self]
        by_cases hg : t' = t ∧
            (components (Fintype.card Node) kappa pool proposer).validProposal V
              ⟨asd, .propose chp chC qc gjp t'⟩ ∧
            (components (Fintype.card Node) kappa pool proposer).justified gjp V = true ∧
            acc.gjFrozen.c ≤ gjp.c
        · rw [if_pos hg]
          exact Or.inr (huniq _ haV chp chC qc gjp (by rw [hg.1]) hg.2.1)
        · rw [if_neg hg]
          exact Or.inl rfl
  · -- and the designated proposal writes it
    intro acc hacc
    obtain ⟨asd, amsg⟩ := sm₀
    have hm0 : amsg = Msg.propose chp₀ chC₀ qc₀ J t := hmsg₀
    subst hm0
    dsimp only
    simp only [apply_ite NodeState.gjFrozen, ite_self]
    rw [if_pos (⟨trivial, hvalid₀, decide_eq_true hJj, hacc⟩ :
      True ∧ (components (Fintype.card Node) kappa pool proposer).validProposal V
          ⟨asd, .propose chp₀ chC₀ qc₀ J t⟩ ∧
        (components (Fintype.card Node) kappa pool proposer).justified J V = true ∧
        acc.gjFrozen.c ≤ J.c)]

/-- **An honest proposal's fields, at its own tick**: the sender is the slot's proposer, the
    carried checkpoint is `GJ` of its view then, and the proposed chain, fast-confirmed chain
    and certificate are what `fastconfirm` and the fork choice returned. -/
theorem propose_fields5 {x5 : Exec Pr5 S} (hsync : SynchronizedClocks x5)
    (hmc : S.MonotoneCorruption) (hmono : TimeMonotone x5)
    {t : Nat} {vp : Node} {chp chC : Chain Tx} {qc : Option (QCert Node Tx)}
    {gjp : Checkpoint (Chain Tx)} {ip : Nat}
    (hsent : (⟨vp, Msg.propose chp chC qc gjp t⟩ : SignedMsg Node M) ∈ x5[ip].sent)
    (hhon_i : vp ∉ S.adv ((x5[ip].time : Int))) :
    vp = proposer t ∧ ∃ kp, kp < ip ∧ x5.lbl kp = .tick vp (Q.slotLength * t) ∧
      x5[kp].time = Q.slotLength * t ∧ x5.Awake kp vp ∧
      (⟨vp, Msg.propose chp chC qc gjp t⟩ : SignedMsg Node M)
        ∈ x5[kp + 1].sent - x5[kp].sent ∧
      gjp = gj (Fintype.card Node) x5[kp][vp].view ∧
      chp = extend pool ((components (Fintype.card Node) kappa pool proposer).mfc
          x5[kp][vp].view x5[kp][vp].view
          ((components (Fintype.card Node) kappa pool proposer).fastConfirm
            x5[kp][vp].view (t - 1)).1 t) t ∧
      chC = ((components (Fintype.card Node) kappa pool proposer).fastConfirm
        x5[kp][vp].view (t - 1)).1 ∧
      qc = ((components (Fintype.card Node) kappa pool proposer).fastConfirm
        x5[kp][vp].view (t - 1)).2 := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  obtain ⟨kp, hkpi, hlblp, hemp⟩ := MfcEquiv.propose_provenance5 hsync hmc hmono hsent
    hhon_i rfl
  have htkp : x5[kp].time = Q.slotLength * t := MfcEquiv.tick_reading5 hsync hlblp
  have hhonp : vp ∉ S.adv ((x5[kp].time : Int)) := fun hadv =>
    hhon_i (hmc _ _ (by exact_mod_cast time_le_of_le hmono (Nat.le_of_lt hkpi)) hadv)
  rcases emitted_step (C := components (Fintype.card Node) kappa pool proposer) hemp
    with ⟨tr, hlbl', -, -, -, pk, -, hsend⟩ | hadv
  · have hSL0 : 0 < Q.slotLength := by omega
    have hmod0 : (Q.slotLength * t) % Q.slotLength = 0 := Nat.mul_mod_right _ _
    have hdiv0 : (Q.slotLength * t) / Q.slotLength = t :=
      Nat.mul_div_cancel_left t hSL0
    have htr : tr = Q.slotLength * t := by
      rw [hlblp] at hlbl'
      injection hlbl' with h1 h2
      exact h2.symm
    subst htr
    obtain ⟨hprop, -, hm⟩ := MfcEquiv.handler_propose_send hmod0 hsend
    rw [hdiv0] at hprop hm
    rw [Msg.propose.injEq] at hm
    have hawk : x5.Awake kp vp := by
      have hstep := x5.step kp
      rw [hlblp] at hstep
      have h := hstep.1
      simp only [spec] at h
      exact h
    refine ⟨hprop, kp, hkpi, hlblp, htkp, hawk, hemp,
      by rw [hm.2.2.2.1, MfcEquiv.components_gj], ?_, hm.2.1, hm.2.2.1⟩
    rw [hm.1, MfcEquiv.components_extend]
  · exact absurd hadv hhonp

set_option maxHeartbeats 1000000 in
/-- **An honest proposal is valid in any view that has caught up with the proposer's.** The
    certificate clause is discharged on `fastconfirm`'s quorum branch by the certificate the
    fast confirmation itself carries (its votes are in the proposer's view, hence in the
    later one), and on the `GJ` branch by the justification rung — the proposal's chain
    *is* the greatest justified chain there. Algorithm 2's counterpart is the `hvalidprop`
    step inside `chi_le_mfc`. -/
theorem honest_propose_valid5 {x5 : Exec Pr5 S}
    {t : Nat} {vp : Node} {chp chC : Chain Tx} {qc : Option (QCert Node Tx)}
    {gjp : Checkpoint (Chain Tx)} {kp : Nat}
    (hprop : vp = proposer t)
    (hgjp : gjp = gj (Fintype.card Node) x5[kp][vp].view)
    (hchp : chp = extend pool ((components (Fintype.card Node) kappa pool proposer).mfc
        x5[kp][vp].view x5[kp][vp].view
        ((components (Fintype.card Node) kappa pool proposer).fastConfirm
          x5[kp][vp].view (t - 1)).1 t) t)
    (hchC : chC = ((components (Fintype.card Node) kappa pool proposer).fastConfirm
      x5[kp][vp].view (t - 1)).1)
    (hqc : qc = ((components (Fintype.card Node) kappa pool proposer).fastConfirm
      x5[kp][vp].view (t - 1)).2)
    {V : View Node M} (hsub : ∀ sm ∈ x5[kp][vp].view, sm ∈ V) :
    ValidProposal5 (Fintype.card Node) proposer V
      ⟨vp, Msg.propose chp chC qc gjp t⟩ := by
  refine ⟨hprop, ?_, ?_, ?_⟩
  · rw [hchp]
    exact proposedAt_extend _ _ _
  · rw [hchp, hchC]
    exact chainLe_trans (base_le_mfc _ _ _ _) (chainLe_extend _ _ _)
  · -- the rung, by `fastconfirm`'s branch
    have hfc : (components (Fintype.card Node) kappa pool proposer).fastConfirm
          x5[kp][vp].view (t - 1)
        = if chainLe (gj (Fintype.card Node) x5[kp][vp].view).ch
              (fastConfirmSimple (Fintype.card Node) x5[kp][vp].view (t - 1)).1 then
            fastConfirmSimple (Fintype.card Node) x5[kp][vp].view (t - 1)
          else ((gj (Fintype.card Node) x5[kp][vp].view).ch, none) := by
      unfold Components.fastConfirm
      rw [MfcEquiv.components_fastConfirmSimple, MfcEquiv.components_gj,
        MfcEquiv.components_prefixLe]
    by_cases hg : chainLe (gj (Fintype.card Node) x5[kp][vp].view).ch
        (fastConfirmSimple (Fintype.card Node) x5[kp][vp].view (t - 1)).1
    · -- the quorum branch: the fast confirmation's own certificate
      rw [hfc, if_pos hg] at hchC hqc
      by_cases hnil : chC = []
      · exact Or.inl hnil
      · refine Or.inr (Or.inl ?_)
        cases hsnd : (fastConfirmSimple (Fintype.card Node) x5[kp][vp].view (t - 1)).2 with
        | none =>
            exact absurd (hchC.trans (fastConfirmSimple_none_fst hsnd)) hnil
        | some cert =>
            have hfcpair : fastConfirmSimple (Fintype.card Node) x5[kp][vp].view (t - 1)
                = ((fastConfirmSimple (Fintype.card Node) x5[kp][vp].view (t - 1)).1,
                  some cert) := by
              rw [← hsnd]
            have hcertdef := fastConfirmSimple_snd_spec hfcpair
            refine ⟨cert, by rw [hqc, hsnd], ?_, ?_⟩
            · rcases fastConfirmSimple_fst_cases (n := Fintype.card Node) x5[kp][vp].view
                  (t - 1) with h0 | hsupp
              · exact absurd (hchC.trans h0) hnil
              · rw [hcertdef, Finset.image_image]
                simpa [Function.comp_def] using hsupp
            · rintro e hemem
              rw [hcertdef] at hemem
              obtain ⟨sm, hsm_supp, rfl⟩ := Finset.mem_image.mp hemem
              rw [Finset.mem_filter] at hsm_supp
              obtain ⟨hsmv, hsmslot, hsmch⟩ := hsm_supp
              have hsmview : sm ∈ x5[kp][vp].view := by
                simp only [votes, Finset.mem_filter] at hsmv
                exact hsmv.1
              obtain ⟨e0, s0, t0', slot0, hm0⟩ := exists_vote_of_mem_votes hsmv
              refine ⟨by rw [hchC]; exact hsmch, by omega, s0, t0', ?_⟩
              have heq : (⟨sm.sender, Msg.vote (msgChain sm.msg) s0 t0' (msgSlot sm.msg)⟩ :
                  SignedMsg Node M) = sm := by
                have h1 : msgChain sm.msg = e0 := by rw [hm0]; exact rfl
                have h2 : msgSlot sm.msg = slot0 := by rw [hm0]; exact rfl
                rw [h1, h2, ← hm0]
              rw [heq]
              exact hsub sm hsmview
    · -- the `GJ` branch: the proposal's chain is the greatest justified chain
      rw [hfc, if_neg hg] at hchC hqc
      refine Or.inr (Or.inr ⟨hqc, ?_, ?_⟩)
      · rw [hchC, hgjp]
      · rw [hgjp]
        exact justifiedIn_mono hsub (gj_justified _ _)

set_option maxHeartbeats 2000000 in
/-- **Lemma 17** (`Lemma 17, arXiv:2601.03862v1 p.23`), the conclusion the re-justification
    argument runs on: in a slot with an honest proposer, every active validator's vote tick
    freezes *the proposal's own* greatest-justified checkpoint —
    `GJfrozen^{voting(t)}_i = GJ_p`.

    The three things `processProposals_gjFrozen_eq` needs: `GJ_p` is justified in the voter's
    view (it is `GJ` of the proposer's view, which synchrony has delivered by the vote
    reading); the checkpoint the voter carries in was frozen at the previous slot's merge, a
    view the proposer had also received, so its slot cannot exceed `GJ_p`'s; and every valid
    slot-`t` proposal in the voter's view *is* this proposal, because validity pins the
    sender to the slot's proposer and that honest proposer's tick sends once. -/
theorem lemma17_gjFrozen {x5 : Exec Pr5 S} (H5 : SettingGA Q S x5)
    {t : Nat} (ht : 1 ≤ t)
    {vp : Node} {chp chC : Chain Tx} {qc : Option (QCert Node Tx)}
    {gjp : Checkpoint (Chain Tx)} {ip : Nat}
    (hsent : (⟨vp, Msg.propose chp chC qc gjp t⟩ : SignedMsg Node M) ∈ x5[ip].sent)
    (hhon_i : vp ∉ S.adv ((x5[ip].time : Int)))
    (hhon_t : vp ∉ S.adv (Q.voting (t : Int)))
    {vi : Node} {j : Nat} (hact : vi ∈ Active Q S (t : Int))
    (hlbl : x5.lbl j = .tick vi (Q.slotLength * t + Q.delta)) :
    (processProposals (components (Fintype.card Node) kappa pool proposer)
      x5[j][vi].view t x5[j][vi].st).gjFrozen = gjp := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  obtain ⟨⟨hmc, -, hsync, hmono, -, hdiv, hdil⟩, hstepw, hwpt, hone, ⟨hsyn, hrel⟩, hslp,
    ⟨hcb, hfn⟩, hgst⟩ := id H5
  have hcard : 0 < Fintype.card Node := by omega
  have hg0 : Q.gst = 0 := hgst
  have htj : x5[j].time = Q.slotLength * t + Q.delta := MfcEquiv.tick_reading5 hsync hlbl
  have hAwj : x5.Awake j vi := by
    have hstep := x5.step j
    rw [hlbl] at hstep
    have h := hstep.1
    simp only [spec] at h
    exact h
  have hvot : Q.voting (t : Int) = ((Q.slotLength * t + Q.delta : Nat) : Int) := by
    unfold Params.voting
    push_cast
    omega
  -- the proposer's tick: its view, its emission, `GJ_p`, and the message's shape
  obtain ⟨hprop, kp, hkpi, hlblp, htkp, hawkp, hemp, hgjp, hchp, hchC, hqc⟩ :=
    propose_fields5 hsync hmc hmono hsent hhon_i
  have htkp1 : x5[kp + 1].time = x5[kp].time := MfcEquiv.tick_time5 hlblp
  -- the proposal, and everything the proposer had seen, reach the voter's view
  have hview : (⟨vp, Msg.propose chp chC qc gjp t⟩ : SignedMsg Node M)
      ∈ x5[j][vi].view := by
    refine hsyn (kp + 1) j vi _ (MfcEquiv.mem_of_mem_sub hemp) ?_ hAwj
    rw [htkp1, htkp, htj]
    omega
  have hviewp : ∀ sm ∈ x5[kp][vp].view, sm ∈ x5[j][vi].view := by
    intro sm hsm
    refine hsyn kp j vi _ (views_sound x5 kp vp _ hsm) ?_ hAwj
    rw [htkp, htj]
    omega
  have hJj : JustifiedIn (Fintype.card Node) x5[j][vi].view gjp := by
    rw [hgjp]
    exact justifiedIn_mono hviewp (gj_justified _ _)
  -- the carried checkpoint was frozen at the previous merge, which the proposer had seen
  obtain ⟨t0, rfl⟩ : ∃ t0, t = t0 + 1 := ⟨t - 1, by omega⟩
  have hact' : vi ∈ Active Q S ((t0 : Int) + 1) := by
    have hcast : (((t0 + 1 : Nat)) : Int) = (t0 : Int) + 1 := by push_cast; omega
    rw [← hcast]
    exact hact
  obtain ⟨im, himj, htim, -, -, -, hgf⟩ :=
    MfcEquiv.frozen_at_vote_tick5 hsync hstepw hdil hone hact' hlbl
  have hexp : Q.slotLength * (t0 + 1) = Q.slotLength * t0 + Q.slotLength := Nat.mul_succ ..
  have hseed : x5[j][vi].st.gjFrozen.c ≤ gjp.c := by
    rw [hgf, hgjp]
    refine le_gj_c_of_justified hcard (justifiedIn_mono ?_ (gj_justified _ _))
    intro sm hsm
    refine hsyn im kp vp _ (views_sound x5 im vi _ hsm) ?_ hawkp
    rw [htim, htkp]
    omega
  -- every valid slot-`t` proposal in the voter's view is this very message
  have huniq : ∀ sm ∈ x5[j][vi].view, ∀ chp' chC' qc' gjp',
      sm.msg = .propose chp' chC' qc' gjp' (t0 + 1) →
      ValidProposal5 (Fintype.card Node) proposer x5[j][vi].view sm → gjp' = gjp := by
    intro sm hsm chp' chC' qc' gjp' hmsg' hvalid'
    have hsender : sm.sender = vp := by
      have h : sm.sender = proposer (t0 + 1) := by
        have hv := hvalid'
        unfold ValidProposal5 at hv
        rw [hmsg'] at hv
        exact hv.1
      rw [h, hprop]
    have hsmlog : sm ∈ x5[j].sent := views_sound x5 j vi _ hsm
    have hhonsm : sm.sender ∉ S.adv ((x5[j].time : Int)) := by
      rw [hsender, htj, ← hvot]
      exact hhon_t
    obtain ⟨k', hk'j, hlbl', hem'⟩ :=
      MfcEquiv.propose_provenance5 hsync hmc hmono hsmlog hhonsm hmsg'
    rw [hsender] at hlbl'
    have hk'kp : k' = kp := hone k' kp vp _ hlbl' hlblp
    subst hk'kp
    have heq := tick_sends_subsingleton5 hlblp hem' hemp
    rw [heq] at hmsg'
    simp only at hmsg'
    rw [Msg.propose.injEq] at hmsg'
    exact hmsg'.2.2.2.1.symm
  exact processProposals_gjFrozen_eq hJj hseed huniq hview rfl
    (honest_propose_valid5 hprop hgjp hchp hchC hqc hviewp)

/-! ### Lemma 18's engine: a quorum of fin-votes justifies its target -/

/-- **A quorum of matching fin-votes justifies the target.** The senders of the votes for
    the pair `C → C'` are counted, so a set of validators each of which is *some* such
    vote's sender bounds the link's voter set from below; with fin-vote validity (`C.c <
    C'.c` and `C.ch ⪯ C'.ch`) and `C` already justified, `C'` is justified too. -/
theorem justified_of_quorum_votes {V : View Node M} {C C' : Checkpoint (Chain Tx)}
    (hC : JustifiedIn (Fintype.card Node) V C)
    (hslot : C.c < C'.c) (hchain : chainLe C.ch C'.ch)
    {W : Finset Node} (hW : 2 * Fintype.card Node ≤ 3 * W.card)
    (hvotes : ∀ w ∈ W, ∃ e : Chain Tx, ∃ s : Nat,
      (⟨w, Msg.vote e C C' s⟩ : SignedMsg Node M) ∈ V) :
    JustifiedIn (Fintype.card Node) V C' := by
  refine JustifiedIn.link hC ⟨hslot, hchain, ?_⟩
  -- the quorum's members are all link voters
  have hsub : W ⊆ linkVoters V C C' := by
    intro w hw
    obtain ⟨e, s, hmem⟩ := hvotes w hw
    refine Finset.mem_image.mpr ⟨⟨w, Msg.vote e C C' s⟩, ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · simp only [votes, Finset.mem_filter]
      exact ⟨hmem, trivial⟩
    · exact ⟨rfl, rfl⟩
  have := Finset.card_le_card hsub
  omega

/-! ### Uniqueness: what a slot's honest agreement pins down -/

set_option maxHeartbeats 1000000 in
/-- **A slot's fast confirmation is exactly the chain its honest voters agreed on.** It is at
    least `chp`, that being quorum-supported and a candidate; and at most `chp`, because its
    own quorum holds an honest validator whose slot-`t` vote *is* `chp` and support flows down
    from extensions. -/
theorem fcs_eq_of_honest_agreement {x5 : Exec Pr5 S} (hsync : SynchronizedClocks x5)
    (hone : OneTickPerReading x5) (hmc : S.MonotoneCorruption) (hmono : TimeMonotone x5)
    (hcb : S.CorruptionBounded Q.f) (hfn : 3 * Q.f < Fintype.card Node)
    {t : Nat} {chp : Chain Tx} (hchp : chp ≠ []) {i : Nat} {w : Node}
    (hsupp : 2 * Fintype.card Node ≤ 3 * (((votes x5[i][w].view).filter (fun sm =>
      msgSlot sm.msg = t ∧ chainLe chp (msgChain sm.msg))).image SignedMsg.sender).card)
    (hall : ∀ sm ∈ votes x5[i][w].view, msgSlot sm.msg = t →
      sm.sender ∉ S.adv ((x5[i].time : Int)) → msgChain sm.msg = chp) :
    (fastConfirmSimple (Fintype.card Node) x5[i][w].view t).1 = chp := by
  have hcard : 0 < Fintype.card Node := by omega
  -- `chp` is a candidate, so the fast confirmation is at least as long
  have hcand : chp ∈ candidates x5[i][w].view ([] : Chain Tx) := by
    have hpos : 0 < (((votes x5[i][w].view).filter (fun sm =>
        msgSlot sm.msg = t ∧ chainLe chp (msgChain sm.msg))).image
          SignedMsg.sender).card := by omega
    rw [Finset.card_pos] at hpos
    obtain ⟨q, hq⟩ := hpos
    obtain ⟨sm, hsm, -⟩ := Finset.mem_image.mp hq
    rw [Finset.mem_filter] at hsm
    exact mem_candidates_of_extends hsm.1 hsm.2.2
  have hlen := fastConfirmSimple_length_ge (n := Fintype.card Node) hchp hcand hsupp
  have hpos : 0 < chp.length := by
    cases hb : chp with
    | nil => exact absurd hb hchp
    | cons _ _ => simp [hb]
  -- and its own quorum holds an honest validator, whose vote is `chp`
  rcases fastConfirmSimple_fst_cases (n := Fintype.card Node) x5[i][w].view t
    with h0 | hsuppF
  · exfalso
    rw [h0] at hlen
    simp only [List.length_nil] at hlen
    omega
  · obtain ⟨q, hqmem, hqhon⟩ :=
      exists_honest_sender (r := ((x5[i].time : Int))) hcb hfn hsuppF
    obtain ⟨sm, hsm, hsmq⟩ := Finset.mem_image.mp hqmem
    rw [Finset.mem_filter] at hsm
    have hchain : msgChain sm.msg = chp :=
      hall sm hsm.1 hsm.2.1 (by rw [hsmq]; exact hqhon)
    -- the fast confirmation is below that vote's chain, hence below `chp`
    have hle : chainLe (fastConfirmSimple (Fintype.card Node) x5[i][w].view t).1 chp := by
      rw [← hchain]
      exact hsm.2.2
    -- with the length bound, the two are equal
    exact chainLe_antisymm hle (chainLe_of_comparable _ _ (Or.inr hle) hlen)

set_option maxHeartbeats 1000000 in
/-- **Nothing above slot `t` is justified before slot `t+1`'s votes exist.** A justified
    checkpoint is genesis or a link's target; the link's quorum holds an honest validator,
    whose fin-vote's slot *is* that checkpoint slot — and an honest vote for slot `s` is not
    in the log before `voting(s)`. -/
theorem no_justified_above_slot {x5 : Exec Pr5 S} (hsync : SynchronizedClocks x5)
    (hone : OneTickPerReading x5) (hmc : S.MonotoneCorruption) (hmono : TimeMonotone x5)
    (hcb : S.CorruptionBounded Q.f) (hfn : 3 * Q.f < Fintype.card Node)
    {i : Nat} {w : Node} {t : Nat} (htime : x5[i].time < Q.slotLength * (t + 1) + Q.delta)
    {C : Checkpoint (Chain Tx)} (hC : JustifiedIn (Fintype.card Node) x5[i][w].view C) :
    C.c ≤ t := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  cases hC with
  | genesis => exact Nat.zero_le t
  | @link C₀ C₁ hjust hlk =>
      obtain ⟨q, hqmem, hqhon⟩ :=
        exists_honest_sender (r := ((x5[i].time : Int))) hcb hfn hlk.2.2
      unfold linkVoters at hqmem
      obtain ⟨sm, hsm, hsmq⟩ := Finset.mem_image.mp hqmem
      rw [Finset.mem_filter] at hsm
      obtain ⟨e, src, tgt, s, hmsg⟩ := exists_vote_of_mem_votes hsm.1
      have hst : tgt = C := by
        have h2 := hsm.2
        rw [hmsg] at h2
        exact h2.2
      have hsmlog : sm ∈ x5[i].sent := by
        have h := hsm.1
        simp only [votes, Finset.mem_filter] at h
        exact views_sound x5 i w _ h.1
      have hhonsm : sm.sender ∉ S.adv ((x5[i].time : Int)) := by
        rw [hsmq]
        exact hqhon
      obtain ⟨htgt, -⟩ := vote_fields5 hsync hmc hmono hsmlog hhonsm hmsg
      have hvl := voting_le_of_vote_mem
        (C := components (Fintype.card Node) kappa pool proposer) hsync hmc hmono hsmlog
        hhonsm hmsg
      rw [hst] at htgt
      have hs : s ≤ t := by
        by_contra hgt
        have h1 : Q.slotLength * (t + 1) ≤ Q.slotLength * s :=
          Nat.mul_le_mul_left _ (by omega)
        omega
      omega

set_option maxHeartbeats 1000000 in
/-- **A slot's justified checkpoint is the one its honest voters targeted.** Any justified
    checkpoint of slot `t ≥ 1` is a link's target, its quorum holds an honest validator, and
    that validator's fin-vote — whose slot is the checkpoint's — targets `T`. -/
theorem justified_slot_unique {x5 : Exec Pr5 S} (hsync : SynchronizedClocks x5)
    (hone : OneTickPerReading x5) (hmc : S.MonotoneCorruption) (hmono : TimeMonotone x5)
    (hcb : S.CorruptionBounded Q.f) (hfn : 3 * Q.f < Fintype.card Node)
    {i : Nat} {w : Node} {t : Nat} (ht : 1 ≤ t) {T : Checkpoint (Chain Tx)}
    (hall : ∀ sm ∈ votes x5[i][w].view, msgSlot sm.msg = t →
      sm.sender ∉ S.adv ((x5[i].time : Int)) →
      ∀ (e : Chain Tx) (src tgt : Checkpoint (Chain Tx)) (s : Nat),
        sm.msg = .vote e src tgt s → tgt = T)
    {C : Checkpoint (Chain Tx)} (hC : JustifiedIn (Fintype.card Node) x5[i][w].view C)
    (hCc : C.c = t) : C = T := by
  cases hC with
  | genesis =>
      exfalso
      have h0 : (0 : Nat) = t := hCc
      omega
  | @link C₀ C₁ hjust hlk =>
      obtain ⟨q, hqmem, hqhon⟩ :=
        exists_honest_sender (r := ((x5[i].time : Int))) hcb hfn hlk.2.2
      unfold linkVoters at hqmem
      obtain ⟨sm, hsm, hsmq⟩ := Finset.mem_image.mp hqmem
      rw [Finset.mem_filter] at hsm
      obtain ⟨e, src, tgt, s, hmsg⟩ := exists_vote_of_mem_votes hsm.1
      have hst : tgt = C := by
        have h2 := hsm.2
        rw [hmsg] at h2
        exact h2.2
      have hsmlog : sm ∈ x5[i].sent := by
        have h := hsm.1
        simp only [votes, Finset.mem_filter] at h
        exact views_sound x5 i w _ h.1
      have hhonsm : sm.sender ∉ S.adv ((x5[i].time : Int)) := by
        rw [hsmq]
        exact hqhon
      obtain ⟨htgt, -⟩ := vote_fields5 hsync hmc hmono hsmlog hhonsm hmsg
      have hslot : msgSlot sm.msg = t := by
        rw [hmsg]
        show s = t
        rw [hst] at htgt
        omega
      rw [← hst]
      exact hall sm hsm.1 hslot hhonsm e src tgt s hmsg

/-! ### Lemma 18: re-justification -/

/-- **After the global awake time, every honest validator is active.** `Active`'s window is
    `[voting(t) - 3Δ, voting(t)]`, so a slot whose window starts past `GAT` has every
    validator that is honest throughout it awake throughout it. -/
theorem active_of_globalAwake (hga : S.GlobalAwakeTime Q.gat Finset.univ)
    {t : Nat} (hgat : (Q.gat : Int) ≤ Q.voting (t : Int) - 3 * (Q.delta : Int))
    {p : Node} (hhon : ∀ r : Int, Q.voting (t : Int) - 3 * (Q.delta : Int) ≤ r →
      r ≤ Q.voting (t : Int) → p ∉ S.adv r) :
    p ∈ Active Q S (t : Int) := by
  refine mem_awakeThroughout.mpr fun r h1 h2 => ?_
  refine hga r (by omega) ?_
  rw [Finset.mem_sdiff]
  exact ⟨Finset.mem_univ _, hhon r h1 h2⟩

/-- **The honest validators are more than two thirds** — the counting `f < n/3` gives, used
    for both of Lemma 18's quorums. -/
theorem honest_quorum (hcb : S.CorruptionBounded Q.f) (hfn : 3 * Q.f < Fintype.card Node)
    (r : Int) : 2 * Fintype.card Node ≤ 3 * (Finset.univ \ S.adv r).card := by
  have h3 : (Finset.univ \ S.adv r).card + (S.adv r).card
      ≥ (Finset.univ : Finset Node).card := by
    have h := Finset.card_le_card_sdiff_add_card (s := (Finset.univ : Finset Node))
      (t := S.adv r)
    omega
  have h2 := hcb r
  have h4 : (Finset.univ : Finset Node).card = Fintype.card Node := Finset.card_univ
  omega

/-- Algorithm 5's vote-phase send, on the **re-justification** branch: with the joining
    check open, and the processed frozen checkpoint not the previous slot's, the tick sends a
    vote whose fin-vote runs from that checkpoint to `(its chain, this slot)`. -/
theorem handler_vote_sends5_rejustify {pick : Chain Tx} {p : Node} {r : Time}
    {V : View Node M} {s : NodeState Node (Chain Tx) (QCert Node Tx)}
    (hmod : r % Q.slotLength = Q.delta) (hgate : s.activeAt ≤ r)
    (hne : (processProposals (components (Fintype.card Node) kappa pool proposer) V
      (r / Q.slotLength) s).gjFrozen.c ≠ r / Q.slotLength - 1) :
    (Msg.vote pick
        (processProposals (components (Fintype.card Node) kappa pool proposer) V
          (r / Q.slotLength) s).gjFrozen
        ⟨(processProposals (components (Fintype.card Node) kappa pool proposer) V
          (r / Q.slotLength) s).gjFrozen.ch, r / Q.slotLength⟩
        (r / Q.slotLength))
      ∈ (handlerCore (components (Fintype.card Node) kappa pool proposer) Q pick p r V
        s).send := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  simp only [handlerCore, apply_ite NodeStepResult.send]
  rw [if_neg (by omega), if_pos hmod, if_pos hgate, if_neg hne]
  exact Multiset.mem_singleton_self _

set_option maxHeartbeats 2000000 in
/-- **Every active validator's slot-`t` fin-vote reads `GJ_p → (GJ_p.ch, t)`** when slot `t`
    has an honest proposer whose carried checkpoint is older than the previous slot — Lemma
    18's first step. Lemma 17 pins the source; the re-justification branch of the target
    fires exactly because that source is not the previous slot's checkpoint. -/
theorem finvote_of_active5 {x5 : Exec Pr5 S} (H5 : SettingGA Q S x5)
    {t : Nat} (ht : 1 ≤ t)
    {vp : Node} {chp chC : Chain Tx} {qc : Option (QCert Node Tx)}
    {gjp : Checkpoint (Chain Tx)} {ip : Nat}
    (hsent : (⟨vp, Msg.propose chp chC qc gjp t⟩ : SignedMsg Node M) ∈ x5[ip].sent)
    (hhon_i : vp ∉ S.adv ((x5[ip].time : Int)))
    (hhon_t : vp ∉ S.adv (Q.voting (t : Int)))
    (hlow : gjp.c ≠ t - 1)
    {vi : Node} (hact : vi ∈ Active Q S (t : Int)) :
    ∃ (i : Nat) (ch : Chain Tx), x5[i].time = Q.slotLength * t + Q.delta ∧
      (⟨vi, Msg.vote ch gjp ⟨gjp.ch, t⟩ t⟩ : SignedMsg Node M) ∈ x5[i].sent := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  obtain ⟨⟨hmc, -, hsync, hmono, -, hdiv, hdil⟩, hstepw, hwpt, hone, ⟨hsyn, hrel⟩, hslp,
    ⟨hcb, hfn⟩, hgst⟩ := id H5
  have hvot : Q.voting (t : Int) = ((Q.slotLength * t + Q.delta : Nat) : Int) := by
    unfold Params.voting
    push_cast
    omega
  -- the validator ticks at its vote reading, with the joining check open
  obtain ⟨i₁, hi₁⟩ := hdiv (Q.slotLength * t + Q.delta)
  obtain ⟨i₀, hi₀, hti₀⟩ := exists_time_eq hstepw hi₁
  have hAw₀ : x5.Awake i₀ vi := by
    show vi ∈ S.awake ((x5[i₀].time : Int))
    rw [hti₀]
    refine mem_awakeThroughout.mp hact _ ?_ ?_ <;> rw [hvot] <;> omega
  obtain ⟨j, htj, hlblj⟩ := hdil (Q.slotLength * t + Q.delta) vi ⟨i₀, hti₀, hAw₀⟩
  have hgate : x5[j][vi].st.activeAt ≤ Q.slotLength * t + Q.delta := by
    refine MfcEquiv.activeAt_le_voting5 hsync hmono (t1 := t) ?_ (le_of_eq htj)
    intro ρ h1 h2
    refine mem_awakeThroughout.mp hact ρ ?_ ?_ <;> rw [hvot] <;> omega
  -- Lemma 17 pins the frozen checkpoint, and the target's branch follows
  have hgj := lemma17_gjFrozen H5 ht hsent hhon_i hhon_t hact hlblj
  -- the same facts, in the spelling `tick_send_mem5` expects
  have hgj' : (processProposals (components (Fintype.card Node) kappa pool proposer)
      (setClock vi (Q.slotLength * t + Q.delta) (x5.cfg j))[vi].view t
      (setClock vi (Q.slotLength * t + Q.delta) (x5.cfg j))[vi].st).gjFrozen = gjp := by
    simp only [setClock_getElem, if_pos rfl, if_true]
    exact hgj
  have hgate' : (setClock vi (Q.slotLength * t + Q.delta) (x5.cfg j))[vi].st.activeAt
      ≤ Q.slotLength * t + Q.delta := by
    simp only [setClock_getElem, if_pos rfl, if_true]
    exact hgate
  have hsend := handler_vote_sends5_rejustify (kappa := kappa) (pool := pool)
      (proposer := proposer) (pick := pick5 x5 j vi (Q.slotLength * t + Q.delta))
      (p := vi) (V := (setClock vi (Q.slotLength * t + Q.delta) (x5.cfg j))[vi].view)
      (s := (setClock vi (Q.slotLength * t + Q.delta) (x5.cfg j))[vi].st)
    (voting_reading_mod Q t) hgate' ?_
  · rw [voting_reading_div Q t, hgj'] at hsend
    refine ⟨j + 1, pick5 x5 j vi (Q.slotLength * t + Q.delta), ?_, ?_⟩
    · rw [MfcEquiv.tick_time5 hlblj]
      exact htj
    · exact MfcEquiv.tick_send_mem5 hlblj hsend
  · rw [voting_reading_div Q t, hgj']
    exact hlow

set_option maxHeartbeats 2000000 in
/-- **Re-justification, one round**: with an honest proposer whose carried checkpoint is older
    than the previous slot, and every validator awake, the checkpoint `(GJ_p.ch, t)` is
    justified in every awake validator's view from `voting(t) + Δ` on.

    Every honest validator is active (`active_of_globalAwake`), so each sends the fin-vote
    `GJ_p → (GJ_p.ch, t)` (`finvote_of_active5`); synchrony delivers them; they are more than
    two thirds (`honest_quorum`); and `justified_of_quorum_votes` closes it, `GJ_p` itself
    being justified there. -/
theorem rejustified_target5 {x5 : Exec Pr5 S} (H5 : SettingGA Q S x5)
    (hga : S.GlobalAwakeTime Q.gat Finset.univ)
    {t : Nat} (ht : 1 ≤ t)
    {vp : Node} {chp chC : Chain Tx} {qc : Option (QCert Node Tx)}
    {gjp : Checkpoint (Chain Tx)} {ip : Nat}
    (hsent : (⟨vp, Msg.propose chp chC qc gjp t⟩ : SignedMsg Node M) ∈ x5[ip].sent)
    (hhon_i : vp ∉ S.adv ((x5[ip].time : Int)))
    (hhon_t : vp ∉ S.adv (Q.voting (t : Int)))
    (hlow : gjp.c < t - 1)
    (hgat : (Q.gat : Int) ≤ Q.voting (t : Int) - 3 * (Q.delta : Int))
    {i : Nat} {w : Node} (hAw : x5.Awake i w)
    (htime : Q.slotLength * t + 2 * Q.delta ≤ x5[i].time) :
    JustifiedIn (Fintype.card Node) x5[i][w].view ⟨gjp.ch, t⟩ := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  obtain ⟨⟨hmc, -, hsync, hmono, -, hdiv, hdil⟩, hstepw, hwpt, hone, ⟨hsyn, hrel⟩, hslp,
    ⟨hcb, hfn⟩, hgst⟩ := id H5
  have hg0 : Q.gst = 0 := hgst
  have hvot : Q.voting (t : Int) = ((Q.slotLength * t + Q.delta : Nat) : Int) := by
    unfold Params.voting
    push_cast
    omega
  -- `GJ_p` is justified in the target view
  obtain ⟨hprop, kp, hkpi, hlblp, htkp, hawkp, hemp, hgjp, -, -, -⟩ :=
    propose_fields5 hsync hmc hmono hsent hhon_i
  have hJp : JustifiedIn (Fintype.card Node) x5[i][w].view gjp := by
    rw [hgjp]
    refine justifiedIn_mono ?_ (gj_justified _ _)
    intro sm hsm
    refine hsyn kp i w _ (views_sound x5 kp vp _ hsm) ?_ hAw
    rw [htkp]
    omega
  -- the honest validators, each with its fin-vote in the target view
  have hslotlt : gjp.c < (⟨gjp.ch, t⟩ : Checkpoint (Chain Tx)).c := by
    show gjp.c < t
    omega
  have hchainle : chainLe gjp.ch (⟨gjp.ch, t⟩ : Checkpoint (Chain Tx)).ch := by
    show chainLe gjp.ch gjp.ch
    exact chainLe_refl _
  refine justified_of_quorum_votes hJp hslotlt hchainle
    (W := Finset.univ \ S.adv (Q.voting (t : Int))) (honest_quorum hcb hfn _) ?_
  intro w' hw'
  have hhonw' : ∀ r : Int, r ≤ Q.voting (t : Int) → w' ∉ S.adv r := by
    intro r hr hadv
    exact absurd (hmc r (Q.voting (t : Int)) hr hadv) (Finset.mem_sdiff.mp hw').2
  have hact : w' ∈ Active Q S (t : Int) :=
    active_of_globalAwake hga hgat (fun r _ h2 => hhonw' r h2)
  obtain ⟨iv, ch, htiv, hvsent⟩ :=
    finvote_of_active5 H5 ht hsent hhon_i hhon_t (by omega) hact
  refine ⟨ch, t, ?_⟩
  refine hsyn iv i w _ hvsent ?_ hAw
  rw [htiv]
  omega

/-- Every admissible pick extends the vote tick's fork choice: a hit passes the filter's
    prefix conjunct, and the fallback *is* the fork choice. Algorithm 5's
    `chainLe_of_votePicks2`, over `components_voteHits`. -/
theorem chainLe_of_votePicks5 {V : View Node M} {r : Time}
    {s : NodeState Node (Chain Tx) (QCert Node Tx)} {pick : Chain Tx}
    (h : pick ∈ (components (Fintype.card Node) kappa pool proposer).votePicks Q V r s) :
    chainLe ((components (Fintype.card Node) kappa pool proposer).mfc
      (processProposals (components (Fintype.card Node) kappa pool proposer) V
        (r / Q.slotLength) s).vFrozen V
      (processProposals (components (Fintype.card Node) kappa pool proposer) V
        (r / Q.slotLength) s).chFrozen (r / Q.slotLength)) pick := by
  simp only [Components.votePicks] at h
  rcases mem_pickSet.mp h with ⟨-, rfl⟩ | hhit
  · exact chainLe_refl _
  · rw [MfcEquiv.components_voteHits] at hhit
    obtain ⟨-, -, -, -, -, -, hle⟩ := mem_voteHits2.mp hhit
    exact hle

set_option maxHeartbeats 1000000 in
/-- **An honest vote's chain extends the fork choice its own tick read.** The chain sent is
    the tick's pick (`handler_vote_fin_content`), and every pick extends that tick's
    processed fork choice. -/
theorem vote_chain_ge_mfc5 {x5 : Exec Pr5 S} (hsync : SynchronizedClocks x5)
    (hmc : S.MonotoneCorruption) (hmono : TimeMonotone x5) {i : Nat}
    {sm : SignedMsg Node M} {e : Chain Tx} {src tgt : Checkpoint (Chain Tx)} {s : Nat}
    (hmem : sm ∈ x5[i].sent) (hhon : sm.sender ∉ S.adv ((x5[i].time : Int)))
    (hmsg : sm.msg = .vote e src tgt s) :
    ∃ k, k < i ∧ x5.lbl k = .tick sm.sender (Q.slotLength * s + Q.delta) ∧
      x5[k].time = Q.slotLength * s + Q.delta ∧
      x5[k][sm.sender].st.activeAt ≤ Q.slotLength * s + Q.delta ∧
      chainLe ((components (Fintype.card Node) kappa pool proposer).mfc
        (processProposals (components (Fintype.card Node) kappa pool proposer)
          x5[k][sm.sender].view s x5[k][sm.sender].st).vFrozen
        x5[k][sm.sender].view
        (processProposals (components (Fintype.card Node) kappa pool proposer)
          x5[k][sm.sender].view s x5[k][sm.sender].st).chFrozen s) e := by
  obtain ⟨k, hki, hlbl, htime, hopen, -, pick, hpick, hsend⟩ :=
    vote_provenance hsync hmc hmono hmem hhon hmsg
  have hcontent := MfcEquiv.handler_vote_fin_content (voting_reading_mod Q s) hsend
  rw [voting_reading_div Q s] at hcontent
  have heq := hmsg.symm.trans hcontent
  rw [Msg.vote.injEq] at heq
  obtain ⟨hch, -, -, -⟩ := heq
  refine ⟨k, hki, hlbl, htime, hopen, ?_⟩
  rw [hch]
  have hb := chainLe_of_votePicks5 (Q := Q) hpick
  rw [voting_reading_div Q s] at hb
  exact hb

set_option maxHeartbeats 1000000 in
/-- **`chAva` does not move between a slot's vote reading and its fast-confirm reading.** Its
    only writes are at those two readings (`chAva_step5`), and no reading of either kind
    falls strictly in between: the arithmetic excludes other slots, and this validator's own
    two ticks are the endpoints, one per reading. -/
theorem chAva_quiet_between {x5 : Exec Pr5 S} (hsync : SynchronizedClocks x5)
    (hmono : TimeMonotone x5) (hone : OneTickPerReading x5) {t : Nat} {p : Node} {k jf : Nat}
    (hlblv : x5.lbl k = .tick p (Q.slotLength * t + Q.delta))
    (hlblf : x5.lbl jf = .tick p (Q.slotLength * t + 2 * Q.delta)) :
    ∀ m, k + 1 ≤ m → m ≤ jf → x5[m][p].st.chAva = x5[k + 1][p].st.chAva := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  have htv : x5[k].time = Q.slotLength * t + Q.delta := MfcEquiv.tick_reading5 hsync hlblv
  have htf : x5[jf].time = Q.slotLength * t + 2 * Q.delta :=
    MfcEquiv.tick_reading5 hsync hlblf
  have htv1 : x5[k + 1].time = Q.slotLength * t + Q.delta := by
    rw [MfcEquiv.tick_time5 hlblv]; exact htv
  intro m hkm
  induction m, hkm using Nat.le_induction with
  | base => exact fun _ => rfl
  | succ m hm ih =>
      intro hmjf
      -- the step from `m` to `m+1` is inside the window, so it is not a `chAva` write
      have htm : x5[m].time ≤ Q.slotLength * t + 2 * Q.delta := by
        have := time_le_of_le hmono (Nat.le_of_lt (by omega : m < jf))
        omega
      have htmge : Q.slotLength * t + Q.delta ≤ x5[m].time := by
        have := time_le_of_le hmono hm
        omega
      have hstep : x5[m + 1][p].st.chAva = x5[m][p].st.chAva := by
        rcases MfcEquiv.chAva_step5 (x5 := x5) (m := m) (p := p) with
          h | ⟨ti, hlbl, -, -⟩ | ⟨ti, hlbl, -, -⟩
        · exact h
        · -- a vote reading strictly after this slot's is the next slot's, too late
          exfalso
          have hti : x5[m].time = Q.slotLength * ti + Q.delta :=
            MfcEquiv.tick_reading5 hsync hlbl
          have hteq : ti = t := by
            rcases Nat.lt_trichotomy ti t with h1 | h1 | h1
            · exfalso
              have : Q.slotLength * (ti + 1) ≤ Q.slotLength * t :=
                Nat.mul_le_mul_left _ (by omega)
              have hexp : Q.slotLength * (ti + 1) = Q.slotLength * ti + Q.slotLength :=
                Nat.mul_succ ..
              omega
            · exact h1
            · exfalso
              have : Q.slotLength * (t + 1) ≤ Q.slotLength * ti :=
                Nat.mul_le_mul_left _ (by omega)
              have hexp : Q.slotLength * (t + 1) = Q.slotLength * t + Q.slotLength :=
                Nat.mul_succ ..
              omega
          subst hteq
          -- so it is *this* validator's slot-`t` vote tick, which is `k < m`
          have hmk : m = k := hone m k p _ hlbl hlblv
          omega
        · -- a fast-confirm reading in the window is this slot's, hence the endpoint `jf`
          exfalso
          have hti : x5[m].time = Q.slotLength * ti + 2 * Q.delta :=
            MfcEquiv.tick_reading5 hsync hlbl
          have hteq : ti = t := by
            rcases Nat.lt_trichotomy ti t with h1 | h1 | h1
            · exfalso
              have : Q.slotLength * (ti + 1) ≤ Q.slotLength * t :=
                Nat.mul_le_mul_left _ (by omega)
              have hexp : Q.slotLength * (ti + 1) = Q.slotLength * ti + Q.slotLength :=
                Nat.mul_succ ..
              omega
            · exact h1
            · exfalso
              have : Q.slotLength * (t + 1) ≤ Q.slotLength * ti :=
                Nat.mul_le_mul_left _ (by omega)
              have hexp : Q.slotLength * (t + 1) = Q.slotLength * t + Q.slotLength :=
                Nat.mul_succ ..
              omega
          subst hteq
          have hmk : m = jf := hone m jf p _ hlbl hlblf
          omega
      rw [hstep]
      exact ih (by omega)

set_option maxHeartbeats 2000000 in
/-- **Lemma 18's second round, the pinning step: an honest slot-`t` vote is one message.**
    In a slot with an honest proposer whose carried checkpoint is older than the previous
    slot, and with every validator awake, an honest validator's slot-`t` vote is exactly
    `[vote, chp, GJ_p → (GJ_p.ch, t), t]`: its chain by `activeVotesEq5_of_propose`, its
    source and target by `finvote_of_active5`, and the two are the same message because a
    validator votes once per slot (`honest_vote_unique`). -/
theorem honest_slot_vote_pinned5 {x5 : Exec Pr5 S} (H5 : SettingGA Q S x5) (hκ : 1 ≤ kappa)
    (hwin5 : MfcEquiv.HonestProposalWindow5 (kappa := kappa) x5)
    (hga : S.GlobalAwakeTime Q.gat Finset.univ)
    {t : Nat} (ht : 1 ≤ t)
    {vp : Node} {chp chC : Chain Tx} {qc : Option (QCert Node Tx)}
    {gjp : Checkpoint (Chain Tx)} {ip : Nat}
    (hsent : (⟨vp, Msg.propose chp chC qc gjp t⟩ : SignedMsg Node M) ∈ x5[ip].sent)
    (hhon_i : vp ∉ S.adv ((x5[ip].time : Int)))
    (hhon_t : vp ∉ S.adv (Q.voting (t : Int)))
    (hlow : gjp.c ≠ t - 1)
    (hgat : (Q.gat : Int) ≤ Q.voting (t : Int) - 3 * (Q.delta : Int))
    {i : Nat} {w : Node} (htime : Q.slotLength * t + Q.delta ≤ x5[i].time) :
    ∀ sm ∈ votes x5[i][w].view, msgSlot sm.msg = t →
      sm.sender ∉ S.adv ((x5[i].time : Int)) →
      sm.msg = Msg.vote chp gjp ⟨gjp.ch, t⟩ t := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  obtain ⟨⟨hmc, -, hsync, hmono, -, -, -⟩, -, -, hone, -, -, -, -⟩ := id H5
  obtain ⟨H2, heq⟩ := MfcEquiv.lemma10 rfl H5 hκ hwin5
  have hvot : Q.voting (t : Int) = ((Q.slotLength * t + Q.delta : Nat) : Int) := by
    unfold Params.voting
    push_cast
    omega
  have hvotcast : ((Q.slotLength * t + Q.delta : Nat) : Int) ≤ ((x5[i].time : Int)) := by
    exact_mod_cast htime
  have hvotes : MfcEquiv.ActiveVotesEq5 x5 t chp :=
    MfcEquiv.activeVotesEq5_of_propose rfl heq H5 H2 ht hsent hhon_i hhon_t
  have hact_of_hon : ∀ q : Node, q ∉ S.adv ((x5[i].time : Int)) →
      q ∈ Active Q S (t : Int) := by
    intro q hq
    refine active_of_globalAwake hga hgat (fun r _ h2 hadv => hq (hmc r _ ?_ hadv))
    rw [hvot] at h2
    omega
  intro sm hsm hslot hhonsm
  obtain ⟨e, src, tgt, s, hmsg⟩ := exists_vote_of_mem_votes hsm
  have hst : s = t := by
    rw [hmsg] at hslot
    exact hslot
  subst hst
  have hsmlog : sm ∈ x5[i].sent := by
    have h := hsm
    simp only [votes, Finset.mem_filter] at h
    exact views_sound x5 i w _ h.1
  have hact := hact_of_hon _ hhonsm
  -- the chain: the active's slot-`t` vote is `chp`
  obtain ⟨iv, src', tgt', htiv, hvsent⟩ := hvotes sm.sender hact
  have hhoniv : (⟨sm.sender, Msg.vote chp src' tgt' s⟩ :
      SignedMsg Node M).sender ∉ S.adv ((x5[iv].time : Int)) := by
    show sm.sender ∉ S.adv ((x5[iv].time : Int))
    intro hadv
    refine hhonsm (hmc _ _ ?_ hadv)
    rw [htiv]
    exact hvotcast
  have h1 := honest_vote_unique hsync hone hmc hmono hsmlog hvsent hhonsm hhoniv rfl hmsg rfl
  -- the source and target: the active's fin-vote re-justifies `(GJ_p.ch, t)`
  obtain ⟨iv2, ch2, htiv2, hvsent2⟩ :=
    finvote_of_active5 H5 ht hsent hhon_i hhon_t hlow hact
  have hhoniv2 : (⟨sm.sender, Msg.vote ch2 gjp ⟨gjp.ch, s⟩ s⟩ :
      SignedMsg Node M).sender ∉ S.adv ((x5[iv2].time : Int)) := by
    show sm.sender ∉ S.adv ((x5[iv2].time : Int))
    intro hadv
    refine hhonsm (hmc _ _ ?_ hadv)
    rw [htiv2]
    exact hvotcast
  have h2 := honest_vote_unique hsync hone hmc hmono hsmlog hvsent2 hhonsm hhoniv2 rfl hmsg
    rfl
  -- one message, so both readings of it hold
  have hm1 : sm.msg = Msg.vote chp src' tgt' s := by rw [← h1]
  have hm2 : sm.msg = Msg.vote ch2 gjp ⟨gjp.ch, s⟩ s := by rw [← h2]
  rw [hm1, Msg.vote.injEq] at hm2
  obtain ⟨-, hsrc, htgt, -⟩ := hm2
  rw [hm1, hsrc, htgt]

/-- **What a slot's development actually needs of its proposal.** A checkpoint `T` at slot
    `s` whose chain prefixes the slot's proposed chain, justified in every awake view from
    `fconf(s)` on, and named as the target of every honest slot-`s` fin-vote.

    Slot `t`'s instance comes from the re-justification branch (`slotPinned_of_low`); slot
    `t+1`'s, from the justification of `(chp, t+1)` and `finvote_target_eq_chp5`. Factoring it
    out is what lets the same development run at either slot: `GJ_p.c < t - 1` is *not*
    available at `t+1`, since `(GJ_p.ch, t)` is justified by then. -/
structure SlotPinned (x5 : Exec Pr5 S) (s : Nat) (chp : Chain Tx)
    (T : Checkpoint (Chain Tx)) : Prop where
  /-- `T` is the slot's own checkpoint. -/
  slot : T.c = s
  /-- Its chain prefixes the slot's proposal. -/
  chain : chainLe T.ch chp
  /-- It is justified in every awake view from the slot's fast-confirm reading on. -/
  justified : ∀ (i : Nat) (w : Node), x5.Awake i w →
    Q.slotLength * s + 2 * Q.delta ≤ x5[i].time →
    JustifiedIn (Fintype.card Node) x5[i][w].view T
  /-- Every honest slot-`s` fin-vote targets it. -/
  target : ∀ (i : Nat) (w : Node), Q.slotLength * s + Q.delta ≤ x5[i].time →
    ∀ sm ∈ votes x5[i][w].view, msgSlot sm.msg = s →
      sm.sender ∉ S.adv ((x5[i].time : Int)) →
      ∀ (e : Chain Tx) (src tgt : Checkpoint (Chain Tx)) (r : Nat),
        sm.msg = .vote e src tgt r → tgt = T

set_option maxHeartbeats 2000000 in
/-- **Every honest slot-`t` vote is for `chp`**, in any view from the vote reading on — the
    chain half of `honest_slot_vote_pinned5`, which needs nothing about the proposal's
    carried checkpoint. -/
theorem honest_slot_vote_chain5 {x5 : Exec Pr5 S} (H5 : SettingGA Q S x5) (hκ : 1 ≤ kappa)
    (hwin5 : MfcEquiv.HonestProposalWindow5 (kappa := kappa) x5)
    (hga : S.GlobalAwakeTime Q.gat Finset.univ)
    {t : Nat} (ht : 1 ≤ t)
    {vp : Node} {chp chC : Chain Tx} {qc : Option (QCert Node Tx)}
    {gjp : Checkpoint (Chain Tx)} {ip : Nat}
    (hsent : (⟨vp, Msg.propose chp chC qc gjp t⟩ : SignedMsg Node M) ∈ x5[ip].sent)
    (hhon_i : vp ∉ S.adv ((x5[ip].time : Int)))
    (hhon_t : vp ∉ S.adv (Q.voting (t : Int)))
    (hgat : (Q.gat : Int) ≤ Q.voting (t : Int) - 3 * (Q.delta : Int))
    {i : Nat} {w : Node} (htime : Q.slotLength * t + Q.delta ≤ x5[i].time) :
    ∀ sm ∈ votes x5[i][w].view, msgSlot sm.msg = t →
      sm.sender ∉ S.adv ((x5[i].time : Int)) → msgChain sm.msg = chp := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  obtain ⟨⟨hmc, -, hsync, hmono, -, -, -⟩, -, -, hone, -, -, -, -⟩ := id H5
  obtain ⟨H2, heq⟩ := MfcEquiv.lemma10 rfl H5 hκ hwin5
  have hvot : Q.voting (t : Int) = ((Q.slotLength * t + Q.delta : Nat) : Int) := by
    unfold Params.voting
    push_cast
    omega
  have hvotcast : ((Q.slotLength * t + Q.delta : Nat) : Int) ≤ ((x5[i].time : Int)) := by
    exact_mod_cast htime
  have hvotes : MfcEquiv.ActiveVotesEq5 x5 t chp :=
    MfcEquiv.activeVotesEq5_of_propose rfl heq H5 H2 ht hsent hhon_i hhon_t
  intro sm hsm hslot hhonsm
  have hact : sm.sender ∈ Active Q S (t : Int) := by
    refine active_of_globalAwake hga hgat (fun r _ h2 hadv => hhonsm (hmc r _ ?_ hadv))
    rw [hvot] at h2
    omega
  obtain ⟨e, src, tgt, s, hmsg⟩ := exists_vote_of_mem_votes hsm
  have hst : s = t := by
    rw [hmsg] at hslot
    exact hslot
  subst hst
  have hsmlog : sm ∈ x5[i].sent := by
    have h := hsm
    simp only [votes, Finset.mem_filter] at h
    exact views_sound x5 i w _ h.1
  obtain ⟨iv, src', tgt', htiv, hvsent⟩ := hvotes sm.sender hact
  have hhoniv : (⟨sm.sender, Msg.vote chp src' tgt' s⟩ :
      SignedMsg Node M).sender ∉ S.adv ((x5[iv].time : Int)) := by
    show sm.sender ∉ S.adv ((x5[iv].time : Int))
    intro hadv
    refine hhonsm (hmc _ _ ?_ hadv)
    rw [htiv]
    exact hvotcast
  have h1 := honest_vote_unique hsync hone hmc hmono hsmlog hvsent hhonsm hhoniv rfl hmsg rfl
  rw [← h1]
  rfl

set_option maxHeartbeats 2000000 in
/-- **Slot `t`'s pinning data, from the re-justification branch.** -/
theorem slotPinned_of_low {x5 : Exec Pr5 S} (H5 : SettingGA Q S x5) (hκ : 1 ≤ kappa)
    (hwin5 : MfcEquiv.HonestProposalWindow5 (kappa := kappa) x5)
    (hga : S.GlobalAwakeTime Q.gat Finset.univ)
    {t : Nat} (ht : 1 ≤ t)
    {vp : Node} {chp chC : Chain Tx} {qc : Option (QCert Node Tx)}
    {gjp : Checkpoint (Chain Tx)} {ip : Nat}
    (hsent : (⟨vp, Msg.propose chp chC qc gjp t⟩ : SignedMsg Node M) ∈ x5[ip].sent)
    (hhon_i : vp ∉ S.adv ((x5[ip].time : Int)))
    (hhon_t : vp ∉ S.adv (Q.voting (t : Int)))
    (hlow : gjp.c < t - 1)
    (hgat : (Q.gat : Int) ≤ Q.voting (t : Int) - 3 * (Q.delta : Int)) :
    SlotPinned x5 t chp ⟨gjp.ch, t⟩ := by
  obtain ⟨⟨hmc, -, hsync, hmono, -, -, -⟩, -, -, -, -, -, -, -⟩ := id H5
  refine ⟨rfl, ?_, ?_, ?_⟩
  · show chainLe gjp.ch chp
    obtain ⟨-, kp, -, -, -, -, -, hgjp, hchp, -, -⟩ :=
      propose_fields5 hsync hmc hmono hsent hhon_i
    rw [hgjp, hchp]
    exact chainLe_trans (gj_le_fastConfirm _ _)
      (chainLe_trans (base_le_mfc _ _ _ _) (chainLe_extend _ _ _))
  · intro i w hAw htime
    exact rejustified_target5 H5 hga ht hsent hhon_i hhon_t hlow hgat hAw htime
  · intro i w htime sm hsm hslot hhonsm e src tgt r hmsg
    have hp := honest_slot_vote_pinned5 H5 hκ hwin5 hga ht hsent hhon_i hhon_t
      (by omega) hgat htime sm hsm hslot hhonsm
    rw [hmsg, Msg.vote.injEq] at hp
    exact hp.2.2.1

set_option maxHeartbeats 2000000 in
/-- **The greatest justified checkpoint of the window is the re-justified target.** Between
    `fconf(t)` and `voting(t+1)`, `(GJ_p.ch, t)` is justified in every awake view (Lemma 18's
    first round) and nothing above slot `t` is (`no_justified_above_slot`), so `GJ`'s slot is
    `t`; and the slot-`t` justified checkpoint is unique, being the one the honest slot-`t`
    votes targeted (`justified_slot_unique` over `honest_slot_vote_pinned5`). -/
theorem gj_eq_target5 {x5 : Exec Pr5 S} (H5 : SettingGA Q S x5) (hκ : 1 ≤ kappa)
    (hwin5 : MfcEquiv.HonestProposalWindow5 (kappa := kappa) x5)
    (hga : S.GlobalAwakeTime Q.gat Finset.univ)
    {t : Nat} (ht : 1 ≤ t)
    {vp : Node} {chp chC : Chain Tx} {qc : Option (QCert Node Tx)}
    {gjp : Checkpoint (Chain Tx)} {ip : Nat}
    (hsent : (⟨vp, Msg.propose chp chC qc gjp t⟩ : SignedMsg Node M) ∈ x5[ip].sent)
    (hhon_i : vp ∉ S.adv ((x5[ip].time : Int)))
    (hhon_t : vp ∉ S.adv (Q.voting (t : Int)))
    (hlow : gjp.c < t - 1)
    (hgat : (Q.gat : Int) ≤ Q.voting (t : Int) - 3 * (Q.delta : Int))
    {i : Nat} {w : Node} (hAw : x5.Awake i w)
    (htime : Q.slotLength * t + 2 * Q.delta ≤ x5[i].time)
    (htime' : x5[i].time < Q.slotLength * (t + 1) + Q.delta) :
    gj (Fintype.card Node) x5[i][w].view = ⟨gjp.ch, t⟩ := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  obtain ⟨⟨hmc, -, hsync, hmono, -, -, -⟩, -, -, hone, -, -, ⟨hcb, hfn⟩, -⟩ := id H5
  have hcard : 0 < Fintype.card Node := by omega
  -- the target is justified, and nothing above slot `t` is
  have hT : JustifiedIn (Fintype.card Node) x5[i][w].view ⟨gjp.ch, t⟩ :=
    rejustified_target5 H5 hga ht hsent hhon_i hhon_t hlow hgat hAw htime
  have hge : t ≤ (gj (Fintype.card Node) x5[i][w].view).c := le_gj_c_of_justified hcard hT
  have hle := no_justified_above_slot hsync hone hmc hmono hcb hfn htime'
    (gj_justified (Fintype.card Node) x5[i][w].view)
  -- and the slot-`t` justified checkpoint is the one the honest votes targeted
  have hallT : ∀ sm ∈ votes x5[i][w].view, msgSlot sm.msg = t →
      sm.sender ∉ S.adv ((x5[i].time : Int)) →
      ∀ (e : Chain Tx) (src tgt : Checkpoint (Chain Tx)) (s : Nat),
        sm.msg = .vote e src tgt s → tgt = ⟨gjp.ch, t⟩ := by
    intro sm hsm hslot hhonsm e src tgt s hmsg
    have hp := honest_slot_vote_pinned5 H5 hκ hwin5 hga ht hsent hhon_i hhon_t
      (by omega) hgat (by omega) sm hsm hslot hhonsm
    rw [hmsg, Msg.vote.injEq] at hp
    exact hp.2.2.1
  exact justified_slot_unique hsync hone hmc hmono hcb hfn ht hallT
    (gj_justified (Fintype.card Node) x5[i][w].view) (le_antisymm hle hge)

set_option maxHeartbeats 2000000 in
/-- **Lemma 18's second round, first step: the slot fast-confirms exactly the proposal.**
    With an honest proposer at slot `t` and every validator awake, each honest validator is
    active (`active_of_globalAwake`), so its slot-`t` vote is exactly `chp`
    (`MfcEquiv.activeVotesEq5_of_propose`); synchrony puts those votes in every awake view
    from `fconf(t)` on, where they are more than two thirds (`honest_quorum`); and
    `honest_vote_unique` makes them the *only* honest slot-`t` votes there, so
    `fcs_eq_of_honest_agreement` pins the fast confirmation to `chp`. -/
theorem fcs_eq_chp5 {x5 : Exec Pr5 S} (H5 : SettingGA Q S x5) (hκ : 1 ≤ kappa)
    (hwin5 : MfcEquiv.HonestProposalWindow5 (kappa := kappa) x5)
    (hga : S.GlobalAwakeTime Q.gat Finset.univ)
    {t : Nat} (ht : 1 ≤ t)
    {vp : Node} {chp chC : Chain Tx} {qc : Option (QCert Node Tx)}
    {gjp : Checkpoint (Chain Tx)} {ip : Nat}
    (hsent : (⟨vp, Msg.propose chp chC qc gjp t⟩ : SignedMsg Node M) ∈ x5[ip].sent)
    (hhon_i : vp ∉ S.adv ((x5[ip].time : Int)))
    (hhon_t : vp ∉ S.adv (Q.voting (t : Int)))
    (hgat : (Q.gat : Int) ≤ Q.voting (t : Int) - 3 * (Q.delta : Int))
    {i : Nat} {w : Node} (hAw : x5.Awake i w)
    (htime : Q.slotLength * t + 2 * Q.delta ≤ x5[i].time) :
    (fastConfirmSimple (Fintype.card Node) x5[i][w].view t).1 = chp := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  obtain ⟨⟨hmc, -, hsync, hmono, -, -, -⟩, -, -, hone, ⟨hsyn, -⟩, -, ⟨hcb, hfn⟩, -⟩ := id H5
  obtain ⟨H2, heq⟩ := MfcEquiv.lemma10 rfl H5 hκ hwin5
  have hvot : Q.voting (t : Int) = ((Q.slotLength * t + Q.delta : Nat) : Int) := by
    unfold Params.voting
    push_cast
    omega
  have hvotcast : ((Q.slotLength * t + Q.delta : Nat) : Int) ≤ ((x5[i].time : Int)) := by
    have : Q.slotLength * t + Q.delta ≤ x5[i].time := by omega
    exact_mod_cast this
  -- every honest validator is active in slot `t`, and votes exactly `chp` there
  have hvotes : MfcEquiv.ActiveVotesEq5 x5 t chp :=
    MfcEquiv.activeVotesEq5_of_propose rfl heq H5 H2 ht hsent hhon_i hhon_t
  have hact_of_hon : ∀ q : Node, q ∉ S.adv ((x5[i].time : Int)) →
      q ∈ Active Q S (t : Int) := by
    intro q hq
    refine active_of_globalAwake hga hgat (fun r _ h2 hadv => hq (hmc r _ ?_ hadv))
    rw [hvot] at h2
    omega
  -- the honest votes are in `w`'s view, and there are more than two thirds of them
  have hin_view : ∀ q : Node, q ∉ S.adv ((x5[i].time : Int)) →
      ∃ (src tgt : Checkpoint (Chain Tx)),
        (⟨q, Msg.vote chp src tgt t⟩ : SignedMsg Node M) ∈ x5[i][w].view := by
    intro q hq
    obtain ⟨iv, src, tgt, htiv, hvsent⟩ := hvotes q (hact_of_hon q hq)
    refine ⟨src, tgt, ?_⟩
    refine hsyn iv i w _ hvsent ?_ hAw
    rw [htiv]
    omega
  have hsupp : 2 * Fintype.card Node ≤ 3 * (((votes x5[i][w].view).filter (fun sm =>
      msgSlot sm.msg = t ∧ chainLe chp (msgChain sm.msg))).image SignedMsg.sender).card := by
    refine le_trans (honest_quorum hcb hfn ((x5[i].time : Int))) ?_
    have hsub : (Finset.univ \ S.adv ((x5[i].time : Int))) ⊆
        (((votes x5[i][w].view).filter (fun sm =>
          msgSlot sm.msg = t ∧ chainLe chp (msgChain sm.msg))).image SignedMsg.sender) := by
      intro q hq
      obtain ⟨src, tgt, hmem⟩ := hin_view q (Finset.mem_sdiff.mp hq).2
      refine Finset.mem_image.mpr ⟨⟨q, Msg.vote chp src tgt t⟩, ?_, rfl⟩
      rw [Finset.mem_filter]
      refine ⟨?_, rfl, chainLe_refl chp⟩
      simp only [votes, Finset.mem_filter]
      exact ⟨hmem, trivial⟩
    have := Finset.card_le_card hsub
    omega
  -- and they are the only honest slot-`t` votes in that view
  have hall : ∀ sm ∈ votes x5[i][w].view, msgSlot sm.msg = t →
      sm.sender ∉ S.adv ((x5[i].time : Int)) → msgChain sm.msg = chp := by
    intro sm hsm hslot hhonsm
    obtain ⟨e, src, tgt, s, hmsg⟩ := exists_vote_of_mem_votes hsm
    have hst : s = t := by
      rw [hmsg] at hslot
      exact hslot
    subst hst
    have hsmlog : sm ∈ x5[i].sent := by
      have h := hsm
      simp only [votes, Finset.mem_filter] at h
      exact views_sound x5 i w _ h.1
    obtain ⟨iv, src', tgt', htiv, hvsent⟩ := hvotes sm.sender (hact_of_hon _ hhonsm)
    have hhoniv : (⟨sm.sender, Msg.vote chp src' tgt' s⟩ :
        SignedMsg Node M).sender ∉ S.adv ((x5[iv].time : Int)) := by
      show sm.sender ∉ S.adv ((x5[iv].time : Int))
      intro hadv
      refine hhonsm (hmc _ _ ?_ hadv)
      rw [htiv]
      exact hvotcast
    have huniq := honest_vote_unique hsync hone hmc hmono hsmlog hvsent hhonsm hhoniv
      rfl hmsg rfl
    rw [← huniq]
    rfl
  -- `chp` is nonempty: an honest proposal extends its base with the slot's block
  have hchpne : chp ≠ [] := by
    obtain ⟨-, -, chM, hchp⟩ :=
      Availability5.propose_chain_facts5 H5 hκ hwin5 hsent rfl ht hhon_i
    rw [hchp]
    unfold extend
    exact List.append_ne_nil_of_right_ne_nil _ (by simp)
  exact fcs_eq_of_honest_agreement hsync hone hmc hmono hcb hfn hchpne hsupp hall

set_option maxHeartbeats 2000000 in
/-- **Before the slot's vote reading, no available chain exceeds `chp`.** Some honest
    validator is active in slot `t` (`f < n/3` leaves one, and `GlobalAwakeTime` makes it
    active), its slot-`t` vote is `chp`, so the fork choice it read is below `chp`
    (`vote_chain_ge_mfc5`) — and Lemma 13 puts *every* validator's earlier available chain
    below that same fork choice. -/
theorem chAva_le_chp_before5 {x5 : Exec Pr5 S} (H5 : SettingGA Q S x5) (hκ : 1 ≤ kappa)
    (hwin5 : MfcEquiv.HonestProposalWindow5 (kappa := kappa) x5)
    (hga : S.GlobalAwakeTime Q.gat Finset.univ)
    {t : Nat} (ht : 1 ≤ t)
    {vp : Node} {chp chC : Chain Tx} {qc : Option (QCert Node Tx)}
    {gjp : Checkpoint (Chain Tx)} {ip : Nat}
    (hsent : (⟨vp, Msg.propose chp chC qc gjp t⟩ : SignedMsg Node M) ∈ x5[ip].sent)
    (hhon_i : vp ∉ S.adv ((x5[ip].time : Int)))
    (hhon_t : vp ∉ S.adv (Q.voting (t : Int)))
    (hgat : (Q.gat : Int) ≤ Q.voting (t : Int) - 3 * (Q.delta : Int))
    {a : Nat} {w : Node} (htime : x5[a].time ≤ Q.slotLength * t + Q.delta) :
    chainLe x5[a][w].st.chAva chp := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  obtain ⟨⟨hmc, hah, hsync, hmono, -, -, -⟩, -, -, -, ⟨hsyn, -⟩, -, ⟨hcb, hfn⟩, -⟩ := id H5
  obtain ⟨H2, heq⟩ := MfcEquiv.lemma10 rfl H5 hκ hwin5
  have hwin2 := MfcEquiv.window_transfer H5 hwin5
  have hcard : 0 < Fintype.card Node := by omega
  have hvot : Q.voting (t : Int) = ((Q.slotLength * t + Q.delta : Nat) : Int) := by
    unfold Params.voting
    push_cast
    omega
  -- an honest validator, hence an active one, with its slot-`t` vote
  obtain ⟨wh, -, hwh⟩ := exists_honest_sender (A := (Finset.univ : Finset Node))
    (r := Q.voting (t : Int)) hcb hfn (by rw [Finset.card_univ]; omega)
  have hactwh : wh ∈ Active Q S (t : Int) := by
    refine active_of_globalAwake hga hgat (fun r _ h2 hadv => hwh (hmc r _ h2 hadv))
  obtain ⟨iv, src, tgt, htiv, hvsent⟩ :=
    MfcEquiv.activeVotesEq5_of_propose rfl heq H5 H2 ht hsent hhon_i hhon_t wh hactwh
  have hhonv : (⟨wh, Msg.vote chp src tgt t⟩ : SignedMsg Node M).sender
      ∉ S.adv ((x5[iv].time : Int)) := by
    show wh ∉ S.adv ((x5[iv].time : Int))
    rw [htiv, ← hvot]
    exact hwh
  obtain ⟨k, -, hlblv, htv, -, hmfcle⟩ :=
    vote_chain_ge_mfc5 hsync hmc hmono hvsent hhonv rfl
  dsimp only at hlblv hmfcle
  -- Lemma 13 bounds every earlier available chain by the fork choice that tick read
  obtain ⟨s0, rfl⟩ : ∃ s0, t = s0 + 1 := ⟨t - 1, by omega⟩
  have hActs0 : wh ∈ Active Q S ((s0 : Int) + 1) := by
    have hcast : (((s0 + 1 : Nat)) : Int) = (s0 : Int) + 1 := by push_cast; omega
    rw [← hcast]
    exact hactwh
  have hold := (MfcEquiv.lemma13 rfl heq H5 H2 hκ hwin2 a w k wh s0 hActs0).2 hlblv htime
  exact chainLe_trans hold hmfcle

set_option maxHeartbeats 2000000 in
/-- **The slot's `fastconfirm` output is the proposal itself**, in any awake view between
    `fconf(t)` and `voting(t+1)`: the quorum branch returns `chp` (`fcs_eq_chp5`) and its
    condition holds because the greatest justified chain there is `GJ_p.ch ⪯ chp`
    (`gj_eq_target5`). -/
theorem fastConfirm_eq_chp5 {x5 : Exec Pr5 S} (H5 : SettingGA Q S x5) (hκ : 1 ≤ kappa)
    (hwin5 : MfcEquiv.HonestProposalWindow5 (kappa := kappa) x5)
    (hga : S.GlobalAwakeTime Q.gat Finset.univ)
    {t : Nat} (ht : 1 ≤ t)
    {vp : Node} {chp chC : Chain Tx} {qc : Option (QCert Node Tx)}
    {gjp : Checkpoint (Chain Tx)} {ip : Nat}
    (hsent : (⟨vp, Msg.propose chp chC qc gjp t⟩ : SignedMsg Node M) ∈ x5[ip].sent)
    (hhon_i : vp ∉ S.adv ((x5[ip].time : Int)))
    (hhon_t : vp ∉ S.adv (Q.voting (t : Int)))
    (hlow : gjp.c < t - 1)
    (hgat : (Q.gat : Int) ≤ Q.voting (t : Int) - 3 * (Q.delta : Int))
    {i : Nat} {w : Node} (hAw : x5.Awake i w)
    (htime : Q.slotLength * t + 2 * Q.delta ≤ x5[i].time)
    (htime' : x5[i].time < Q.slotLength * (t + 1) + Q.delta) :
    ((components (Fintype.card Node) kappa pool proposer).fastConfirm x5[i][w].view t).1
      = chp := by
  obtain ⟨⟨hmc, -, hsync, hmono, -, -, -⟩, -, -, -, -, -, -, -⟩ := id H5
  have hfcs : (fastConfirmSimple (Fintype.card Node) x5[i][w].view t).1 = chp :=
    fcs_eq_chp5 H5 hκ hwin5 hga ht hsent hhon_i hhon_t hgat hAw htime
  have hgjeq : gj (Fintype.card Node) x5[i][w].view = ⟨gjp.ch, t⟩ :=
    gj_eq_target5 H5 hκ hwin5 hga ht hsent hhon_i hhon_t hlow hgat hAw htime htime'
  have hgjle : chainLe gjp.ch chp := by
    obtain ⟨-, kp, -, -, -, -, -, hgjp, hchp, -, -⟩ :=
      propose_fields5 hsync hmc hmono hsent hhon_i
    rw [hgjp, hchp]
    exact chainLe_trans (gj_le_fastConfirm _ _)
      (chainLe_trans (base_le_mfc _ _ _ _) (chainLe_extend _ _ _))
  unfold Components.fastConfirm
  rw [MfcEquiv.components_fastConfirmSimple, MfcEquiv.components_gj,
    MfcEquiv.components_prefixLe]
  dsimp only
  rw [if_pos (by rw [hgjeq, hfcs]; exact hgjle)]
  exact hfcs

set_option maxHeartbeats 4000000 in
/-- **Lemma 18's second round, second step: every honest validator leaves slot `t` with
    `chAva = chp`.** At its slot-`t` vote tick all three `chAva` candidates sit below `chp`:
    the previous chain by Lemma 13 and the pick's own bound (`vote_chain_ge_mfc5`), the
    κ-deep prefix by `kappaPrefix_le_self`, and the frozen justified chain by Lemma 17
    together with `GJ_p.ch ⪯ chp`. Nothing moves it until the fast-confirm tick
    (`chAva_quiet_between`), where `fastconfirm` returns `chp` — `fcs_eq_chp5` for the
    quorum branch, closed by `gj_eq_target5` — and the write takes the longer of the two,
    which antisymmetry makes `chp` either way. -/
theorem chAva_eq_chp_at_fconf5 {x5 : Exec Pr5 S} (H5 : SettingGA Q S x5) (hκ : 1 ≤ kappa)
    (hwin5 : MfcEquiv.HonestProposalWindow5 (kappa := kappa) x5)
    (hga : S.GlobalAwakeTime Q.gat Finset.univ)
    {t : Nat} (ht : 1 ≤ t)
    {vp : Node} {chp chC : Chain Tx} {qc : Option (QCert Node Tx)}
    {gjp : Checkpoint (Chain Tx)} {ip : Nat}
    (hsent : (⟨vp, Msg.propose chp chC qc gjp t⟩ : SignedMsg Node M) ∈ x5[ip].sent)
    (hhon_i : vp ∉ S.adv ((x5[ip].time : Int)))
    (hhon_t : vp ∉ S.adv (Q.voting (t : Int)))
    (hlow : gjp.c < t - 1)
    (hgat : (Q.gat : Int) ≤ Q.voting (t : Int) - 3 * (Q.delta : Int))
    {vi : Node} {jf : Nat}
    (hlblf : x5.lbl jf = .tick vi (Q.slotLength * t + 2 * Q.delta)) :
    x5[jf + 1][vi].st.chAva = chp := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  obtain ⟨⟨hmc, hah, hsync, hmono, -, hdiv, hdil⟩, hstepw, hwpt, hone, ⟨hsyn, hrel⟩, hslp,
    ⟨hcb, hfn⟩, hgst⟩ := id H5
  obtain ⟨H2, heq⟩ := MfcEquiv.lemma10 rfl H5 hκ hwin5
  have hwin2 := MfcEquiv.window_transfer H5 hwin5
  have hvot : Q.voting (t : Int) = ((Q.slotLength * t + Q.delta : Nat) : Int) := by
    unfold Params.voting
    push_cast
    omega
  have htf : x5[jf].time = Q.slotLength * t + 2 * Q.delta :=
    MfcEquiv.tick_reading5 hsync hlblf
  have hAwf : x5.Awake jf vi := by
    have hstep := x5.step jf
    rw [hlblf] at hstep
    have h := hstep.1
    simp only [spec] at h
    exact h
  obtain ⟨s0, rfl⟩ : ∃ s0, t = s0 + 1 := ⟨t - 1, by omega⟩
  -- the pre-state available chain is below `chp`: up to the vote reading by
  -- `chAva_le_chp_before5`, and the only write in between is this slot's fast confirm,
  -- which writes `chp` itself
  have hpref : ∀ m : Nat, x5[m].time ≤ Q.slotLength * (s0 + 1) + 2 * Q.delta →
      ∀ u : Node, chainLe x5[m][u].st.chAva chp := by
    intro m
    induction m with
    | zero =>
        intro htm u
        exact chAva_le_chp_before5 H5 hκ hwin5 hga ht hsent hhon_i hhon_t hgat
          (by have h0 : x5[0].time = 0 := x5.init.1
              omega)
    | succ m ih =>
        intro htm u
        by_cases hearly : x5[m + 1].time ≤ Q.slotLength * (s0 + 1) + Q.delta
        · exact chAva_le_chp_before5 H5 hκ hwin5 hga ht hsent hhon_i hhon_t hgat hearly
        · have htmm : x5[m].time ≤ x5[m + 1].time := time_le_of_le hmono (Nat.le_succ m)
          rcases MfcEquiv.chAva_step5 (x5 := x5) (m := m) (p := u) with
            hkeep | ⟨ti, hlbl, -, hw⟩ | ⟨ti, hlbl, -, hw⟩
          · rw [hkeep]
            exact ih (by omega) u
          · -- a vote write past this slot's vote reading would be the next slot's
            exfalso
            have hti : x5[m].time = Q.slotLength * ti + Q.delta :=
              MfcEquiv.tick_reading5 hsync hlbl
            have htm1 : x5[m + 1].time = x5[m].time := MfcEquiv.tick_time5 hlbl
            have hgt : Q.slotLength * (s0 + 1) < Q.slotLength * ti := by omega
            have hle : Q.slotLength * (s0 + 1 + 1) ≤ Q.slotLength * ti :=
              Nat.mul_le_mul_left _ (by
                exact Nat.succ_le_of_lt (Nat.lt_of_mul_lt_mul_left hgt))
            have hexp : Q.slotLength * (s0 + 1 + 1)
                = Q.slotLength * (s0 + 1) + Q.slotLength := Nat.mul_succ ..
            omega
          · -- so the write is this slot's fast confirm, and it writes `chp`
            have hti : x5[m].time = Q.slotLength * ti + 2 * Q.delta :=
              MfcEquiv.tick_reading5 hsync hlbl
            have htm1 : x5[m + 1].time = x5[m].time := MfcEquiv.tick_time5 hlbl
            have htieq : ti = s0 + 1 := by
              rcases Nat.lt_trichotomy ti (s0 + 1) with h1 | h1 | h1
              · exfalso
                have hle : Q.slotLength * (ti + 1) ≤ Q.slotLength * (s0 + 1) :=
                  Nat.mul_le_mul_left _ (by omega)
                have hexp : Q.slotLength * (ti + 1) = Q.slotLength * ti + Q.slotLength :=
                  Nat.mul_succ ..
                omega
              · exact h1
              · exfalso
                have hle : Q.slotLength * (s0 + 1 + 1) ≤ Q.slotLength * ti :=
                  Nat.mul_le_mul_left _ (by omega)
                have hexp : Q.slotLength * (s0 + 1 + 1)
                    = Q.slotLength * (s0 + 1) + Q.slotLength := Nat.mul_succ ..
                omega
            subst htieq
            have hAwm : x5.Awake m u := by
              have hstep := x5.step m
              rw [hlbl] at hstep
              have h := hstep.1
              simp only [spec] at h
              exact h
            rw [hw, fastConfirm_eq_chp5 H5 hκ hwin5 hga ht hsent hhon_i hhon_t hlow
              hgat hAwm (le_of_eq hti.symm) (by
                have hexp : Q.slotLength * (s0 + 1 + 1)
                    = Q.slotLength * (s0 + 1) + Q.slotLength := Nat.mul_succ ..
                omega)]
            exact chainLe_refl _
  have hpre := hpref jf (le_of_eq htf) vi
  -- and there `fastconfirm` returns `chp`
  have hfc : ((components (Fintype.card Node) kappa pool proposer).fastConfirm
      x5[jf][vi].view (s0 + 1)).1 = chp :=
    fastConfirm_eq_chp5 H5 hκ hwin5 hga ht hsent hhon_i hhon_t hlow hgat hAwf
      (le_of_eq htf.symm) (by
        have hexp : Q.slotLength * (s0 + 1 + 1) = Q.slotLength * (s0 + 1) + Q.slotLength :=
          Nat.mul_succ ..
        omega)
  -- the write keeps the longer chain, and antisymmetry makes both branches `chp`
  rw [Availability5.chAva_at_fconf5 hlblf, hfc]
  by_cases hb : chainLe chp x5[jf][vi].st.chAva
  · rw [if_pos hb]
    exact chainLe_antisymm hpre hb
  · rw [if_neg hb]

/-- **A fold either keeps a field of its seed or the last write to it satisfies `P`** —
    stated abstractly so the concrete `match` is never restated: the step obligation is
    discharged inline on the goal `refine` produces. -/
theorem foldl_seed_or_prop {α β γ : Type} {f : β → α → β} {g : β → γ} {P : γ → Prop}
    (hstep : ∀ (acc : β) (a : α), g (f acc a) = g acc ∨ P (g (f acc a))) :
    ∀ (l : List α) (s₀ : β), g (l.foldl f s₀) = g s₀ ∨ P (g (l.foldl f s₀)) := by
  intro l
  induction l with
  | nil => exact fun _ => Or.inl rfl
  | cons a l ih =>
      intro s₀
      rw [List.foldl_cons]
      rcases ih (f s₀ a) with h | h
      · rw [h]
        exact hstep s₀ a
      · exact Or.inr h

set_option maxHeartbeats 1000000 in
/-- **The processed frozen checkpoint is the seed's or a justified one**: `gjFrozen` is
    written only on the checkpoint branch, whose condition carries the view's own
    justification. Algorithm 2's `processProposals2_chFrozen`, for Algorithm 5's other
    field. -/
theorem processProposals_gjFrozen_cases (C : Components Node (Chain Tx) (QCert Node Tx))
    (V : View Node M) (t : Nat) (s : NodeState Node (Chain Tx) (QCert Node Tx)) :
    (processProposals C V t s).gjFrozen = s.gjFrozen ∨
      C.justified ((processProposals C V t s).gjFrozen) V := by
  unfold processProposals
  refine foldl_seed_or_prop (g := NodeState.gjFrozen)
    (P := fun ck => C.justified ck V) ?_ _ _
  intro acc sm
  obtain ⟨asd, amsg⟩ := sm
  cases amsg with
  | vote ch src tgt t' => exact Or.inl rfl
  | propose chp chC qc gjp t' =>
      dsimp only
      split_ifs with h1 h2 h3 h4 h5 <;>
        first
          | exact Or.inl rfl
          | exact Or.inr h1.2.2.1
          | exact Or.inr h2.2.2.1
          | exact Or.inr h3.2.2.1

/-- **Only prefixes of `chp` have slot-`t` support**, in a view where every honest slot-`t`
    vote is `chp`: support by more than `f` senders holds an honest one, whose vote's chain
    *is* `chp`, and support flows down from extensions. -/
theorem le_chp_of_support5 {x5 : Exec Pr5 S} (hcb : S.CorruptionBounded Q.f)
    {i : Nat} {w : Node} {t : Nat} {chp ch : Chain Tx}
    (hall : ∀ sm ∈ votes x5[i][w].view, msgSlot sm.msg = t →
      sm.sender ∉ S.adv ((x5[i].time : Int)) → msgChain sm.msg = chp)
    (hsupp : Q.f < (((votes x5[i][w].view).filter (fun sm => msgSlot sm.msg = t ∧
      chainLe ch (msgChain sm.msg))).image SignedMsg.sender).card) :
    chainLe ch chp := by
  -- more than `f` supporters cannot all be corrupt
  by_cases hsub : (((votes x5[i][w].view).filter (fun sm => msgSlot sm.msg = t ∧
      chainLe ch (msgChain sm.msg))).image SignedMsg.sender) ⊆ S.adv ((x5[i].time : Int))
  · exfalso
    have h1 := Finset.card_le_card hsub
    have h2 := hcb ((x5[i].time : Int))
    omega
  · rw [Finset.not_subset] at hsub
    obtain ⟨q, hqmem, hqhon⟩ := hsub
    obtain ⟨sm, hsm, hsmq⟩ := Finset.mem_image.mp hqmem
    rw [Finset.mem_filter] at hsm
    have hchain : msgChain sm.msg = chp :=
      hall sm hsm.1 hsm.2.1 (by rw [hsmq]; exact hqhon)
    rw [← hchain]
    exact hsm.2.2

set_option maxHeartbeats 1000000 in
/-- **Nothing beyond `chp` passes the slot-`(t+1)` majority test.** The test counts slot-`t`
    voters — `fil1Exp` keeps the votes of the previous slot — and every honest one of those
    voted `chp`, so a chain `chp` does not extend is supported by corrupt senders only. The
    honest validators are all voters there, so support must exceed `(n − f)/2 > f`, and
    `le_chp_of_support5` closes it. -/
theorem majority_le_chp5 {x5 : Exec Pr5 S} (hcb : S.CorruptionBounded Q.f)
    (hfn : 3 * Q.f < Fintype.card Node)
    {i : Nat} {w : Node} {t : Nat} {chp ch : Chain Tx}
    (hall : ∀ sm ∈ votes x5[i][w].view, msgSlot sm.msg = t →
      sm.sender ∉ S.adv ((x5[i].time : Int)) → msgChain sm.msg = chp)
    (hvoters : (Finset.univ \ S.adv ((x5[i].time : Int)))
      ⊆ voters x5[i][w].view (t + 1))
    {V : View Node M} (hmaj : Majority V x5[i][w].view (t + 1) ch) :
    chainLe ch chp := by
  by_cases hnil : ch = []
  · rw [hnil]
    exact chainLe_nil _
  -- the majority's own senders support `ch` at slot `t` in this view
  refine le_chp_of_support5 hcb hall ?_
  have hsub : (((votesFor V ch (t + 1)) ∩ (votesFor x5[i][w].view ch (t + 1))).image
        SignedMsg.sender)
      ⊆ (((votes x5[i][w].view).filter (fun sm => msgSlot sm.msg = t ∧
        chainLe ch (msgChain sm.msg))).image SignedMsg.sender) := by
    intro q hq
    obtain ⟨sm, hsm, hsmq⟩ := Finset.mem_image.mp hq
    have hsm2 := (Finset.mem_inter.mp hsm).2
    unfold votesFor at hsm2
    rw [Finset.mem_filter] at hsm2
    obtain ⟨hsmf, hle⟩ := hsm2
    unfold filLmd at hsmf
    rw [Finset.mem_filter] at hsmf
    unfold fil1Exp at hsmf
    rw [Finset.mem_filter] at hsmf
    obtain ⟨⟨hsmE, hslot⟩, -⟩ := hsmf
    have hslot' : msgSlot sm.msg = t := by omega
    -- the equivocation filter runs over the view's votes, so membership is immediate
    have hvote : sm ∈ votes x5[i][w].view := by
      have h := hsmE
      unfold filEq at h
      rw [Finset.mem_filter] at h
      exact h.1
    refine Finset.mem_image.mpr ⟨sm, ?_, hsmq⟩
    rw [Finset.mem_filter]
    exact ⟨hvote, hslot', hle⟩
  -- and the honest validators are all voters, so that support exceeds `f`
  have hcards := Finset.card_le_card hsub
  have hhon := Finset.card_le_card hvoters
  have hq := honest_quorum hcb hfn ((x5[i].time : Int))
  unfold Majority at hmaj
  omega

set_option maxHeartbeats 4000000 in
/-- **At slot `t+1`'s vote reading, the fork choice and the frozen checkpoint are both below
    `chp`** — given only that nothing justified in that view exceeds `chp`, which is what the
    induction of `chAva_and_justified_le_chp5` supplies.

    The frozen chain starts at the merge value, `chp` itself (`frozen_at_vote_tick5` with
    `fastConfirm_eq_chp5`), and `processProposals_bounded` keeps it there: a certified
    proposal's `chC` has more than `f` slot-`t` supporters in the view, so
    `le_chp_of_support5` bounds it, and a justified proposal's checkpoint is bounded by
    hypothesis. The fork choice is then that base or a majority chain (`majority_le_chp5`),
    and the frozen checkpoint is the merge's — `(GJ_p.ch, t)` by `gj_eq_target5` — or one
    justified in the view. -/
theorem vote_tick_bounds_chp5 {x5 : Exec Pr5 S} (H5 : SettingGA Q S x5) (hκ : 1 ≤ kappa)
    (hwin5 : MfcEquiv.HonestProposalWindow5 (kappa := kappa) x5)
    (hga : S.GlobalAwakeTime Q.gat Finset.univ)
    {t : Nat} (ht : 1 ≤ t)
    {vp : Node} {chp chC : Chain Tx} {qc : Option (QCert Node Tx)}
    {gjp : Checkpoint (Chain Tx)} {ip : Nat}
    (hsent : (⟨vp, Msg.propose chp chC qc gjp t⟩ : SignedMsg Node M) ∈ x5[ip].sent)
    (hhon_i : vp ∉ S.adv ((x5[ip].time : Int)))
    (hhon_t : vp ∉ S.adv (Q.voting (t : Int)))
    (hlow : gjp.c < t - 1)
    (hgat : (Q.gat : Int) ≤ Q.voting (t : Int) - 3 * (Q.delta : Int))
    {m : Nat} {u : Node} (hact1 : u ∈ Active Q S ((t : Int) + 1))
    (hlbl : x5.lbl m = .tick u (Q.slotLength * (t + 1) + Q.delta))
    (hjust : ∀ C, JustifiedIn (Fintype.card Node) x5[m][u].view C → chainLe C.ch chp) :
    chainLe ((components (Fintype.card Node) kappa pool proposer).mfc
        (processProposals (components (Fintype.card Node) kappa pool proposer)
          x5[m][u].view (t + 1) x5[m][u].st).vFrozen x5[m][u].view
        (processProposals (components (Fintype.card Node) kappa pool proposer)
          x5[m][u].view (t + 1) x5[m][u].st).chFrozen (t + 1)) chp ∧
      chainLe (processProposals (components (Fintype.card Node) kappa pool proposer)
        x5[m][u].view (t + 1) x5[m][u].st).gjFrozen.ch chp := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  obtain ⟨⟨hmc, hah, hsync, hmono, -, -, hdil⟩, hstepw, -, hone, ⟨hsyn, -⟩, -,
    ⟨hcb, hfn⟩, -⟩ := id H5
  obtain ⟨H2, heq⟩ := MfcEquiv.lemma10 rfl H5 hκ hwin5
  have hcard : 0 < Fintype.card Node := by omega
  have hexp : Q.slotLength * (t + 1) = Q.slotLength * t + Q.slotLength := Nat.mul_succ ..
  have htm : x5[m].time = Q.slotLength * (t + 1) + Q.delta :=
    MfcEquiv.tick_reading5 hsync hlbl
  have hAwm : x5.Awake m u := by
    have hstep := x5.step m
    rw [hlbl] at hstep
    have h := hstep.1
    simp only [spec] at h
    exact h
  have hvot : Q.voting (t : Int) = ((Q.slotLength * t + Q.delta : Nat) : Int) := by
    unfold Params.voting
    push_cast
    omega
  -- every honest slot-`t` vote in this view is `chp`
  have hall : ∀ sm ∈ votes x5[m][u].view, msgSlot sm.msg = t →
      sm.sender ∉ S.adv ((x5[m].time : Int)) → msgChain sm.msg = chp := by
    intro sm hsm hslot hhon
    rw [honest_slot_vote_pinned5 H5 hκ hwin5 hga ht hsent hhon_i hhon_t (by omega) hgat
      (by omega) sm hsm hslot hhon]
    rfl
  -- and every honest validator is one of the slot-`t` voters counted there
  have hvotes : MfcEquiv.ActiveVotesEq5 x5 t chp :=
    MfcEquiv.activeVotesEq5_of_propose rfl heq H5 H2 ht hsent hhon_i hhon_t
  have hvoters : (Finset.univ \ S.adv ((x5[m].time : Int)))
      ⊆ voters x5[m][u].view (t + 1) := by
    intro q hq
    have hqhon : q ∉ S.adv ((x5[m].time : Int)) := (Finset.mem_sdiff.mp hq).2
    have hqact : q ∈ Active Q S (t : Int) := by
      refine active_of_globalAwake hga hgat (fun r _ h2 hadv => hqhon (hmc r _ ?_ hadv))
      rw [hvot] at h2
      have : ((Q.slotLength * t + Q.delta : Nat) : Int) ≤ ((x5[m].time : Int)) := by
        have : Q.slotLength * t + Q.delta ≤ x5[m].time := by omega
        exact_mod_cast this
      omega
    obtain ⟨iv, src, tgt, htiv, hvsent⟩ := hvotes q hqact
    have hview : (⟨q, Msg.vote chp src tgt t⟩ : SignedMsg Node M) ∈ x5[m][u].view := by
      refine hsyn iv m u _ hvsent ?_ hAwm
      rw [htiv]
      omega
    simp only [voters, fil1Exp, Finset.mem_image]
    refine ⟨⟨q, Msg.vote chp src tgt t⟩, Finset.mem_filter.2 ⟨?_, rfl⟩, rfl⟩
    simp only [votes, Finset.mem_filter]
    exact ⟨hview, trivial⟩
  -- the merge freeze: the chain is `chp` and the checkpoint is `(GJ_p.ch, t)`
  obtain ⟨im, himm, htim, hlblim, -, hcf, hgf⟩ :=
    MfcEquiv.frozen_at_vote_tick5 hsync hstepw hdil hone hact1 hlbl
  have hAwim : x5.Awake im u := by
    have hstep := x5.step im
    rw [hlblim] at hstep
    have h := hstep.1
    simp only [spec] at h
    exact h
  have hgjle : chainLe gjp.ch chp := by
    obtain ⟨-, kp, -, -, -, -, -, hgjp, hchp, -, -⟩ :=
      propose_fields5 hsync hmc hmono hsent hhon_i
    rw [hgjp, hchp]
    exact chainLe_trans (gj_le_fastConfirm _ _)
      (chainLe_trans (base_le_mfc _ _ _ _) (chainLe_extend _ _ _))
  have hseed : chainLe x5[m][u].st.chFrozen chp := by
    rw [hcf, fastConfirm_eq_chp5 H5 hκ hwin5 hga ht hsent hhon_i hhon_t hlow hgat hAwim
      (by omega) (by omega)]
    exact chainLe_refl _
  have hgjseed : x5[m][u].st.gjFrozen = ⟨gjp.ch, t⟩ := by
    rw [hgf]
    exact gj_eq_target5 H5 hκ hwin5 hga ht hsent hhon_i hhon_t hlow hgat hAwim
      (by omega) (by omega)
  -- the processed frozen chain stays below `chp`
  have hchF : chainLe (processProposals (components (Fintype.card Node) kappa pool proposer)
      x5[m][u].view (t + 1) x5[m][u].st).chFrozen chp := by
    refine (MfcEquiv.processProposals_bounded (n := Fintype.card Node) hseed ?_ ?_).1.1
    · -- a certified proposal's chain: more than `f` slot-`t` supporters in the view
      intro sm hsm chp' chC' qc' ck' hmsg hvalid
      unfold ValidProposal5 at hvalid
      rw [hmsg] at hvalid
      obtain ⟨-, -, -, hchCv⟩ := hvalid
      rcases hchCv with hnil | ⟨cert, -, hcert, hcertv⟩ | ⟨-, hchCeq, hJ⟩
      · rw [hnil]
        exact chainLe_nil _
      · refine le_chp_of_support5 hcb hall ?_
        have hsupp := MfcEquiv.support_of_cert (n := Fintype.card Node)
          (V := x5[m][u].view) (ch := chC') (t := t) hcert ?_
        · omega
        · intro e he
          obtain ⟨h1, h2, src, tgt, h3⟩ := hcertv e he
          exact ⟨h1, by omega, src, tgt, h3⟩
      · rw [hchCeq]
        exact hjust _ hJ
    · -- a justified proposal's checkpoint: bounded by hypothesis
      intro sm hsm chp' chC' qc' gjp' hmsg hJ
      exact hjust _ hJ
  refine ⟨?_, ?_⟩
  · -- the fork choice is that base or a majority chain
    rw [MfcEquiv.components_mfc]
    rcases mfc_base_or_majority
        (processProposals (components (Fintype.card Node) kappa pool proposer)
          x5[m][u].view (t + 1) x5[m][u].st).vFrozen x5[m][u].view
        (processProposals (components (Fintype.card Node) kappa pool proposer)
          x5[m][u].view (t + 1) x5[m][u].st).chFrozen (t + 1) with hb | hmaj
    · rw [hb]
      exact hchF
    · exact majority_le_chp5 hcb hfn hall hvoters hmaj
  · -- and the frozen checkpoint is the merge's or one justified in the view
    rcases processProposals_gjFrozen_cases (components (Fintype.card Node) kappa pool proposer)
      x5[m][u].view (t + 1) x5[m][u].st with h | h
    · rw [h, hgjseed]
      exact hgjle
    · exact hjust _ (of_decide_eq_true h)

set_option maxHeartbeats 4000000 in
/-- **Through slot `t+1`'s vote reading, neither an available chain nor a justified chain
    exceeds `chp`.** The two halves are one induction because each feeds the other one index
    apart: the available half at `m` needs the justified half at `m-1` (the slot-`(t+1)` fold
    reads justified checkpoints out of the view), and the justified half at `m` needs the
    available half at every index up to `m` (a justified chain descends to some vote tick's
    available chain — `justified_to_voteChAva`, whose tick comes with its joining check open,
    so the descent lands on a *state* and `vote_tick_chAva` applies).

    Note where the strictness matters: at time exactly `voting(t+1)` a view may already hold
    slot-`(t+1)` fin-votes, from validators whose ticks came first, so
    `no_justified_above_slot` does not apply there and the targets have to be pinned in tick
    order — which is what the induction does. -/
theorem chAva_and_justified_le_chp5 {x5 : Exec Pr5 S} (H5 : SettingGA Q S x5) (hκ : 1 ≤ kappa)
    (hwin5 : MfcEquiv.HonestProposalWindow5 (kappa := kappa) x5)
    (hga : S.GlobalAwakeTime Q.gat Finset.univ)
    {t : Nat} (ht : 1 ≤ t)
    {vp : Node} {chp chC : Chain Tx} {qc : Option (QCert Node Tx)}
    {gjp : Checkpoint (Chain Tx)} {ip : Nat}
    (hsent : (⟨vp, Msg.propose chp chC qc gjp t⟩ : SignedMsg Node M) ∈ x5[ip].sent)
    (hhon_i : vp ∉ S.adv ((x5[ip].time : Int)))
    (hhon_t : vp ∉ S.adv (Q.voting (t : Int)))
    (hlow : gjp.c < t - 1)
    (hgat : (Q.gat : Int) ≤ Q.voting (t : Int) - 3 * (Q.delta : Int)) :
    ∀ m : Nat, x5[m].time ≤ Q.slotLength * (t + 1) + Q.delta →
      (∀ u : Node, chainLe x5[m][u].st.chAva chp) ∧
      (∀ (u : Node) (C : Checkpoint (Chain Tx)),
        JustifiedIn (Fintype.card Node) x5[m][u].view C → chainLe C.ch chp) := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  obtain ⟨⟨hmc, hah, hsync, hmono, -, -, hdil⟩, hstepw, hwpt, hone, ⟨hsyn, -⟩, -,
    ⟨hcb, hfn⟩, -⟩ := id H5
  have hexp : Q.slotLength * (t + 1) = Q.slotLength * t + Q.slotLength := Nat.mul_succ ..
  have hexp2 : Q.slotLength * (t + 1 + 1) = Q.slotLength * (t + 1) + Q.slotLength :=
    Nat.mul_succ ..
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
  intro htm
  -- the available half first: it only reaches back one index
  have hchAva : ∀ u : Node, chainLe x5[m][u].st.chAva chp := by
    intro u
    by_cases hearly : x5[m].time ≤ Q.slotLength * t + Q.delta
    · exact chAva_le_chp_before5 H5 hκ hwin5 hga ht hsent hhon_i hhon_t hgat hearly
    · -- past the vote reading, so `m` has a predecessor
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := by
        cases m with
        | zero =>
            exact absurd (by
              have h0 : x5[0].time = 0 := x5.init.1
              omega) hearly
        | succ m' => exact ⟨m', rfl⟩
      have hle' : x5[m'].time ≤ x5[m' + 1].time := time_le_of_le hmono (Nat.le_succ m')
      have htm' : x5[m'].time ≤ Q.slotLength * (t + 1) + Q.delta := le_trans hle' htm
      have hIH := IH m' (by omega) htm'
      rcases MfcEquiv.chAva_step5 (x5 := x5) (m := m') (p := u) with
        hkeep | ⟨ti, hlbl, hgate, hw⟩ | ⟨ti, hlbl, -, hw⟩
      · rw [hkeep]
        exact hIH.1 u
      · -- a vote write in the window is slot `t+1`'s
        have hti : x5[m'].time = Q.slotLength * ti + Q.delta :=
          MfcEquiv.tick_reading5 hsync hlbl
        have htm1 : x5[m' + 1].time = x5[m'].time := MfcEquiv.tick_time5 hlbl
        have htieq : ti = t + 1 := by
          rcases Nat.lt_trichotomy ti (t + 1) with h1 | h1 | h1
          · exfalso
            have hle : Q.slotLength * (ti + 1) ≤ Q.slotLength * (t + 1) :=
              Nat.mul_le_mul_left _ (by omega)
            have he : Q.slotLength * (ti + 1) = Q.slotLength * ti + Q.slotLength :=
              Nat.mul_succ ..
            omega
          · exact h1
          · exfalso
            have hle : Q.slotLength * (t + 1 + 1) ≤ Q.slotLength * ti :=
              Nat.mul_le_mul_left _ (by omega)
            omega
        subst htieq
        -- the joining check is open, so the voter is active in slot `t+1`
        have hact1 : u ∈ Active Q S ((t : Int) + 1) := by
          have h := active_of_open_join5 hsync hstepw hdil hwpt (by omega) hlbl hti hgate
          have hcast : (((t + 1 : Nat)) : Int) = (t : Int) + 1 := by push_cast; omega
          rw [← hcast]
          exact h
        obtain ⟨hmfc, hgjf⟩ := vote_tick_bounds_chp5 H5 hκ hwin5 hga ht hsent hhon_i hhon_t
          hlow hgat hact1 hlbl (hIH.2 u)
        rw [hw]
        rcases MfcEquiv.voteChAva_cases x5 m' u (Q.slotLength * (t + 1) + Q.delta) with
          h | h | h <;> rw [h, voting_reading_div Q (t + 1)]
        · rw [show (processProposals (components (Fintype.card Node) kappa pool proposer)
              x5[m'][u].view (t + 1) x5[m'][u].st).chAva = x5[m'][u].st.chAva from
            MfcEquiv.processProposals_chAva _ _ _ _]
          exact hIH.1 u
        · exact chainLe_trans (kappaPrefix_le_self _ _ _) hmfc
        · exact hgjf
      · -- a fast-confirm write in the window is slot `t`'s, and it writes `chp`
        have hti : x5[m'].time = Q.slotLength * ti + 2 * Q.delta :=
          MfcEquiv.tick_reading5 hsync hlbl
        have htm1 : x5[m' + 1].time = x5[m'].time := MfcEquiv.tick_time5 hlbl
        have htieq : ti = t := by
          rcases Nat.lt_trichotomy ti t with h1 | h1 | h1
          · exfalso
            have hle : Q.slotLength * (ti + 1) ≤ Q.slotLength * t :=
              Nat.mul_le_mul_left _ (by omega)
            have he : Q.slotLength * (ti + 1) = Q.slotLength * ti + Q.slotLength :=
              Nat.mul_succ ..
            omega
          · exact h1
          · exfalso
            have hle : Q.slotLength * (t + 1) ≤ Q.slotLength * ti :=
              Nat.mul_le_mul_left _ (by omega)
            omega
        subst htieq
        have hAwm' : x5.Awake m' u := by
          have hstep := x5.step m'
          rw [hlbl] at hstep
          have h := hstep.1
          simp only [spec] at h
          exact h
        rw [hw, fastConfirm_eq_chp5 H5 hκ hwin5 hga ht hsent hhon_i hhon_t hlow hgat hAwm'
          (by omega) (by omega)]
        exact chainLe_refl _
  refine ⟨hchAva, ?_⟩
  -- the justified half: a justified chain descends to some vote tick's available chain
  intro u C hC
  rcases MfcEquiv.justified_to_voteChAva hsync hmc hmono hcb hfn (le_refl _) (i := m)
      C.c C rfl m u (le_refl m) hC with hnil | ⟨k, v, τ, hk, hlblk, hmodk, hgatek, hle⟩
  · rw [hnil]
    exact chainLe_nil _
  · rw [← MfcEquiv.vote_tick_chAva hlblk hmodk hgatek] at hle
    have htk1 : x5[k + 1].time ≤ Q.slotLength * (t + 1) + Q.delta := by
      have h1 := time_le_of_le hmono (Nat.le_of_lt hk)
      have h2 : x5[k + 1].time = x5[k].time := MfcEquiv.tick_time5 hlblk
      omega
    rcases Nat.lt_or_ge (k + 1) m with hlt | hge
    · exact chainLe_trans hle ((IH (k + 1) hlt htk1).1 v)
    · have hkm : k + 1 = m := by omega
      rw [hkm] at hle
      exact chainLe_trans hle (hchAva v)

/-- Algorithm 5's vote-phase send on the **extension** branch: with the joining check open
    and the processed frozen checkpoint at the previous slot, the target is this tick's own
    available chain at this slot. The companion of `handler_vote_sends5_rejustify`. -/
theorem handler_vote_sends5_extend {pick : Chain Tx} {p : Node} {r : Time}
    {V : View Node M} {s : NodeState Node (Chain Tx) (QCert Node Tx)}
    (hmod : r % Q.slotLength = Q.delta) (hgate : s.activeAt ≤ r)
    (heq : (processProposals (components (Fintype.card Node) kappa pool proposer) V
      (r / Q.slotLength) s).gjFrozen.c = r / Q.slotLength - 1) :
    (Msg.vote pick
        (processProposals (components (Fintype.card Node) kappa pool proposer) V
          (r / Q.slotLength) s).gjFrozen
        ⟨(handlerCore (components (Fintype.card Node) kappa pool proposer) Q pick p r V
          s).state.chAva, r / Q.slotLength⟩
        (r / Q.slotLength))
      ∈ (handlerCore (components (Fintype.card Node) kappa pool proposer) Q pick p r V
        s).send := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  simp only [handlerCore, apply_ite NodeStepResult.send, apply_ite NodeStepResult.state,
    if_neg (show ¬ (r % Q.slotLength = 0) from by omega), if_pos hmod, if_pos hgate,
    if_pos heq]
  exact Multiset.mem_singleton_self _

set_option maxHeartbeats 4000000 in
/-- **Every honest slot-`(t+1)` fin-vote targets `(chp, t+1)`** — Lemma 18's second round,
    assembled. Induction on the index, because the two branches of the target resolve
    differently and one of them appeals to another validator's vote:

    * the frozen checkpoint's slot is `t` — then it is `(GJ_p.ch, t)` itself
      (`justified_slot_unique`), the **extension** branch fires, and the target is the tick's
      own available chain, which is `chp`: `⪰` by monotonicity from slot `t`'s fast confirm,
      `⪯` by `chAva_and_justified_le_chp5`;
    * or it is `t+1` — the only other value, since the fold cannot go below the merge's `t`
      and `no_justified_above_slot` caps it at `t+1` — then the **re-justification** branch
      fires with target `(G.ch, t+1)`, and `G.ch = chp` because `G`'s own quorum holds an
      honest validator whose fin-vote named `G`, and that vote is earlier: the induction
      hypothesis gives `G = (chp, t+1)`.

    A view at exactly `voting(t+1)` may already hold slot-`(t+1)` fin-votes, from validators
    whose ticks came first, which is why the second case exists at all and why the argument
    has to run in tick order. -/
theorem finvote_target_eq_chp5 {x5 : Exec Pr5 S} (H5 : SettingGA Q S x5) (hκ : 1 ≤ kappa)
    (hwin5 : MfcEquiv.HonestProposalWindow5 (kappa := kappa) x5)
    (hga : S.GlobalAwakeTime Q.gat Finset.univ)
    {t : Nat} (ht : 1 ≤ t)
    {vp : Node} {chp chC : Chain Tx} {qc : Option (QCert Node Tx)}
    {gjp : Checkpoint (Chain Tx)} {ip : Nat}
    (hsent : (⟨vp, Msg.propose chp chC qc gjp t⟩ : SignedMsg Node M) ∈ x5[ip].sent)
    (hhon_i : vp ∉ S.adv ((x5[ip].time : Int)))
    (hhon_t : vp ∉ S.adv (Q.voting (t : Int)))
    (hlow : gjp.c < t - 1)
    (hgat : (Q.gat : Int) ≤ Q.voting (t : Int) - 3 * (Q.delta : Int)) :
    ∀ m : Nat, x5[m].time ≤ Q.slotLength * (t + 1) + Q.delta →
      ∀ (sm : SignedMsg Node M) (e : Chain Tx) (src tgt : Checkpoint (Chain Tx)),
        sm ∈ x5[m].sent → sm.msg = .vote e src tgt (t + 1) →
        sm.sender ∉ S.adv ((x5[m].time : Int)) → tgt = ⟨chp, t + 1⟩ := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  obtain ⟨⟨hmc, hah, hsync, hmono, -, hdiv, hdil⟩, hstepw, hwpt, hone, ⟨hsyn, -⟩, -,
    ⟨hcb, hfn⟩, -⟩ := id H5
  have hcard : 0 < Fintype.card Node := by omega
  have hexp : Q.slotLength * (t + 1) = Q.slotLength * t + Q.slotLength := Nat.mul_succ ..
  have hexp2 : Q.slotLength * (t + 1 + 1) = Q.slotLength * (t + 1) + Q.slotLength :=
    Nat.mul_succ ..
  have hbound := chAva_and_justified_le_chp5 H5 hκ hwin5 hga ht hsent hhon_i hhon_t hlow hgat
  have hvot1 : Q.voting (((t + 1 : Nat)) : Int)
      = ((Q.slotLength * (t + 1) + Q.delta : Nat) : Int) := by
    unfold Params.voting
    push_cast
    omega
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
  intro htm sm e src tgt hmem hmsg hhon
  -- the emitting tick, its pick, and the message the handler sent
  obtain ⟨k, hkm, hlblk, htk, hgate, hem, pick, -, hsend⟩ :=
    vote_provenance hsync hmc hmono hmem hhon hmsg
  have hcontent := MfcEquiv.handler_vote_fin_content (voting_reading_mod Q (t + 1)) hsend
  rw [voting_reading_div Q (t + 1)] at hcontent
  have heq := hmsg.symm.trans hcontent
  rw [Msg.vote.injEq] at heq
  obtain ⟨-, -, htgt, -⟩ := heq
  -- the voter is active in slot `t+1`, so its frozen fields come from the merge
  have hact1 : sm.sender ∈ Active Q S (((t + 1 : Nat)) : Int) :=
    active_of_open_join5 hsync hstepw hdil hwpt (by omega) hlblk htk hgate
  have hact1' : sm.sender ∈ Active Q S ((t : Int) + 1) := by
    have hcast : (((t + 1 : Nat)) : Int) = (t : Int) + 1 := by push_cast; omega
    rw [← hcast]
    exact hact1
  obtain ⟨im, himk, htim, hlblim, -, -, hgf⟩ :=
    MfcEquiv.frozen_at_vote_tick5 hsync hstepw hdil hone hact1' hlblk
  have hAwim : x5.Awake im sm.sender := by
    have hstep := x5.step im
    rw [hlblim] at hstep
    have h := hstep.1
    simp only [spec] at h
    exact h
  have hseedgj : x5[k][sm.sender].st.gjFrozen = ⟨gjp.ch, t⟩ := by
    rw [hgf]
    exact gj_eq_target5 H5 hκ hwin5 hga ht hsent hhon_i hhon_t hlow hgat hAwim
      (by omega) (by omega)
  by_cases hbranch : (processProposals (components (Fintype.card Node) kappa pool proposer)
      x5[k][sm.sender].view (t + 1) x5[k][sm.sender].st).gjFrozen.c = t + 1 - 1
  · -- the extension branch: the target is this tick's own available chain
    rw [htgt, if_pos hbranch]
    congr 1
    -- the fold is the tick's `chAva` write
    have hfold : (MfcEquiv.voteChAva x5 k sm.sender (Q.slotLength * (t + 1) + Q.delta))
        = x5[k + 1][sm.sender].st.chAva :=
      (MfcEquiv.vote_tick_chAva hlblk (voting_reading_mod Q (t + 1)) hgate).symm
    unfold MfcEquiv.voteChAva at hfold
    rw [voting_reading_div Q (t + 1)] at hfold
    rw [hfold]
    -- and that write is `chp`: below by the induction, above by monotonicity
    refine chainLe_antisymm ?_ ?_
    · exact (hbound (k + 1) (by rw [MfcEquiv.tick_time5 hlblk, htk])).1 sm.sender
    · obtain ⟨jf, htjf, hlbljf⟩ := hdil (Q.slotLength * t + 2 * Q.delta) sm.sender
        (by
          obtain ⟨i₃, hi₃⟩ := hdiv (Q.slotLength * t + 2 * Q.delta)
          obtain ⟨i₂, hi₂, hti₂⟩ := exists_time_eq hstepw hi₃
          refine ⟨i₂, hti₂, ?_⟩
          show sm.sender ∈ S.awake ((x5[i₂].time : Int))
          rw [hti₂]
          refine mem_awakeThroughout.mp hact1 _ ?_ ?_ <;> rw [hvot1] <;> omega)
      have hfceq : x5[jf + 1][sm.sender].st.chAva = chp :=
        chAva_eq_chp_at_fconf5 H5 hκ hwin5 hga ht hsent hhon_i hhon_t hlow hgat hlbljf
      have hjfk : jf + 1 ≤ k + 1 := by
        by_contra hcon
        have hkl : k ≤ jf := by omega
        have h1 : x5[k].time ≤ x5[jf].time := time_le_of_le hmono hkl
        omega
      rw [← hfceq]
      exact Availability5.chAva_mono H5 hκ hwin5 sm.sender hjfk
  · -- the re-justification branch: the frozen checkpoint is justified at slot `t+1`
    rw [htgt, if_neg hbranch]
    congr 1
    -- it is not the merge's own, so it is justified in the view
    have hJ : JustifiedIn (Fintype.card Node) x5[k][sm.sender].view
        (processProposals (components (Fintype.card Node) kappa pool proposer)
          x5[k][sm.sender].view (t + 1) x5[k][sm.sender].st).gjFrozen := by
      rcases processProposals_gjFrozen_cases
        (components (Fintype.card Node) kappa pool proposer) x5[k][sm.sender].view (t + 1)
        x5[k][sm.sender].st with h | h
      · exact absurd (by rw [h, hseedgj]; show t = t + 1 - 1; omega) hbranch
      · exact of_decide_eq_true h
    -- its slot is `t+1`: at least `t` from the merge, at most `t+1` from the counting
    have hge : t ≤ (processProposals (components (Fintype.card Node) kappa pool proposer)
        x5[k][sm.sender].view (t + 1) x5[k][sm.sender].st).gjFrozen.c := by
      have hmono' := processProposals_gjFrozen_c_mono
        (components (Fintype.card Node) kappa pool proposer) x5[k][sm.sender].view (t + 1)
        x5[k][sm.sender].st
      rw [hseedgj] at hmono'
      exact hmono'
    have hle := no_justified_above_slot hsync hone hmc hmono hcb hfn
      (t := t + 1) (by rw [htk]; omega) hJ
    -- name it, so the justification can be taken apart
    obtain ⟨G, hGdef⟩ :
        ∃ G, (processProposals (components (Fintype.card Node) kappa pool proposer)
          x5[k][sm.sender].view (t + 1) x5[k][sm.sender].st).gjFrozen = G := ⟨_, rfl⟩
    rw [hGdef] at hbranch hJ hge hle ⊢
    have hGc : G.c = t + 1 := by omega
    -- its own quorum holds an honest validator, whose earlier fin-vote named it
    cases hJ with
    | genesis =>
        exfalso
        have h0 : (0 : Nat) = t + 1 := hGc
        omega
    | link hjust hlk =>
        obtain ⟨q, hqmem, hqhon⟩ :=
          exists_honest_sender (r := ((x5[k].time : Int))) hcb hfn hlk.2.2
        obtain ⟨smq, hsmqV, hsmqs, e', τ, hsmqmsg⟩ := mem_linkVoters hqmem
        have hsmqlog : smq ∈ x5[k].sent := views_sound x5 k sm.sender _ hsmqV
        have hhonq : smq.sender ∉ S.adv ((x5[k].time : Int)) := by
          rw [hsmqs]
          exact hqhon
        have hτ : τ = t + 1 := by
          obtain ⟨htgtc, -⟩ := vote_fields5 hsync hmc hmono hsmqlog hhonq hsmqmsg
          omega
        subst hτ
        have hIHq := IH k hkm (by rw [htk]) smq e' _ _ hsmqlog hsmqmsg hhonq
        rw [hIHq]

/-- Older messages reach every later awake view, `Δ` being the delivery bound. -/
theorem view_subset_of_time5 {x5 : Exec Pr5 S} (hsyn : Synchrony 0 Q.delta x5)
    {a b : Nat} {u w : Node} (hb : x5.Awake b w)
    (h : x5[a].time + Q.delta ≤ x5[b].time) :
    ∀ sm ∈ x5[a][u].view, sm ∈ x5[b][w].view := by
  intro sm hsm
  exact hsyn a b w sm (views_sound x5 a u sm hsm) (by omega) hb

set_option maxHeartbeats 4000000 in
/-- **Each slot-`(t+1)` active sends the fin-vote whose target is `(chp, t+1)`.** Its source
    is either the merge's `(GJ_p.ch, t)` — the extension branch — or a slot-`(t+1)` checkpoint
    already justified in its own view, which by `finvote_target_eq_chp5` is `(chp, t+1)`
    itself. Either way the target is `(chp, t+1)`. -/
theorem finvote_of_active5_next {x5 : Exec Pr5 S} (H5 : SettingGA Q S x5) (hκ : 1 ≤ kappa)
    (hwin5 : MfcEquiv.HonestProposalWindow5 (kappa := kappa) x5)
    (hga : S.GlobalAwakeTime Q.gat Finset.univ)
    {t : Nat} (ht : 1 ≤ t)
    {vp : Node} {chp chC : Chain Tx} {qc : Option (QCert Node Tx)}
    {gjp : Checkpoint (Chain Tx)} {ip : Nat}
    (hsent : (⟨vp, Msg.propose chp chC qc gjp t⟩ : SignedMsg Node M) ∈ x5[ip].sent)
    (hhon_i : vp ∉ S.adv ((x5[ip].time : Int)))
    (hhon_t : vp ∉ S.adv (Q.voting (t : Int)))
    (hlow : gjp.c < t - 1)
    (hgat : (Q.gat : Int) ≤ Q.voting (t : Int) - 3 * (Q.delta : Int))
    {vi : Node} (hact1 : vi ∈ Active Q S ((t : Int) + 1)) :
    ∃ (m : Nat) (ch : Chain Tx) (src : Checkpoint (Chain Tx)),
      x5[m].time = Q.slotLength * (t + 1) + Q.delta ∧
      x5[m + 1].time = Q.slotLength * (t + 1) + Q.delta ∧
      (⟨vi, Msg.vote ch src ⟨chp, t + 1⟩ (t + 1)⟩ : SignedMsg Node M) ∈ x5[m + 1].sent ∧
      (src = ⟨gjp.ch, t⟩ ∨
        JustifiedIn (Fintype.card Node) x5[m][vi].view ⟨chp, t + 1⟩) := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  obtain ⟨⟨hmc, hah, hsync, hmono, -, hdiv, hdil⟩, hstepw, hwpt, hone, ⟨hsyn, -⟩, -,
    ⟨hcb, hfn⟩, -⟩ := id H5
  have hexp : Q.slotLength * (t + 1) = Q.slotLength * t + Q.slotLength := Nat.mul_succ ..
  have hexp2 : Q.slotLength * (t + 1 + 1) = Q.slotLength * (t + 1) + Q.slotLength :=
    Nat.mul_succ ..
  have hvot1 : Q.voting (((t + 1 : Nat)) : Int)
      = ((Q.slotLength * (t + 1) + Q.delta : Nat) : Int) := by
    unfold Params.voting
    push_cast
    omega
  have hact1n : vi ∈ Active Q S (((t + 1 : Nat)) : Int) := by
    have hcast : (((t + 1 : Nat)) : Int) = (t : Int) + 1 := by push_cast; omega
    rw [hcast]
    exact hact1
  -- the tick at slot `t+1`'s vote reading, with the joining check open
  obtain ⟨i₁, hi₁⟩ := hdiv (Q.slotLength * (t + 1) + Q.delta)
  obtain ⟨i₀, hi₀, hti₀⟩ := exists_time_eq hstepw hi₁
  have hAw₀ : x5.Awake i₀ vi := by
    show vi ∈ S.awake ((x5[i₀].time : Int))
    rw [hti₀]
    refine mem_awakeThroughout.mp hact1n _ ?_ ?_ <;> rw [hvot1] <;> omega
  obtain ⟨m, htm, hlblm⟩ := hdil (Q.slotLength * (t + 1) + Q.delta) vi ⟨i₀, hti₀, hAw₀⟩
  have hgate : x5[m][vi].st.activeAt ≤ Q.slotLength * (t + 1) + Q.delta := by
    refine MfcEquiv.activeAt_le_voting5 hsync hmono (t1 := t + 1) ?_ (le_of_eq htm)
    intro ρ h1 h2
    refine mem_awakeThroughout.mp hact1n ρ ?_ ?_ <;> rw [hvot1] <;> omega
  have hhonvi : vi ∉ S.adv ((x5[m].time : Int)) := by
    rw [htm]
    have hawk : vi ∈ S.awake ((Q.slotLength * (t + 1) + Q.delta : Nat) : Int) := by
      refine mem_awakeThroughout.mp hact1n _ ?_ ?_ <;> rw [hvot1] <;> omega
    exact Finset.disjoint_left.mp (hah _) hawk
  -- the merge's frozen checkpoint, and the two branch facts about the processed one
  obtain ⟨im, himm, htim, hlblim, -, -, hgf⟩ :=
    MfcEquiv.frozen_at_vote_tick5 hsync hstepw hdil hone hact1 hlblm
  have hAwim : x5.Awake im vi := by
    have hstep := x5.step im
    rw [hlblim] at hstep
    have h := hstep.1
    simp only [spec] at h
    exact h
  have hseedgj : x5[m][vi].st.gjFrozen = ⟨gjp.ch, t⟩ := by
    rw [hgf]
    exact gj_eq_target5 H5 hκ hwin5 hga ht hsent hhon_i hhon_t hlow hgat hAwim
      (by omega) (by omega)
  -- the spellings `tick_send_mem5` expects
  have hgate' : (setClock vi (Q.slotLength * (t + 1) + Q.delta) (x5.cfg m))[vi].st.activeAt
      ≤ Q.slotLength * (t + 1) + Q.delta := by
    simp only [setClock_getElem, if_pos rfl, if_true]
    exact hgate
  have hview' : (setClock vi (Q.slotLength * (t + 1) + Q.delta) (x5.cfg m))[vi].view
      = x5[m][vi].view := by
    simp only [setClock_getElem, if_true]
    rfl
  have hst' : (setClock vi (Q.slotLength * (t + 1) + Q.delta) (x5.cfg m))[vi].st
      = x5[m][vi].st := by
    simp only [setClock_getElem, if_true]
    rfl
  by_cases hbranch : (processProposals (components (Fintype.card Node) kappa pool proposer)
      x5[m][vi].view (t + 1) x5[m][vi].st).gjFrozen.c = t + 1 - 1
  · -- the extension branch: the source is the merge's checkpoint
    have hsend := handler_vote_sends5_extend (kappa := kappa) (pool := pool)
        (proposer := proposer)
        (pick := pick5 x5 m vi (Q.slotLength * (t + 1) + Q.delta)) (p := vi)
        (V := (setClock vi (Q.slotLength * (t + 1) + Q.delta) (x5.cfg m))[vi].view)
        (s := (setClock vi (Q.slotLength * (t + 1) + Q.delta) (x5.cfg m))[vi].st)
      (voting_reading_mod Q (t + 1)) hgate' (by
        rw [voting_reading_div Q (t + 1), hview', hst']
        exact hbranch)
    rw [voting_reading_div Q (t + 1)] at hsend
    have hlog := MfcEquiv.tick_send_mem5 hlblm hsend
    rw [hview', hst'] at hlog
    -- the target is `(chp, t+1)`, and the source is `(GJ_p.ch, t)`
    have htgt := finvote_target_eq_chp5 H5 hκ hwin5 hga ht hsent hhon_i hhon_t hlow hgat
      (m + 1) (by rw [MfcEquiv.tick_time5 hlblm, htm]) _ _ _ _ hlog rfl
      (by rw [MfcEquiv.tick_time5 hlblm]; exact hhonvi)
    have hsrc : (processProposals (components (Fintype.card Node) kappa pool proposer)
        x5[m][vi].view (t + 1) x5[m][vi].st).gjFrozen = ⟨gjp.ch, t⟩ := by
      rcases processProposals_gjFrozen_cases
        (components (Fintype.card Node) kappa pool proposer) x5[m][vi].view (t + 1)
        x5[m][vi].st with h | h
      · rw [h, hseedgj]
      · refine justified_slot_unique hsync hone hmc hmono hcb hfn ht ?_
          (of_decide_eq_true h) (by omega)
        intro sm hsm hslot hhonsm e src tgt s hmsg
        have hp := honest_slot_vote_pinned5 H5 hκ hwin5 hga ht hsent hhon_i hhon_t
          (by omega) hgat (by rw [htm]; omega) sm hsm hslot hhonsm
        rw [hmsg, Msg.vote.injEq] at hp
        exact hp.2.2.1
    refine ⟨m, pick5 x5 m vi (Q.slotLength * (t + 1) + Q.delta),
      (processProposals (components (Fintype.card Node) kappa pool proposer)
        x5[m][vi].view (t + 1) x5[m][vi].st).gjFrozen, htm,
      by rw [MfcEquiv.tick_time5 hlblm]; exact htm, ?_, Or.inl hsrc⟩
    rw [← htgt]
    exact hlog
  · -- the re-justification branch: the source is justified at slot `t+1`, hence `(chp, t+1)`
    have hsend := handler_vote_sends5_rejustify (kappa := kappa) (pool := pool)
        (proposer := proposer)
        (pick := pick5 x5 m vi (Q.slotLength * (t + 1) + Q.delta)) (p := vi)
        (V := (setClock vi (Q.slotLength * (t + 1) + Q.delta) (x5.cfg m))[vi].view)
        (s := (setClock vi (Q.slotLength * (t + 1) + Q.delta) (x5.cfg m))[vi].st)
      (voting_reading_mod Q (t + 1)) hgate' (by
        rw [voting_reading_div Q (t + 1), hview', hst']
        exact hbranch)
    rw [voting_reading_div Q (t + 1)] at hsend
    have hlog := MfcEquiv.tick_send_mem5 hlblm hsend
    rw [hview', hst'] at hlog
    have htgt := finvote_target_eq_chp5 H5 hκ hwin5 hga ht hsent hhon_i hhon_t hlow hgat
      (m + 1) (by rw [MfcEquiv.tick_time5 hlblm, htm]) _ _ _ _ hlog rfl
      (by rw [MfcEquiv.tick_time5 hlblm]; exact hhonvi)
    -- the frozen checkpoint is justified in the view, and its slot is `t+1`
    have hJ : JustifiedIn (Fintype.card Node) x5[m][vi].view
        (processProposals (components (Fintype.card Node) kappa pool proposer)
          x5[m][vi].view (t + 1) x5[m][vi].st).gjFrozen := by
      rcases processProposals_gjFrozen_cases
        (components (Fintype.card Node) kappa pool proposer) x5[m][vi].view (t + 1)
        x5[m][vi].st with h | h
      · exact absurd (by rw [h, hseedgj]; show t = t + 1 - 1; omega) hbranch
      · exact of_decide_eq_true h
    -- the target pins its chain, and the branch pins its slot
    have hGeq : (processProposals (components (Fintype.card Node) kappa pool proposer)
        x5[m][vi].view (t + 1) x5[m][vi].st).gjFrozen = ⟨chp, t + 1⟩ := by
      have hge : t ≤ (processProposals (components (Fintype.card Node) kappa pool proposer)
          x5[m][vi].view (t + 1) x5[m][vi].st).gjFrozen.c := by
        have hmono' := processProposals_gjFrozen_c_mono
          (components (Fintype.card Node) kappa pool proposer) x5[m][vi].view (t + 1)
          x5[m][vi].st
        rw [hseedgj] at hmono'
        exact hmono'
      have hle := no_justified_above_slot hsync hone hmc hmono hcb hfn
        (t := t + 1) (by rw [htm]; omega) hJ
      have hch : (processProposals (components (Fintype.card Node) kappa pool proposer)
          x5[m][vi].view (t + 1) x5[m][vi].st).gjFrozen.ch = chp := by
        have h := htgt
        rw [Checkpoint.mk.injEq] at h
        exact h.1
      have hc : (processProposals (components (Fintype.card Node) kappa pool proposer)
          x5[m][vi].view (t + 1) x5[m][vi].st).gjFrozen.c = t + 1 := by omega
      have heta : (processProposals (components (Fintype.card Node) kappa pool proposer)
            x5[m][vi].view (t + 1) x5[m][vi].st).gjFrozen
          = ⟨(processProposals (components (Fintype.card Node) kappa pool proposer)
              x5[m][vi].view (t + 1) x5[m][vi].st).gjFrozen.ch,
            (processProposals (components (Fintype.card Node) kappa pool proposer)
              x5[m][vi].view (t + 1) x5[m][vi].st).gjFrozen.c⟩ := rfl
      rw [heta, hch, hc]
    refine ⟨m, pick5 x5 m vi (Q.slotLength * (t + 1) + Q.delta),
      (processProposals (components (Fintype.card Node) kappa pool proposer)
        x5[m][vi].view (t + 1) x5[m][vi].st).gjFrozen, htm,
      by rw [MfcEquiv.tick_time5 hlblm]; exact htm, ?_, Or.inr ?_⟩
    · rw [← htgt]
      exact hlog
    · rw [← hGeq]
      exact hJ

set_option maxHeartbeats 4000000 in
/-- **Lemma 18's justification step: `(chp, t+1)` is justified in every awake view from
    `voting(t+1) + Δ` on.** Each honest validator is active in slot `t+1`, so each sends a
    fin-vote targeting `(chp, t+1)` (`finvote_of_active5_next`), and their sources fall into
    two cases. If some honest validator's own view already justified `(chp, t+1)`, delivery
    carries that justification forward (`view_subset_of_time5`, `justifiedIn_mono`).
    Otherwise every honest source is the merge's `(GJ_p.ch, t)`, those votes are more than two
    thirds, and `justified_of_quorum_votes` justifies the target — `(GJ_p.ch, t)` being
    justified there by Lemma 18's first round, its slot below `t+1`, and its chain below
    `chp`. -/
theorem justified_chp_next5 {x5 : Exec Pr5 S} (H5 : SettingGA Q S x5) (hκ : 1 ≤ kappa)
    (hwin5 : MfcEquiv.HonestProposalWindow5 (kappa := kappa) x5)
    (hga : S.GlobalAwakeTime Q.gat Finset.univ)
    {t : Nat} (ht : 1 ≤ t)
    {vp : Node} {chp chC : Chain Tx} {qc : Option (QCert Node Tx)}
    {gjp : Checkpoint (Chain Tx)} {ip : Nat}
    (hsent : (⟨vp, Msg.propose chp chC qc gjp t⟩ : SignedMsg Node M) ∈ x5[ip].sent)
    (hhon_i : vp ∉ S.adv ((x5[ip].time : Int)))
    (hhon_t : vp ∉ S.adv (Q.voting (t : Int)))
    (hlow : gjp.c < t - 1)
    (hgat : (Q.gat : Int) ≤ Q.voting (t : Int) - 3 * (Q.delta : Int))
    {i : Nat} {w : Node} (hAw : x5.Awake i w)
    (htime : Q.slotLength * (t + 1) + 2 * Q.delta ≤ x5[i].time) :
    JustifiedIn (Fintype.card Node) x5[i][w].view ⟨chp, t + 1⟩ := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  obtain ⟨⟨hmc, hah, hsync, hmono, -, hdiv, hdil⟩, hstepw, hwpt, hone, ⟨hsyn, -⟩, -,
    ⟨hcb, hfn⟩, -⟩ := id H5
  have hexp : Q.slotLength * (t + 1) = Q.slotLength * t + Q.slotLength := Nat.mul_succ ..
  have hvot : Q.voting (t : Int) = ((Q.slotLength * t + Q.delta : Nat) : Int) := by
    unfold Params.voting
    push_cast
    omega
  have hvot1 : Q.voting ((t : Int) + 1)
      = ((Q.slotLength * (t + 1) + Q.delta : Nat) : Int) := by
    unfold Params.voting
    push_cast
    omega
  have hgat1 : (Q.gat : Int) ≤ Q.voting ((t : Int) + 1) - 3 * (Q.delta : Int) := by
    rw [hvot1]
    rw [hvot] at hgat
    have hstep : ((Q.slotLength * t + Q.delta : Nat) : Int)
        ≤ ((Q.slotLength * (t + 1) + Q.delta : Nat) : Int) := by
      have h : Q.slotLength * t + Q.delta ≤ Q.slotLength * (t + 1) + Q.delta := by omega
      exact_mod_cast h
    omega
  -- the honest validators, each active in slot `t+1` and each with its fin-vote
  have hcastn : (((t + 1 : Nat)) : Int) = (t : Int) + 1 := by push_cast; try omega
  have hcastv : Q.voting (((t + 1 : Nat)) : Int) = Q.voting ((t : Int) + 1) := by
    rw [hcastn]
  have hhon_of : ∀ q : Node, q ∈ (Finset.univ \ S.adv (Q.voting ((t : Int) + 1))) →
      q ∈ Active Q S ((t : Int) + 1) := by
    intro q hq
    rw [← hcastn]
    refine active_of_globalAwake hga (by rw [hcastv]; exact hgat1) ?_
    intro r _ h2 hadv
    rw [hcastv] at h2
    exact (Finset.mem_sdiff.mp hq).2 (hmc r _ h2 hadv)
  by_cases hcase : ∃ q ∈ (Finset.univ \ S.adv (Q.voting ((t : Int) + 1))),
      ∃ m : Nat, x5[m].time = Q.slotLength * (t + 1) + Q.delta ∧
        JustifiedIn (Fintype.card Node) x5[m][q].view ⟨chp, t + 1⟩
  · -- some honest validator already saw it justified; delivery carries that forward
    obtain ⟨q, -, m, htm, hJ⟩ := hcase
    exact justifiedIn_mono (view_subset_of_time5 hsyn hAw (by omega)) hJ
  · -- otherwise every honest fin-vote has the merge's checkpoint as its source
    refine justified_of_quorum_votes (C := ⟨gjp.ch, t⟩) ?_ (by show t < t + 1; omega) ?_
      (W := Finset.univ \ S.adv (Q.voting ((t : Int) + 1))) (honest_quorum hcb hfn _) ?_
    · -- `(GJ_p.ch, t)` is justified in this view
      exact rejustified_target5 H5 hga ht hsent hhon_i hhon_t hlow hgat hAw (by omega)
    · -- and its chain is below `chp`
      show chainLe gjp.ch chp
      obtain ⟨-, kp, -, -, -, -, -, hgjp, hchp, -, -⟩ :=
        propose_fields5 hsync hmc hmono hsent hhon_i
      rw [hgjp, hchp]
      exact chainLe_trans (gj_le_fastConfirm _ _)
        (chainLe_trans (base_le_mfc _ _ _ _) (chainLe_extend _ _ _))
    · intro q hq
      obtain ⟨m, ch, src, htm, htm1, hlog, hsrc⟩ :=
        finvote_of_active5_next H5 hκ hwin5 hga ht hsent hhon_i hhon_t hlow hgat
          (hhon_of q hq)
      rcases hsrc with hsrceq | hJ
      · -- the extension branch: the vote is a link from `(GJ_p.ch, t)`
        subst hsrceq
        refine ⟨ch, t + 1, ?_⟩
        refine hsyn (m + 1) i w _ hlog ?_ hAw
        rw [htm1]
        omega
      · exact absurd ⟨q, hq, m, htm, hJ⟩ hcase

set_option maxHeartbeats 1000000 in
/-- **Any two justified chains are comparable.** Each justified checkpoint's chain sits below
    some validator's available chain (`justified_to_voteChAva`, descending through fin-vote
    targets), and available chains are totally ordered (`chAva_comparable`, itself from
    Lemma 10's dominance and Algorithm 2's safety). Note what this is *not*: cross-slot
    nesting of justified checkpoints does not follow from the slashing conditions alone —
    conflicting justified checkpoints at different slots violate neither E1 nor E2 — so this
    goes through the available chain instead. -/
theorem justified_chains_comparable {x5 : Exec Pr5 S} (H5 : SettingGA Q S x5)
    (hκ : 1 ≤ kappa) (hwin5 : MfcEquiv.HonestProposalWindow5 (kappa := kappa) x5)
    {i₁ : Nat} {w₁ : Node} {C₁ : Checkpoint (Chain Tx)}
    (h₁ : JustifiedIn (Fintype.card Node) x5[i₁][w₁].view C₁)
    {i₂ : Nat} {w₂ : Node} {C₂ : Checkpoint (Chain Tx)}
    (h₂ : JustifiedIn (Fintype.card Node) x5[i₂][w₂].view C₂) :
    chainLe C₁.ch C₂.ch ∨ chainLe C₂.ch C₁.ch := by
  obtain ⟨⟨hmc, -, hsync, hmono, -, -, -⟩, -, -, -, -, -, ⟨hcb, hfn⟩, -⟩ := id H5
  -- each justified chain sits below some available chain
  have hdesc : ∀ (i : Nat) (w : Node) (C : Checkpoint (Chain Tx)),
      JustifiedIn (Fintype.card Node) x5[i][w].view C →
      ∃ (a : Nat) (v : Node), chainLe C.ch x5[a][v].st.chAva := by
    intro i w C hC
    rcases MfcEquiv.justified_to_voteChAva hsync hmc hmono hcb hfn (le_refl _)
        (i := i) C.c _ rfl i w (le_refl i) hC with hnil | hd
    · exact ⟨0, w, by rw [hnil]; exact chainLe_nil _⟩
    · obtain ⟨k, v, tr, -, hlbl, hmod, hgate, hle⟩ := hd
      exact ⟨k + 1, v, by rw [MfcEquiv.vote_tick_chAva hlbl hmod hgate]; exact hle⟩
  obtain ⟨a₁, v₁, hle₁⟩ := hdesc i₁ w₁ C₁ h₁
  obtain ⟨a₂, v₂, hle₂⟩ := hdesc i₂ w₂ C₂ h₂
  -- and available chains are totally ordered
  rcases Availability5.chAva_comparable H5 hκ hwin5 a₁ v₁ a₂ v₂ with h | h
  · exact comparable_of_common_extension (chainLe_trans hle₁ h) hle₂
  · exact comparable_of_common_extension hle₁ (chainLe_trans hle₂ h)

end Majorum.Finality5
