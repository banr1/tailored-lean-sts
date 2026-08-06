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
