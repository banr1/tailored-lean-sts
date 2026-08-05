import Examples.StsMultisetLog.majorum.Analysis.Proofs.Analysis2
import Examples.StsMultisetLog.majorum.Analysis.Proofs.Equivalence
import Examples.StsMultisetLog.majorum.Analysis.Proofs.Finality
import Examples.StsMultisetLog.majorum.Analysis.Proofs.Transfer

/-!
# MFC equivalence across the simulation (Lemma 10, stage C2)

The slot induction establishing Definition 9's conditions over `simulate x5`. This file
opens with the executions' snapshot discipline — each protocol's frozen view is a past
view, hence a subset of the current one — which is what lets `Majority_congr` run at
the vote-round call sites.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 400

namespace Majorum

open the framework's flat multiset-log flavour Classical

variable {Node Tx : Type} [DecidableEq Node] [DecidableEq Tx] [Fintype Node]
  {Q : Params} {S : Schedule Node} {n kappa : Nat} {pool : Nat → Tx}
  {proposer : Nat → Node}

local notation "Pr5" => protocol (components n kappa pool proposer) Q
local notation "Pr2" => protocol2 Q n kappa pool proposer
local notation "M" => Msg (Chain Tx) (QCert Node Tx)

/-- Algorithm 5's frozen view is a past view: a subset of the current one. -/
theorem vFrozen_subset_view5 {x5 : Exec Pr5 S} (k : Nat) (p : Node) :
    (x5.cfg k)[p].st.vFrozen ⊆ (x5.cfg k)[p].view := by
  induction k with
  | zero =>
      have h0 := x5.init.2.1 p
      show ((x5.cfg 0)[p]).st.vFrozen ⊆ ((x5.cfg 0)[p]).view
      rw [h0]
      intro a ha
      cases ha
  | succ k ih =>
      have h5 := exec5_succ (x5 := x5) k
      rw [h5]
      cases h : x5.lbl k with
      | advance t => exact ih
      | tick q t =>
          by_cases hq : q = p
          · subst hq
            intro a ha
            simp only [applyNodeStepResult_getElem, setClock_getElem,
              if_pos rfl, if_true] at ha ⊢
            rcases handler_vFrozen (components n kappa pool proposer) Q
                (pick5 x5 k q t) q t
                (x5.cfg k)[q].view (x5.cfg k)[q].st with hfz | hfz
            · rw [hfz] at ha
              exact ih ha
            · rw [hfz] at ha
              exact ha
          · intro a ha
            simp only [applyNodeStepResult_getElem, setClock_getElem,
              if_true, if_neg hq] at ha ⊢
            exact ih ha
      | deliver q m =>
          by_cases hq : q = p
          · subst hq
            intro a ha
            simp only [applyNodeStepResult_getElem, receive_getElem,
              if_pos rfl, if_true] at ha ⊢
            exact Finset.mem_insert_of_mem (ih ha)
          · intro a ha
            simp only [applyNodeStepResult_getElem, receive_getElem,
              if_true, if_neg hq] at ha ⊢
            exact ih ha
      | wake q =>
          by_cases hq : q = p
          · subst hq
            intro a ha
            simp only [applyNodeStepResult_getElem, if_pos rfl, if_true] at ha ⊢
            exact ih ha
          · intro a ha
            simp only [applyNodeStepResult_getElem, if_true, if_neg hq] at ha ⊢
            exact ih ha
      | custom q ev => exact ev.elim
      | adversarial q m => exact ih

/-- Algorithm 2's frozen view is a past view: a subset of the current one. -/
theorem vFrozen_subset_view2 {x : Exec Pr2 S} (k : Nat) (p : Node) :
    x[k][p].st.vFrozen ⊆ x[k][p].view := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  induction k with
  | zero =>
      have h0 := x.init.2.1 p
      show ((x.cfg 0)[p]).st.vFrozen ⊆ ((x.cfg 0)[p]).view
      rw [h0]
      intro a ha
      cases ha
  | succ k ih =>
      by_cases hlp : ∃ tr, x.lbl k = .tick p tr
      case neg =>
        have hfz := (frozen_step2 (fun tr hr => absurd ⟨tr, hr⟩ hlp)).1
        rw [hfz]
        exact ih.trans (view_mono k p)
      case pos =>
      obtain ⟨tr, hr⟩ := hlp
      have hview := tick_view (x := x) hr p
      by_cases hph3 : tr % Q.slotLength = 3 * Q.delta
      · -- the merge tick refreezes to its own view
        obtain ⟨dt, pk, -, hst, -⟩ := tick_effect hr
        rw [handler2_merge hph3] at hst
        intro a ha
        rw [hst] at ha
        rw [hview]
        exact ha
      · by_cases hph1 : tr % Q.slotLength = Q.delta
        · -- the vote tick's proposal processing keeps the snapshot
          obtain ⟨dt, pk, -, hst, -⟩ := tick_effect hr
          rw [handler2_vote_state hph1] at hst
          have hfz : x[k + 1][p].st.vFrozen = x[k][p].st.vFrozen := by
            rw [hst, processProposals2_vFrozen]
          rw [hfz, hview]
          exact ih
        · have hfz := (frozen_step2 (x := x) (m := k) (p := p) (fun tr' hr' => by
            rw [hr] at hr'
            injection hr' with h1 h2
            first
              | exact h2 ▸ ⟨hph1, hph3⟩
              | exact ⟨hph1, hph3⟩)).1
          rw [hfz]
          exact ih.trans (view_mono k p)

/-! ### Definition 8, tablewise: the running invariant of the slot induction -/

/-- `DynEq` is reflexive. -/
theorem DynEq.refl (m : M) : DynEq m m := by
  cases m <;> exact ⟨rfl, rfl⟩

/-- The correspondence table is `SDynEq` at step `k` — Definition 8 for the simulation,
    tablewise: every key corresponds to its image. The mutual slot induction's running
    invariant. -/
def TableDynEq (x5 : Exec Pr5 S) (k : Nat) : Prop :=
  ∀ sm : SignedMsg Node M, SDynEq sm ((simState x5 k).2 sm)

theorem tableDynEq_zero (x5 : Exec Pr5 S) : TableDynEq x5 0 :=
  fun sm => ⟨rfl, DynEq.refl sm.msg⟩

/-- An `SDynEq` table makes every validator's two views correspond in Definition 8's
    set form — the shape `Majority_congr` and the skeleton layer consume. -/
theorem viewCorr_of_tableDynEq {x5 : Exec Pr5 S} (hone : OneTickPerReading x5)
    (hmc : S.MonotoneCorruption) (hah : S.AwakeHonest) (hmono : TimeMonotone x5)
    {k : Nat} (h : TableDynEq x5 k) (q : Node) :
    ViewCorr (x5.cfg k)[q].view (simState x5 k).1[q].view := by
  constructor
  · intro sm hsm
    exact ⟨(simState x5 k).2 sm, view_image hone hmc hah hmono k q hsm, h sm⟩
  · intro sm' hsm'
    obtain ⟨m5, hm5, rfl⟩ := view_covered hone hmc hah hmono k q hsm'
    exact ⟨m5, hm5, h m5⟩

/-! ### The vote pick aligns across corresponding views -/

/-- At the concrete instance, Algorithm 5's hit set *is* Algorithm 2's — elementwise;
    the sets are built with independently synthesized `DecidableEq` instances, so this
    is an `ext`, not a `rfl`. -/
theorem components_voteHits (V : View Node M) (slot : Nat) (chMFC : Chain Tx) :
    (components n kappa pool proposer).voteHits V slot chMFC
      = voteHits2 proposer V slot chMFC := by
  ext c
  rw [mem_voteHits2]
  unfold Components.voteHits
  rw [Finset.mem_biUnion]
  simp only [components]
  constructor
  · rintro ⟨sm, hsm, hc⟩
    revert hc
    cases hmsg : sm.msg with
    | vote e src tgt t' =>
        intro hc
        exact absurd hc (Finset.notMem_empty c)
    | propose chp chC qc ck t' =>
        dsimp only
        split_ifs with hcond
        · intro hc
          rw [Finset.mem_singleton] at hc
          subst hc
          simp only [Bool.and_eq_true, beq_iff_eq] at hcond
          obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hcond
          exact ⟨sm, hsm, ⟨chC, qc, ck, by subst h2; exact hmsg⟩, h1, h3, h4, h5⟩
        · intro hc
          exact absurd hc (Finset.notMem_empty c)
  · rintro ⟨sm, hsm, ⟨chC, qc, ck, hmsg⟩, h1, h3, h4, h5⟩
    refine ⟨sm, hsm, ?_⟩
    rw [hmsg]
    dsimp only
    rw [if_pos (by simp [h1, h3, h4, h5])]
    exact Finset.mem_singleton_self c

/-- Corresponding views have the same hit set at any given fork-choice output:
    everything the filter reads — signer, proposed chain, slot — survives dynamic
    equivalence. -/
theorem voteHits2_corr {V5 V2 : View Node M} (hcorr : ViewCorr V5 V2)
    (slot : Nat) (chMFC : Chain Tx) :
    voteHits2 (Tx := Tx) proposer V5 slot chMFC = voteHits2 proposer V2 slot chMFC := by
  have transfer : ∀ {Va Vb : View Node M}, (∀ sm ∈ Va, ∃ sm' ∈ Vb, SDynEq sm sm') →
      ∀ c, c ∈ voteHits2 (Tx := Tx) proposer Va slot chMFC →
        c ∈ voteHits2 proposer Vb slot chMFC := by
    intro Va Vb hdir c hc
    obtain ⟨sm, hsm, ⟨chC, qc, ck, hmsg⟩, h1, h3, h4, h5⟩ := mem_voteHits2.mp hc
    obtain ⟨sm', hsm', hsender, hde⟩ := hdir sm hsm
    rw [hmsg] at hde
    rcases hm' : sm'.msg with ⟨chp', chC', qc', ck', t'⟩ | ⟨e', src', tgt', sl'⟩ <;>
      rw [hm'] at hde
    · obtain ⟨hchp, hslot⟩ := hde
      exact mem_voteHits2.mpr ⟨sm', hsm', ⟨chC', qc', ck',
          by rw [hm', ← hchp, ← hslot]⟩,
        hsender ▸ h1, h3, h4, h5⟩
    · cases hde
  ext c
  exact ⟨transfer hcorr.1 c, transfer (fun sm' hsm' => by
    obtain ⟨sm, hsm, hsde⟩ := hcorr.2 sm' hsm'
    exact ⟨sm, hsm, hsde.symm⟩) c⟩

/-- **The simulated pick is the original's** whenever the two vote views correspond and
    the two fork-choice outputs agree — the reduction of condition 2.7's vote half to
    conditions 2.1–2.2's MFC agreement. -/
theorem simPick_eq_pick5 {x5 : Exec Pr5 S} {k : Nat} {p : Node} {t : Time}
    (hlbl : x5.lbl k = .tick p t)
    (hcorr : ViewCorr (x5.cfg k)[p].view (simState x5 k).1[p].view)
    (hmfc :
      (components n kappa pool proposer).mfc
          (processProposals (components n kappa pool proposer)
            (x5.cfg k)[p].view (t / Q.slotLength) (x5.cfg k)[p].st).vFrozen
          (x5.cfg k)[p].view
          (processProposals (components n kappa pool proposer)
            (x5.cfg k)[p].view (t / Q.slotLength) (x5.cfg k)[p].st).chFrozen
          (t / Q.slotLength)
        = mfc
          (processProposals2 n proposer
            (simState x5 k).1[p].view (t / Q.slotLength) (simState x5 k).1[p].st).vFrozen
          (simState x5 k).1[p].view
          (processProposals2 n proposer
            (simState x5 k).1[p].view (t / Q.slotLength) (simState x5 k).1[p].st).chFrozen
          (t / Q.slotLength)) :
    simPick x5 k p t (setClock p t (simState x5 k).1)[p].view
      (setClock p t (simState x5 k).1)[p].st = pick5 x5 k p t := by
  have hmem5 := pick5_mem hlbl
  have hmem2 : pick5 x5 k p t ∈ votePicks2 Q n proposer
      (setClock p t (simState x5 k).1)[p].view t
      (setClock p t (simState x5 k).1)[p].st := by
    simp only [Components.votePicks, setClock_getElem, if_pos rfl, if_true] at hmem5
    simp only [votePicks2, setClock_getElem, if_pos rfl, if_true]
    rw [components_voteHits] at hmem5
    rw [← hmfc, ← voteHits2_corr hcorr]
    exact hmem5
  unfold simPick
  rw [if_pos hmem2]

/-! ### The tick sends align, phase by phase -/

/-- Algorithm 5's propose-phase send, exactly. -/
theorem handler_propose_send {C : Components Node (Chain Tx) (QCert Node Tx)}
    {pick : Chain Tx} {p : Node} {r : Time} {V : View Node M}
    {s : NodeState Node (Chain Tx) (QCert Node Tx)} {m : M}
    (hmod : r % Q.slotLength = 0)
    (h : m ∈ (handlerCore C Q pick p r V s).send) :
    p = C.proposer (r / Q.slotLength) ∧ s.activeAt ≤ r ∧
      m = .propose (C.extend (C.mfc V V (C.fastConfirm V (r / Q.slotLength - 1)).1
          (r / Q.slotLength)) (r / Q.slotLength))
        (C.fastConfirm V (r / Q.slotLength - 1)).1
        (C.fastConfirm V (r / Q.slotLength - 1)).2 (C.gj V) (r / Q.slotLength) := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  simp only [handlerCore, apply_ite NodeStepResult.send] at h
  split_ifs at h <;> first | omega | simp at h
  exact ⟨‹p = C.proposer (r / Q.slotLength) ∧ s.activeAt ≤ r›.1,
    ‹p = C.proposer (r / Q.slotLength) ∧ s.activeAt ≤ r›.2, h⟩

/-- Algorithm 5's vote-phase send content: a vote for the pick, at the reading's
    slot. -/
theorem handler_vote_content {C : Components Node (Chain Tx) (QCert Node Tx)}
    {pick : Chain Tx} {p : Node} {r : Time} {V : View Node M}
    {s : NodeState Node (Chain Tx) (QCert Node Tx)} {m : M}
    (hmod : r % Q.slotLength = Q.delta)
    (h : m ∈ (handlerCore C Q pick p r V s).send) :
    ∃ src tgt, m = .vote pick src tgt (r / Q.slotLength) := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  simp only [handlerCore, apply_ite NodeStepResult.send] at h
  split_ifs at h <;> first | omega | simp at h
  all_goals exact ⟨_, _, h⟩

/-- The instance's block builder is Algorithm 2's. -/
theorem components_extend :
    (components (Node := Node) n kappa pool proposer).extend = extend pool := rfl

/-- **The table stays `SDynEq` across one step**, given the two per-phase alignment
    facts at this step's tick (vacuous off ticks): the propose-round fork choices
    agree, and the simulated pick is the original's. The slot induction supplies both
    from conditions 2.1–2.2. -/
theorem tableDynEq_step {x5 : Exec Pr5 S} {k : Nat} (h : TableDynEq x5 k)
    (hP : ∀ p t, x5.lbl k = .tick p t → t % Q.slotLength = 0 →
      (components n kappa pool proposer).mfc (x5.cfg k)[p].view (x5.cfg k)[p].view
          ((components n kappa pool proposer).fastConfirm (x5.cfg k)[p].view
            (t / Q.slotLength - 1)).1 (t / Q.slotLength)
        = mfc (simState x5 k).1[p].view (simState x5 k).1[p].view
          (fastConfirmSimple n (simState x5 k).1[p].view (t / Q.slotLength - 1)).1
          (t / Q.slotLength))
    (hV : ∀ p t, x5.lbl k = .tick p t → t % Q.slotLength = Q.delta →
      x5[k][p].st.activeAt ≤ t →
      simPick x5 k p t (setClock p t (simState x5 k).1)[p].view
        (setClock p t (simState x5 k).1)[p].st = pick5 x5 k p t) :
    TableDynEq x5 (k + 1) := by
  intro sm
  show SDynEq sm ((simStep x5 k (simState x5 k)).2 sm)
  cases hl : x5.lbl k with
  | advance t => simp only [simStep, hl]; exact h sm
  | tick p t =>
      simp only [simStep, hl]
      by_cases hcond : sm.sender = p ∧ sm.msg ∈
          (handlerCore (components n kappa pool proposer) Q (pick5 x5 k p t) p t
            (setClock p t (x5.cfg k))[p].view (setClock p t (x5.cfg k))[p].st).send
      · rw [if_pos hcond]
        cases hso : sendOf (handler2Core Q n kappa pool proposer simBlank
            (simPick x5 k p t (setClock p t (simState x5 k).1)[p].view
              (setClock p t (simState x5 k).1)[p].st) p t
            (setClock p t (simState x5 k).1)[p].view
            (setClock p t (simState x5 k).1)[p].st) with
        | none => exact h sm
        | some m2 =>
            refine ⟨hcond.1, ?_⟩
            have hm2 := sendOf_mem hso
            obtain ⟨-, hshape⟩ := mem_handler_send hcond.2
            rcases hshape with ⟨-, -, -, -, -, hmod⟩ | ⟨-, -, -, -, hmod⟩
            · -- propose reading: both chains are the extended fork choice
              obtain ⟨-, -, hm5⟩ := handler_propose_send hmod hcond.2
              obtain ⟨-, -, hm2'⟩ := handler2_propose_send hmod hm2
              rw [hm5, hm2']
              refine ⟨?_, rfl⟩
              have hmfc := hP p t hl hmod
              simp only [setClock_getElem, if_pos rfl, if_true]
              rw [components_extend, hmfc]
            · -- vote reading: both chains are the (aligned) pick; the fired send
              -- opens the joining check
              obtain ⟨src, tgt, hm5⟩ := handler_vote_content hmod hcond.2
              have hm2' := handler2_vote_content hmod hm2
              rw [hm5, hm2']
              have hgate : x5[k][p].st.activeAt ≤ t := by
                have hg := (mem_handler_send hcond.2).1
                simp only [setClock_getElem, if_pos rfl, if_true] at hg
                exact hg
              exact ⟨(hV p t hl hmod hgate).symm, rfl⟩
      · rw [if_neg hcond]
        exact h sm
  | deliver q m' => simp only [simStep, hl]; exact h sm
  | wake q => simp only [simStep, hl]; exact h sm
  | custom q ev => exact ev.elim
  | adversarial q m' => simp only [simStep, hl]; exact h sm

/-! ### The frozen views correspond: both runs freeze at the same merge ticks -/

/-- Algorithm 5's core refreezes the view exactly at the merge phase. -/
theorem handler_merge_vFrozen {C : Components Node (Chain Tx) (QCert Node Tx)}
    {pick : Chain Tx} {p : Node} {r : Time} {V : View Node M}
    {s : NodeState Node (Chain Tx) (QCert Node Tx)}
    (hmod : r % Q.slotLength = 3 * Q.delta) :
    (handlerCore C Q pick p r V s).state.vFrozen = V := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  simp only [handlerCore, apply_ite NodeStepResult.state]
  split_ifs <;> first | rfl | omega

/-- Off the merge phase, Algorithm 5's core keeps the frozen view. -/
theorem handler_vFrozen_quiet {C : Components Node (Chain Tx) (QCert Node Tx)}
    {pick : Chain Tx} {p : Node} {r : Time} {V : View Node M}
    {s : NodeState Node (Chain Tx) (QCert Node Tx)}
    (hmod : r % Q.slotLength ≠ 3 * Q.delta) :
    (handlerCore C Q pick p r V s).state.vFrozen = s.vFrozen := by
  simp only [handlerCore, apply_ite NodeStepResult.state]
  split_ifs <;>
    first
      | rfl
      | exact absurd ‹r % Q.slotLength = 3 * Q.delta› hmod
      | exact processProposals_vFrozen C V _ s

/-- Off the merge phase, Algorithm 2's core keeps the frozen view. -/
theorem handler2_vFrozen_quiet {p : Node} {r : Time} {V : View Node M}
    {s : NodeState2 Node Tx} {dot : Checkpoint (Chain Tx)} {pick : Chain Tx}
    (hmod : r % Q.slotLength ≠ 3 * Q.delta) :
    (handler2Core Q n kappa pool proposer dot pick p r V s).state.vFrozen
      = s.vFrozen := by
  simp only [handler2Core, apply_ite NodeStepResult.state]
  split_ifs <;>
    first
      | rfl
      | exact absurd ‹r % Q.slotLength = 3 * Q.delta› hmod
      | exact processProposals2_vFrozen _ _ _

/-- **The frozen views correspond** whenever the table has been `SDynEq` all along:
    both runs freeze their current views at the same merge ticks, and those views
    correspond by the table. -/
theorem frozen_viewCorr {x5 : Exec Pr5 S} (hone : OneTickPerReading x5)
    (hmc : S.MonotoneCorruption) (hah : S.AwakeHonest) (hmono : TimeMonotone x5)
    (k : Nat) (hTD : ∀ j, j ≤ k → TableDynEq x5 j) (q : Node) :
    ViewCorr (x5.cfg k)[q].st.vFrozen (simState x5 k).1[q].st.vFrozen := by
  induction k with
  | zero =>
      rw [x5.init.2.1 q]
      show ViewCorr ∅ (simState x5 0).1[q].st.vFrozen
      exact ⟨fun sm hsm => absurd hsm (Finset.notMem_empty sm),
        fun sm hsm => absurd hsm (Finset.notMem_empty sm)⟩
  | succ k ih =>
      have ih' := ih (fun j hj => hTD j (Nat.le_succ_of_le hj))
      have h5 := exec5_succ (x5 := x5) k
      rw [h5]
      cases h : x5.lbl k with
      | advance t =>
          have e2 : (simState x5 (k + 1)).1[q].st.vFrozen
              = (simState x5 k).1[q].st.vFrozen := by
            show (simStep x5 k (simState x5 k)).1[q].st.vFrozen = _
            simp only [simStep, h]
            rfl
          rw [e2]
          exact ih'
      | tick p t =>
          by_cases hq : q = p
          · subst hq
            simp only [applyNodeStepResult_getElem, setClock_getElem, if_pos rfl,
              if_true]
            by_cases hph : t % Q.slotLength = 3 * Q.delta
            · -- both refreeze to their current views, which correspond
              rw [handler_merge_vFrozen hph]
              have e2 : (simState x5 (k + 1)).1[q].st.vFrozen
                  = (simState x5 k).1[q].view := by
                show (simStep x5 k (simState x5 k)).1[q].st.vFrozen = _
                simp only [simStep, h]
                simp only [applyNodeStepResult_getElem, setClock_getElem, if_pos rfl,
                  if_true]
                rw [handler2_merge hph]
              rw [e2]
              exact viewCorr_of_tableDynEq hone hmc hah hmono
                (hTD k (Nat.le_succ k)) q
            · -- both keep their snapshots
              rw [handler_vFrozen_quiet hph]
              have e2 : (simState x5 (k + 1)).1[q].st.vFrozen
                  = (simState x5 k).1[q].st.vFrozen := by
                show (simStep x5 k (simState x5 k)).1[q].st.vFrozen = _
                simp only [simStep, h]
                simp only [applyNodeStepResult_getElem, setClock_getElem, if_pos rfl,
                  if_true]
                rw [handler2_vFrozen_quiet hph]
              rw [e2]
              exact ih'
          · simp only [applyNodeStepResult_getElem, setClock_getElem, if_true,
              if_neg (fun hh => hq (Eq.symm hh))]
            have e2 : (simState x5 (k + 1)).1[q].st.vFrozen
                = (simState x5 k).1[q].st.vFrozen := by
              show (simStep x5 k (simState x5 k)).1[q].st.vFrozen = _
              simp only [simStep, h]
              simp [applyNodeStepResult_getElem, setClock_getElem,
                if_neg (fun hh => hq (Eq.symm hh))]
            rw [e2]
            exact ih'
      | deliver p m =>
          have e2 : (simState x5 (k + 1)).1[q].st.vFrozen
              = (simState x5 k).1[q].st.vFrozen := by
            show (simStep x5 k (simState x5 k)).1[q].st.vFrozen = _
            simp only [simStep, h]
            by_cases hq : q = p
            · subst hq
              simp [applyNodeStepResult_getElem, receive_getElem]
            · simp [applyNodeStepResult_getElem, receive_getElem,
                if_neg (fun hh => hq (Eq.symm hh))]
          rw [e2]
          by_cases hq : q = p
          · subst hq
            simp only [applyNodeStepResult_getElem, receive_getElem, if_pos rfl,
              if_true]
            exact ih'
          · simp only [applyNodeStepResult_getElem, receive_getElem,
              if_neg (fun hh => hq (Eq.symm hh))]
            exact ih'
      | wake p =>
          have e2 : (simState x5 (k + 1)).1[q].st.vFrozen
              = (simState x5 k).1[q].st.vFrozen := by
            show (simStep x5 k (simState x5 k)).1[q].st.vFrozen = _
            simp only [simStep, h]
            by_cases hq : q = p
            · subst hq
              simp only [applyNodeStepResult_getElem, if_pos rfl, if_true]
            · simp [applyNodeStepResult_getElem, if_neg (fun hh => hq (Eq.symm hh))]
          rw [e2]
          by_cases hq : q = p
          · subst hq
            simp only [applyNodeStepResult_getElem, if_pos rfl, if_true]
            exact ih'
          · simp only [applyNodeStepResult_getElem,
              if_neg (fun hh => hq (Eq.symm hh))]
            exact ih'
      | custom p ev => exact ev.elim
      | adversarial p m =>
          have e2 : (simState x5 (k + 1)).1[q].st.vFrozen
              = (simState x5 k).1[q].st.vFrozen := by
            show (simStep x5 k (simState x5 k)).1[q].st.vFrozen = _
            simp only [simStep, h]
            rfl
          rw [e2]
          exact ih'

/-! ### Condition 2.1, assembled: the propose-round fork choices agree -/

/-- The instance's fork choice, fast confirmation and greatest-justified are
    Algorithm 2's. -/
theorem components_mfc :
    (components (Node := Node) n kappa pool proposer).mfc = mfc := rfl

theorem components_fastConfirmSimple :
    (components (Node := Node) n kappa pool proposer).fastConfirmSimple
      = fastConfirmSimple n := rfl

theorem components_gj :
    (components (Node := Node) n kappa pool proposer).gj = gj n := rfl

theorem components_prefixLe :
    (components (Node := Node) n kappa pool proposer).prefixLe = chainLe := rfl

/-- **Condition 2.1's assembly**: the two propose-round fork choices agree, given the
    views' skeleton equality and the 2.5 bound on the greatest justified chain. The
    simple fast-confirmations coincide by congruence, so either the bases are equal
    (`fastconfirm`'s quorum branch), or Algorithm 5's base is the justified chain —
    and then both bases are prefixes of the simulated output (2.5 and `base_le_mfc`),
    hence comparable, the branch guard orients them, and the base swap closes. -/
theorem mfc_propose_agree {V5 V2 : View Node M} {t : Nat}
    (hskel : voteSkel V5 = voteSkel V2)
    (h25 : chainLe (gj n V5).ch
      (mfc V2 V2 (fastConfirmSimple n V2 (t - 1)).1 t)) :
    (components n kappa pool proposer).mfc V5 V5
        ((components n kappa pool proposer).fastConfirm V5 (t - 1)).1 t
      = mfc V2 V2 (fastConfirmSimple n V2 (t - 1)).1 t := by
  have hfcs : fastConfirmSimple n V5 (t - 1) = fastConfirmSimple n V2 (t - 1) :=
    fastConfirmSimple_congr hskel n (t - 1)
  rw [components_mfc]
  unfold Components.fastConfirm
  rw [components_fastConfirmSimple, components_gj, components_prefixLe, hfcs]
  by_cases hguard : chainLe (gj n V5).ch (fastConfirmSimple n V2 (t - 1)).1
  · rw [if_pos hguard]
    exact mfc_congr hskel hskel (Finset.Subset.refl _) (Finset.Subset.refl _) _ t
  · rw [if_neg hguard]
    have hb2le : chainLe (fastConfirmSimple n V2 (t - 1)).1
        (mfc V2 V2 (fastConfirmSimple n V2 (t - 1)).1 t) := base_le_mfc V2 V2 _ t
    have hb2b5 : chainLe (fastConfirmSimple n V2 (t - 1)).1 (gj n V5).ch := by
      rcases comparable_of_common_extension h25 hb2le with h | h
      · exact absurd h hguard
      · exact h
    have hswap : mfc V2 V2 (gj n V5).ch t
        = mfc V2 V2 (fastConfirmSimple n V2 (t - 1)).1 t :=
      mfc_base_swap
        (chainLe_trans hb2b5 (base_le_mfc V2 V2 (gj n V5).ch t)) h25
    calc mfc V5 V5 (gj n V5).ch t
        = mfc V2 V2 (gj n V5).ch t :=
          mfc_congr hskel hskel (Finset.Subset.refl _) (Finset.Subset.refl _) _ t
      _ = mfc V2 V2 (fastConfirmSimple n V2 (t - 1)).1 t := hswap

/-- **Condition 2.2's assembly**: the two vote-round fork choices agree, given the
    frozen and current views' skeleton equalities, the snapshot discipline, and the
    two cross-bounds on the (divergent) frozen bases — which the slot induction
    supplies from the justified-chain and quorum arguments. -/
theorem mfc_vote_agree {Vf5 V5 Vf2 V2 : View Node M} {b5 b2 : Chain Tx} {t : Nat}
    (hskelF : voteSkel Vf5 = voteSkel Vf2) (hskel : voteSkel V5 = voteSkel V2)
    (hsub5 : Vf5 ⊆ V5) (hsub2 : Vf2 ⊆ V2)
    (h5 : chainLe b5 (mfc Vf2 V2 b2 t)) (h2 : chainLe b2 (mfc Vf2 V2 b5 t)) :
    mfc Vf5 V5 b5 t = mfc Vf2 V2 b2 t :=
  calc mfc Vf5 V5 b5 t
      = mfc Vf2 V2 b5 t := mfc_congr hskelF hskel hsub5 hsub2 b5 t
    _ = mfc Vf2 V2 b2 t := mfc_base_swap h2 h5

/-! ### Algorithm 5's frozen greatest-justified checkpoint is justified -/

/-- The proposal fold only ever adopts justified checkpoints. -/
theorem processProposals_gjFrozen_justified {V : View Node M} {t : Nat}
    {s : NodeState Node (Chain Tx) (QCert Node Tx)}
    (h : JustifiedIn n V s.gjFrozen) :
    JustifiedIn n V
      (processProposals (components n kappa pool proposer) V t s).gjFrozen := by
  unfold processProposals
  generalize V.toList = l
  induction l generalizing s with
  | nil => exact h
  | cons a l ih =>
      rw [List.foldl_cons]
      refine ih ?_
      cases hmsg : a.msg with
      | vote e src tgt t' => exact h
      | propose chp chC qc gjp t' =>
          dsimp only
          simp only [apply_ite NodeState.gjFrozen, ite_self]
          split_ifs with hcond
          · exact of_decide_eq_true hcond.2.2.1
          · exact h
  
/-- Algorithm 5's frozen greatest-justified checkpoint is justified in the current
    view, always: genesis at start, `GJ` of the current view at merges, a
    justification-checked proposal checkpoint at the vote reading — and justification
    only grows with the view. -/
theorem gjFrozen_justified {x5 : Exec Pr5 S} (k : Nat) (q : Node) :
    JustifiedIn n (x5.cfg k)[q].view (x5.cfg k)[q].st.gjFrozen := by
  induction k with
  | zero =>
      rw [x5.init.2.1 q]
      exact .genesis
  | succ k ih =>
      have h5 := exec5_succ (x5 := x5) k
      rw [h5]
      cases h : x5.lbl k with
      | advance t => exact ih
      | tick q' t =>
          by_cases hq : q = q'
          · subst hq
            simp only [applyNodeStepResult_getElem, setClock_getElem, if_pos rfl,
              if_true]
            have hgjV := gj_justified n (x5.cfg k)[q].view
            rw [← congrFun (components_gj (Node := Node) (n := n) (kappa := kappa)
              (pool := pool) (proposer := proposer)) (x5.cfg k)[q].view] at hgjV
            simp only [handlerCore, apply_ite NodeStepResult.state]
            split_ifs <;>
              first
                | exact ih
                | exact processProposals_gjFrozen_justified ih
                | exact hgjV
          · simp only [applyNodeStepResult_getElem, setClock_getElem, if_true,
              if_neg (fun hh => hq (Eq.symm hh))]
            exact ih
      | deliver q' m =>
          by_cases hq : q = q'
          · subst hq
            simp only [applyNodeStepResult_getElem, receive_getElem, if_pos rfl,
              if_true]
            exact justifiedIn_mono (Finset.subset_insert m _) ih
          · simp only [applyNodeStepResult_getElem, receive_getElem,
              if_neg (fun hh => hq (Eq.symm hh))]
            exact ih
      | wake q' =>
          by_cases hq : q = q'
          · subst hq
            simp only [applyNodeStepResult_getElem, if_pos rfl, if_true]
            exact ih
          · simp only [applyNodeStepResult_getElem,
              if_neg (fun hh => hq (Eq.symm hh))]
            exact ih
      | custom q' ev => exact ev.elim
      | adversarial q' m => exact ih

/-! ### The 2.5 leg's raw materials -/

/-- **A supermajority has an honest member at any round**: `2n/3` supporters against a
    corruption budget below `n/3` over at most `n` validators. -/
theorem exists_honest_of_quorum {A : Finset Node} {r : Int}
    (hcb : S.CorruptionBounded Q.f) (hfn : 3 * Q.f < n)
    (hcard : Fintype.card Node ≤ n) (hA : 2 * n ≤ 3 * A.card) :
    ∃ w ∈ A, w ∉ S.adv r := by
  by_contra hall
  push_neg at hall
  have hsub : A ⊆ S.adv r := hall
  have hle : A.card ≤ Q.f := le_trans (Finset.card_le_card hsub) (hcb r)
  have hcard' : A.card ≤ Fintype.card Node := Finset.card_le_univ A
  omega

/-- Algorithm 5's vote-phase send, in full: the pick, the processed frozen
    greatest-justified as source, and the two-mode target. -/
theorem handler_vote_fin_content {C : Components Node (Chain Tx) (QCert Node Tx)}
    {pick : Chain Tx} {p : Node} {r : Time} {V : View Node M}
    {s : NodeState Node (Chain Tx) (QCert Node Tx)} {m : M}
    (hmod : r % Q.slotLength = Q.delta)
    (h : m ∈ (handlerCore C Q pick p r V s).send) :
    m = .vote pick
      (processProposals C V (r / Q.slotLength) s).gjFrozen
      (if (processProposals C V (r / Q.slotLength) s).gjFrozen.c
          = r / Q.slotLength - 1 then
        ⟨[(processProposals C V (r / Q.slotLength) s).chAva,
            C.kappaPrefix (r / Q.slotLength)
              (C.mfc (processProposals C V (r / Q.slotLength) s).vFrozen V
                (processProposals C V (r / Q.slotLength) s).chFrozen
                (r / Q.slotLength)),
            (processProposals C V (r / Q.slotLength) s).gjFrozen.ch].foldl
          (fun acc ch => if C.prefixLe ch
              (C.mfc (processProposals C V (r / Q.slotLength) s).vFrozen V
                (processProposals C V (r / Q.slotLength) s).chFrozen
                (r / Q.slotLength)) then C.maxCh acc ch else acc)
          (processProposals C V (r / Q.slotLength) s).chAva,
          r / Q.slotLength⟩
      else ⟨(processProposals C V (r / Q.slotLength) s).gjFrozen.ch,
          r / Q.slotLength⟩)
      (r / Q.slotLength) := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  simp only [handlerCore, apply_ite NodeStepResult.send] at h
  split_ifs at h <;> first | omega | simp at h
  all_goals simp_all

/-- The vote-tick `chAva` fold output at step `k` of validator `w`, at reading `t` —
    the chain the tick writes to `chAva` and, in the fresh-checkpoint mode, fin-votes
    for. Named so `justified_le_of_chAva_le`'s hypothesis and the step induction spell
    it identically. -/
noncomputable def voteChAva (x5 : Exec Pr5 S) (k : Nat) (w : Node) (t : Time) :
    Chain Tx :=
  [(processProposals (components n kappa pool proposer)
      x5[k][w].view (t / Q.slotLength) x5[k][w].st).chAva,
    (components n kappa pool proposer).kappaPrefix (t / Q.slotLength)
      ((components n kappa pool proposer).mfc
        (processProposals (components n kappa pool proposer)
          x5[k][w].view (t / Q.slotLength) x5[k][w].st).vFrozen
        x5[k][w].view
        (processProposals (components n kappa pool proposer)
          x5[k][w].view (t / Q.slotLength) x5[k][w].st).chFrozen
        (t / Q.slotLength)),
    (processProposals (components n kappa pool proposer)
      x5[k][w].view (t / Q.slotLength) x5[k][w].st).gjFrozen.ch].foldl
    (fun acc ch => if (components n kappa pool proposer).prefixLe ch
        ((components n kappa pool proposer).mfc
          (processProposals (components n kappa pool proposer)
            x5[k][w].view (t / Q.slotLength) x5[k][w].st).vFrozen
          x5[k][w].view
          (processProposals (components n kappa pool proposer)
            x5[k][w].view (t / Q.slotLength) x5[k][w].st).chFrozen
          (t / Q.slotLength)) then
      (components n kappa pool proposer).maxCh acc ch
    else acc)
    (processProposals (components n kappa pool proposer)
      x5[k][w].view (t / Q.slotLength) x5[k][w].st).chAva

/-- **Condition 2.5/2.6's engine**: a checkpoint justified in *any* honest-reachable
    view by step `i` is below any chain `M2` that dominates every earlier honest
    vote-tick's `chAva` output. Strong induction on the checkpoint slot; the inner
    claim quantifies over all (step, validator) pairs, so the fresh-checkpoint mode
    hands off to the `chAva` bound and the stale mode *descends inside the fin-voter's
    own view at its own step* — the target's chain equals its source's, the source is
    the voter's processed `gjFrozen` (justified there), and link validity strictly
    drops the slot. No `Relay`, no slack: justification is consumed where it lives. -/
theorem justified_le_of_chAva_le {x5 : Exec Pr5 S}
    (hsync : SynchronizedClocks x5) (hmc : S.MonotoneCorruption)
    (hmono : TimeMonotone x5)
    (hcb : S.CorruptionBounded Q.f) (hfn : 3 * Q.f < n)
    (hcard : Fintype.card Node ≤ n)
    {i : Nat} {M2 : Chain Tx}
    (hchAva : ∀ (k : Nat) (w : Node) (t : Time), k < i → x5.lbl k = .tick w t →
      t % Q.slotLength = Q.delta → chainLe (voteChAva x5 k w t) M2)
    (cJ : Nat) :
    ∀ (J : Checkpoint (Chain Tx)), J.c = cJ →
    ∀ (j : Nat) (q : Node), j ≤ i →
      JustifiedIn n x5[j][q].view J → chainLe J.ch M2 := by
  induction cJ using Nat.strong_induction_on with
  | _ cJ IH =>
  intro J hJc j q hji hJ
  cases hJ with
  | genesis => exact chainLe_nil M2
  | @link C _ hC hlink =>
      -- an honest-at-`j` link voter, its fin-vote, and that vote's provenance
      obtain ⟨w, hwA, hwhon⟩ := exists_honest_of_quorum (r := (x5[j].time : Int))
        hcb hfn hcard hlink.2.2
      obtain ⟨sm, hsmV, hsmw, e, τ, hsmmsg⟩ := mem_linkVoters hwA
      have hsmsent : sm ∈ x5[j].sent := views_sound x5 j q sm hsmV
      have hhon : sm.sender ∉ S.adv (x5[j].time : Int) := by
        rw [hsmw]
        exact hwhon
      obtain ⟨k, hkj, hlblk, htimek, -, -, pk, hpk, hsend⟩ :=
        vote_provenance (C := components n kappa pool proposer) hsync hmc hmono
          hsmsent hhon hsmmsg
      -- the tick's send, in full
      have hcontent := handler_vote_fin_content (voting_reading_mod Q τ) hsend
      rw [voting_reading_div Q τ, hsmmsg] at hcontent
      -- match the fin-vote against the send shape
      injection hcontent with he hsrc htgt hslot
      by_cases hmode : (processProposals (components n kappa pool proposer)
          x5[k][sm.sender].view τ x5[k][sm.sender].st).gjFrozen.c = τ - 1
      · -- fresh mode: the target's chain is the tick's `chAva` output
        rw [if_pos hmode] at htgt
        have hJch : J.ch = voteChAva x5 k sm.sender (Q.slotLength * τ + Q.delta) := by
          rw [htgt]
          unfold voteChAva
          rw [voting_reading_div Q τ]
        rw [hJch]
        exact hchAva k sm.sender (Q.slotLength * τ + Q.delta)
          (lt_of_lt_of_le hkj hji) hlblk (voting_reading_mod Q τ)
      · -- stale mode: the target's chain is its source's; descend at the voter
        rw [if_neg hmode] at htgt
        have hCsrc : C = (processProposals (components n kappa pool proposer)
            x5[k][sm.sender].view τ x5[k][sm.sender].st).gjFrozen := hsrc
        have hJch : J.ch = C.ch := by
          rw [htgt, hCsrc]
        have hCjust : JustifiedIn n x5[k][sm.sender].view C := by
          rw [hCsrc]
          exact processProposals_gjFrozen_justified (gjFrozen_justified k sm.sender)
        rw [hJch]
        exact IH C.c (hJc ▸ hlink.1) C rfl k sm.sender
          (le_of_lt (lt_of_lt_of_le hkj hji)) hCjust

/-! ### One step of Algorithm 5's available chain — condition 2.3/2.4's case analysis -/

/-- The proposal fold never writes `chAva`. -/
theorem processProposals_chAva (C : Components Node (Chain Tx) (QCert Node Tx))
    (V : View Node M) (t : Nat) (s : NodeState Node (Chain Tx) (QCert Node Tx)) :
    (processProposals C V t s).chAva = s.chAva := by
  unfold processProposals
  generalize V.toList = l
  induction l generalizing s with
  | nil => rfl
  | cons a l ih =>
      rw [List.foldl_cons, ih]
      cases hm : a.msg with
      | vote ch src tgt t' => rfl
      | propose chp chC qc gjp t' =>
          dsimp only
          simp only [apply_ite NodeState.chAva, ite_self]

/-- **One step of `chAva`**: unchanged, or the owner's vote tick with the joining check
    open writes the `chAva` fold (`voteChAva`), or the owner's fast-confirm tick adopts
    a longer fast confirmation. -/
theorem chAva_step5 {x5 : Exec Pr5 S} {m : Nat} {p : Node} :
    x5[m + 1][p].st.chAva = x5[m][p].st.chAva ∨
    (∃ ti : Nat, x5.lbl m = .tick p (Q.slotLength * ti + Q.delta) ∧
      x5[m][p].st.activeAt ≤ Q.slotLength * ti + Q.delta ∧
      x5[m + 1][p].st.chAva = voteChAva x5 m p (Q.slotLength * ti + Q.delta)) ∨
    (∃ ti : Nat, x5.lbl m = .tick p (Q.slotLength * ti + 2 * Q.delta) ∧
      ¬ chainLe ((components n kappa pool proposer).fastConfirm x5[m][p].view ti).1
          x5[m][p].st.chAva ∧
      x5[m + 1][p].st.chAva
        = ((components n kappa pool proposer).fastConfirm x5[m][p].view ti).1) := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  have h5 : x5[m + 1] = _ := exec5_succ (x5 := x5) m
  cases h : x5.lbl m with
  | advance t =>
      refine Or.inl ?_
      rw [h5, h]
      rfl
  | tick q t =>
      by_cases hq : p = q
      · subst hq
        have hget : x5[m + 1][p].st
            = (handlerCore (components n kappa pool proposer) Q (pick5 x5 m p t) p t
              x5[m][p].view x5[m][p].st).state := by
          rw [h5, h]
          simp only [applyNodeStepResult_getElem, setClock_getElem, if_pos rfl,
            if_true]
          rfl
        by_cases hph1 : t % Q.slotLength = Q.delta
        · -- the vote phase
          have htr : t = Q.slotLength * (t / Q.slotLength) + Q.delta := by
            conv_lhs => rw [← Nat.div_add_mod t Q.slotLength]
            rw [hph1]
          by_cases hgate : x5[m][p].st.activeAt ≤ t
          · refine Or.inr (Or.inl ⟨t / Q.slotLength, congrArg (Action.tick p) htr,
              by rw [← htr]; exact hgate, ?_⟩)
            rw [hget]
            simp only [handlerCore, apply_ite NodeStepResult.state]
            rw [if_neg (by omega), if_pos hph1, if_pos hgate]
            unfold voteChAva
            rw [← htr]
          · refine Or.inl ?_
            rw [hget]
            simp only [handlerCore, apply_ite NodeStepResult.state]
            rw [if_neg (by omega), if_pos hph1, if_neg hgate]
            exact processProposals_chAva _ _ _ _
        · by_cases hph2 : t % Q.slotLength = 2 * Q.delta
          · -- the fast-confirm phase
            have htr : t = Q.slotLength * (t / Q.slotLength) + 2 * Q.delta := by
              conv_lhs => rw [← Nat.div_add_mod t Q.slotLength]
              rw [hph2]
            by_cases hg : chainLe
                ((components n kappa pool proposer).fastConfirm x5[m][p].view
                  (t / Q.slotLength)).1 x5[m][p].st.chAva
            · refine Or.inl ?_
              rw [hget]
              simp only [handlerCore, apply_ite NodeStepResult.state]
              rw [if_neg (by omega), if_neg (by omega), if_pos hph2]
              dsimp only
              rw [components_prefixLe, if_pos hg]
            · refine Or.inr (Or.inr ⟨t / Q.slotLength, congrArg (Action.tick p) htr, hg, ?_⟩)
              rw [hget]
              simp only [handlerCore, apply_ite NodeStepResult.state]
              rw [if_neg (by omega), if_neg (by omega), if_pos hph2]
              dsimp only
              rw [components_prefixLe, if_neg hg]
          · -- quiet phases: propose, merge, idle
            refine Or.inl ?_
            rw [hget]
            simp only [handlerCore, apply_ite NodeStepResult.state]
            by_cases hph0 : t % Q.slotLength = 0
            · rw [if_pos hph0]
              split_ifs <;> rfl
            · rw [if_neg hph0, if_neg hph1, if_neg hph2]
              split_ifs <;> rfl
      · refine Or.inl ?_
        rw [h5, h]
        simp only [applyNodeStepResult_getElem, setClock_getElem, if_true,
          if_neg (fun hh => hq (Eq.symm hh))]
        rfl
  | deliver q msg =>
      refine Or.inl ?_
      rw [h5, h]
      by_cases hq : p = q
      · subst hq
        simp only [applyNodeStepResult_getElem, receive_getElem, if_pos rfl, if_true]
        rfl
      · simp only [applyNodeStepResult_getElem, receive_getElem,
          if_neg (fun hh => hq (Eq.symm hh))]
        rfl
  | wake q =>
      refine Or.inl ?_
      rw [h5, h]
      by_cases hq : p = q
      · subst hq
        simp only [applyNodeStepResult_getElem, if_pos rfl, if_true]
        rfl
      · simp only [applyNodeStepResult_getElem, if_neg (fun hh => hq (Eq.symm hh))]
        rfl
  | custom q ev => exact ev.elim
  | adversarial q msg =>
      refine Or.inl ?_
      rw [h5, h]
      rfl

/-- A guarded-max fold lands on its seed or a list element. -/
theorem foldl_maxCh_mem {C : Components Node (Chain Tx) (QCert Node Tx)}
    {Mb : Chain Tx} (l : List (Chain Tx)) (init : Chain Tx) :
    l.foldl (fun acc ch => if C.prefixLe ch Mb then C.maxCh acc ch else acc) init = init ∨
    l.foldl (fun acc ch => if C.prefixLe ch Mb then C.maxCh acc ch else acc) init ∈ l := by
  induction l generalizing init with
  | nil => exact Or.inl rfl
  | cons a l ih =>
      rw [List.foldl_cons]
      have hstep : (if C.prefixLe a Mb then C.maxCh init a else init) = init ∨
          (if C.prefixLe a Mb then C.maxCh init a else init) = a := by
        split_ifs
        · unfold Components.maxCh
          split_ifs
          · exact Or.inr rfl
          · exact Or.inl rfl
        · exact Or.inl rfl
      rcases ih (if C.prefixLe a Mb then C.maxCh init a else init) with h | h
      · rw [h]
        rcases hstep with hs | hs
        · exact Or.inl hs
        · refine Or.inr ?_
          rw [hs]
          exact List.mem_cons_self
      · exact Or.inr (List.mem_cons_of_mem a h)

/-- **The vote-tick `chAva` output is one of its three candidates**: the previous
    `chAva`, the κ-deep prefix of this tick's fork choice, or the frozen
    greatest-justified chain — condition 2.3's case split. -/
theorem voteChAva_cases (x5 : Exec Pr5 S) (k : Nat) (w : Node) (t : Time) :
    voteChAva x5 k w t
        = (processProposals (components n kappa pool proposer)
            x5[k][w].view (t / Q.slotLength) x5[k][w].st).chAva ∨
    voteChAva x5 k w t
        = (components n kappa pool proposer).kappaPrefix (t / Q.slotLength)
          ((components n kappa pool proposer).mfc
            (processProposals (components n kappa pool proposer)
              x5[k][w].view (t / Q.slotLength) x5[k][w].st).vFrozen
            x5[k][w].view
            (processProposals (components n kappa pool proposer)
              x5[k][w].view (t / Q.slotLength) x5[k][w].st).chFrozen
            (t / Q.slotLength)) ∨
    voteChAva x5 k w t
        = (processProposals (components n kappa pool proposer)
            x5[k][w].view (t / Q.slotLength) x5[k][w].st).gjFrozen.ch := by
  have h := foldl_maxCh_mem (C := components n kappa pool proposer)
    (Mb := (components n kappa pool proposer).mfc
      (processProposals (components n kappa pool proposer)
        x5[k][w].view (t / Q.slotLength) x5[k][w].st).vFrozen
      x5[k][w].view
      (processProposals (components n kappa pool proposer)
        x5[k][w].view (t / Q.slotLength) x5[k][w].st).chFrozen
      (t / Q.slotLength))
    [(processProposals (components n kappa pool proposer)
        x5[k][w].view (t / Q.slotLength) x5[k][w].st).chAva,
      (components n kappa pool proposer).kappaPrefix (t / Q.slotLength)
        ((components n kappa pool proposer).mfc
          (processProposals (components n kappa pool proposer)
            x5[k][w].view (t / Q.slotLength) x5[k][w].st).vFrozen
          x5[k][w].view
          (processProposals (components n kappa pool proposer)
            x5[k][w].view (t / Q.slotLength) x5[k][w].st).chFrozen
          (t / Q.slotLength)),
      (processProposals (components n kappa pool proposer)
        x5[k][w].view (t / Q.slotLength) x5[k][w].st).gjFrozen.ch]
    (processProposals (components n kappa pool proposer)
      x5[k][w].view (t / Q.slotLength) x5[k][w].st).chAva
  rcases h with h | h
  · exact Or.inl h
  · rcases List.mem_cons.mp h with h1 | h1
    · exact Or.inl h1
    · rcases List.mem_cons.mp h1 with h2 | h2
      · exact Or.inr (Or.inl h2)
      · rcases List.mem_cons.mp h2 with h3 | h3
        · exact Or.inr (Or.inr h3)
        · cases h3

/-- The vote skeleton is monotone in the view. -/
theorem voteSkel_mono {Va Vb : View Node M} (hsub : Va ⊆ Vb) :
    voteSkel Va ⊆ voteSkel Vb := by
  intro tr htr
  obtain ⟨q, c, s⟩ := tr
  obtain ⟨sm, hsm, h1, h2, h3⟩ := mem_voteSkel.mp htr
  refine mem_voteSkel.mpr ⟨sm, ?_, h1, h2, h3⟩
  unfold votes at hsm ⊢
  exact Finset.mem_filter.mpr ⟨hsub (Finset.mem_filter.mp hsm).1,
    (Finset.mem_filter.mp hsm).2⟩


/-- **Algorithm 5's processed frozen chain, traced**: the merge seed survives, or a
    checked slot-`t` proposal's fast-confirmed chain replaced it, or a
    justification-checked proposal checkpoint's chain did — condition 2.2's base
    provenance on the Algorithm-5 side. -/
theorem processProposals_chFrozen (V : View Node M) (t : Nat)
    (s : NodeState Node (Chain Tx) (QCert Node Tx)) :
    (processProposals (components n kappa pool proposer) V t s).chFrozen
        = s.chFrozen ∨
    (∃ sm ∈ V, (∃ chp qc ck, sm.msg = .propose chp
        ((processProposals (components n kappa pool proposer) V t s).chFrozen)
        qc ck t) ∧
      ValidProposal5 n proposer V sm) ∨
    (∃ c : Nat, JustifiedIn n V
      ⟨(processProposals (components n kappa pool proposer) V t s).chFrozen, c⟩) := by
  unfold processProposals
  have hV : ∀ a ∈ V.toList, a ∈ V := fun a ha => Finset.mem_toList.mp ha
  revert hV
  generalize V.toList = l
  intro hV
  induction l generalizing s with
  | nil => exact Or.inl rfl
  | cons a l ih =>
      rw [List.foldl_cons]
      rcases ih (fun b hb => hV b (List.mem_cons_of_mem a hb)) (s := _)
        with h | h | h
      · rw [h]
        obtain ⟨asd, amsg⟩ := a
        cases amsg with
        | vote ch src tgt t' => exact Or.inl rfl
        | propose chp chC qc gjp t' =>
            dsimp only
            -- split the guarded checkpoint block first: its condition is `ite`-free
            by_cases hg : t' = t ∧
                (components n kappa pool proposer).validProposal V
                  ⟨asd, .propose chp chC qc gjp t'⟩ ∧
                (components n kappa pool proposer).justified gjp V = true ∧
                s.gjFrozen.c ≤ gjp.c
            · rw [if_pos hg]
              split_ifs with h1 h2 h3
              · exact Or.inr (Or.inl ⟨⟨asd, .propose chp chC qc gjp t'⟩,
                  hV _ List.mem_cons_self, ⟨chp, qc, gjp, by rw [hg.1]⟩, hg.2.1⟩)
              · exact Or.inl rfl
              · exact Or.inr (Or.inl ⟨⟨asd, .propose chp chC qc gjp t'⟩,
                  hV _ List.mem_cons_self, ⟨chp, qc, gjp, by rw [hg.1]⟩, hg.2.1⟩)
              · exact Or.inr (Or.inr ⟨gjp.c,
                  show JustifiedIn n V gjp from of_decide_eq_true hg.2.2.1⟩)
            · rw [if_neg hg]
              split_ifs with h1
              · exact Or.inr (Or.inl ⟨⟨asd, .propose chp chC qc gjp t'⟩,
                  hV _ List.mem_cons_self, ⟨chp, qc, gjp, by rw [h1.1]⟩, h1.2.1⟩)
              · exact Or.inl rfl
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)

/-- A tick does not move the original run's time. -/
theorem tick_time5 {x5 : Exec Pr5 S} {k : Nat} {p : Node} {t : Time}
    (hlbl : x5.lbl k = .tick p t) : x5[k + 1].time = x5[k].time := by
  rw [show x5[k + 1] = _ from exec5_succ (x5 := x5) k, hlbl]
  rfl

/-- Under synchronized clocks, a tick's reading is the real time it happens at —
    Algorithm 5's side. -/
theorem tick_reading5 {x5 : Exec Pr5 S} (hsync : SynchronizedClocks x5)
    {k : Nat} {p : Node} {t : Time} (hlbl : x5.lbl k = .tick p t) :
    x5[k].time = t := by
  have hclock : x5[k + 1][p].clock = t := by
    rw [show x5[k + 1] = _ from exec5_succ (x5 := x5) k, hlbl]
    simp [applyNodeStepResult_getElem, setClock_getElem]
  have hstep := x5.step k
  rw [hlbl] at hstep
  have hawk : x5.Awake (k + 1) p := by
    show p ∈ S.awake ((x5[k + 1].time : Int))
    rw [tick_time5 hlbl]
    have h1 := hstep.1
    simp only [spec] at h1
    exact h1
  have hs := hsync (k + 1) p hawk
  rw [hclock] at hs
  rw [← tick_time5 hlbl, ← hs]

/-! ### Definition 9, rendered -/

/-- The honest-proposal window, on the Algorithm-5 side — `HonestProposalWindow`'s
    shape over the original run's log; the table transfers it to the simulated run. -/
def HonestProposalWindow5 (x5 : Exec Pr5 S) : Prop :=
  ∀ t : Nat, kappa ≤ t → ∃ tp, 1 ≤ tp ∧ t - kappa ≤ tp ∧ tp < t ∧
    ∃ (i : Nat) (vp : Node) (chp chC : Chain Tx) (qc : Option (QCert Node Tx))
      (ck : Checkpoint (Chain Tx)),
      (⟨vp, Msg.propose chp chC qc ck tp⟩ : SignedMsg Node M) ∈ x5[i].sent ∧
      vp ∉ S.adv ((x5[i].time : Int)) ∧ vp ∉ S.adv (Q.voting (tp : Int))

/-- **Definition 9** (`Definition 9, arXiv:2601.03862v1 p.18`): an Algorithm-5 and an
    Algorithm-2 run over one schedule are **MFC-equivalent** when they take the same
    non-delivery steps and, at every shared tick:
    * (condition 1, the paper's 2.7 rephrasing) the two log deltas — the handlers'
      sends, at most singletons — pair up under dynamic equivalence;
    * (2.1) at propose readings the two fork choices agree;
    * (2.2) at vote readings the two processed fork choices agree;
    * (2.3/2.4, strengthened to the state level) at *every* step, Algorithm 5's
      available chain is dominated by some Algorithm-2 confirmed chain of no later a
      time — the paper samples this at the vote and fast-confirm readings; the state
      form implies both samples and never less. -/
def MfcEquivalent (x5 : Exec Pr5 S) (x2 : Exec Pr2 S) : Prop :=
  (∀ k p t, x5.lbl k = .tick p t ↔ x2.lbl k = .tick p t) ∧
  (∀ k p t, x5.lbl k = .tick p t →
    (∀ sm5 ∈ x5[k + 1].sent - x5[k].sent, ∃ sm2 ∈ x2[k + 1].sent - x2[k].sent,
      SDynEq sm5 sm2) ∧
    (∀ sm2 ∈ x2[k + 1].sent - x2[k].sent, ∃ sm5 ∈ x5[k + 1].sent - x5[k].sent,
      SDynEq sm5 sm2)) ∧
  (∀ k p t, x5.lbl k = .tick p t → t % Q.slotLength = 0 →
    (components n kappa pool proposer).mfc x5[k][p].view x5[k][p].view
        ((components n kappa pool proposer).fastConfirm x5[k][p].view
          (t / Q.slotLength - 1)).1 (t / Q.slotLength)
      = mfc x2[k][p].view x2[k][p].view
        (fastConfirmSimple n x2[k][p].view (t / Q.slotLength - 1)).1
        (t / Q.slotLength)) ∧
  (∀ k p t, x5.lbl k = .tick p t → t % Q.slotLength = Q.delta →
    x5[k][p].st.activeAt ≤ t →
    (components n kappa pool proposer).mfc
        (processProposals (components n kappa pool proposer)
          x5[k][p].view (t / Q.slotLength) x5[k][p].st).vFrozen
        x5[k][p].view
        (processProposals (components n kappa pool proposer)
          x5[k][p].view (t / Q.slotLength) x5[k][p].st).chFrozen
        (t / Q.slotLength)
      = mfc
        (processProposals2 n proposer
          x2[k][p].view (t / Q.slotLength) x2[k][p].st).vFrozen
        x2[k][p].view
        (processProposals2 n proposer
          x2[k][p].view (t / Q.slotLength) x2[k][p].st).chFrozen
        (t / Q.slotLength)) ∧
  (∀ (k : Nat) (p : Node), ∃ (a : Nat) (w : Node), x2[a].time ≤ x5[k].time ∧
    chainLe x5[k][p].st.chAva x2[a][w].st.chi)

/-- **Lemma 10's statement** (`Lemma 10, arXiv:2601.03862v1 p.18`): every compliant
    Algorithm-5 run has an MFC-equivalent compliant Algorithm-2 run. Unproved — the
    grand induction over `simulate x5` is stage C2's remaining proof; parked
    (user decision, 2026-08-05) until the transfers validate this statement. -/
def Lemma10Statement (Q : Params) (S : Schedule Node) (n kappa : Nat)
    (pool : Nat → Tx) (proposer : Nat → Node) : Prop :=
  ∀ x5 : Exec Pr5 S, SettingGA Q S x5 →
    Fintype.card Node ≤ n → 3 * Q.f < n → 1 ≤ kappa →
    HonestProposalWindow5 x5 →
    ∃ x2 : Exec Pr2 S, SettingGA Q S x2 ∧ MfcEquivalent x5 x2

/-! ### The transfers: Lemmas 11–13 consume `MfcEquivalent` -/

/-- `ActiveVotesExtend2`, on the Algorithm-5 side: every slot-`t` active's vote at the
    voting reading extends `ch`. -/
def ActiveVotesExtend5 (x5 : Exec Pr5 S) (t : Nat) (ch : Chain Tx) : Prop :=
  ∀ p ∈ Active Q S (t : Int),
    ∃ (i : Nat) (e : Chain Tx) (src tgt : Checkpoint (Chain Tx)),
    x5[i].time = Q.slotLength * t + Q.delta ∧
    ⟪vote, e, src, tgt, t, p⟫ ∈ x5[i].sent ∧
    chainLe ch e

/-- Membership in a multiset difference is membership. -/
theorem mem_of_mem_sub {α : Type} [DecidableEq α] {a b : Multiset α} {m : α}
    (h : m ∈ a - b) : m ∈ a := by
  rw [← Multiset.count_pos] at h ⊢
  rw [Multiset.count_sub] at h
  omega

/-- **The active votes transfer, Algorithm 5 → Algorithm 2**: an active's vote in the
    original run has, at its own emitting tick, a dynamically equivalent counterpart in
    the equivalent run — same signer, same chain, same slot. -/
theorem activeVotesExtend_transfer {x5 : Exec Pr5 S} {x2 : Exec Pr2 S}
    (heq : MfcEquivalent x5 x2)
    (hsync5 : SynchronizedClocks x5) (hmc : S.MonotoneCorruption)
    (hmono5 : TimeMonotone x5) (hah : S.AwakeHonest)
    (hsync2 : SynchronizedClocks x2)
    {t : Nat} {ch : Chain Tx} (h : ActiveVotesExtend5 x5 t ch) :
    ActiveVotesExtend2 x2 t ch := by
  intro p hp
  obtain ⟨i, e, src, tgt, htime, hmem, hle⟩ := h p hp
  have hδ := Q.deltaPos
  -- the vote's sender is awake at its reading, hence honest there
  have hhon : (⟪vote, e, src, tgt, t, p⟫ :
      SignedMsg Node M).sender ∉ S.adv ((x5[i].time : Int)) := by
    show p ∉ S.adv ((x5[i].time : Int))
    rw [htime]
    have hawk : p ∈ S.awake ((Q.slotLength * t + Q.delta : Nat) : Int) := by
      refine mem_awakeThroughout.mp hp _ ?_ ?_ <;>
        · show _
          unfold Params.voting
          push_cast
          omega
    exact Finset.disjoint_left.mp (hah _) hawk
  obtain ⟨k, hki, hlblk, htimek, -, hem, -, -, -⟩ :=
    vote_provenance (C := components n kappa pool proposer) hsync5 hmc hmono5
      hmem hhon rfl
  -- the emitting tick's delta pairs with the equivalent run's
  obtain ⟨sm2, hsm2, hsde⟩ := (heq.2.1 k p _ hlblk).1 _ hem
  obtain ⟨hsender, hde⟩ := hsde
  rcases hmsg2 : sm2.msg with ⟨chp', chC', qc', ck', t'⟩ | ⟨e2, src2, tgt2, t2⟩ <;>
    rw [hmsg2] at hde
  · cases hde
  · obtain ⟨hee, htt⟩ := hde
    -- the equivalent run's tick happens at the same reading and time
    have hlbl2 : x2.lbl k = .tick p (Q.slotLength * t + Q.delta) :=
      (heq.1 k p _).mp hlblk
    have htime2 : x2[k + 1].time = Q.slotLength * t + Q.delta := by
      rw [tick_time hlbl2]
      exact tick_reading hsync2 hlbl2
    refine ⟨k + 1, e2, src2, tgt2, htime2, ?_, ?_⟩
    · have : sm2 = ⟪vote, e2, src2, tgt2, t, p⟫ := by
        cases sm2 with
        | mk sd mg =>
            simp only at hsender hmsg2
            rw [← hsender, hmsg2, ← htt]
      rw [← this]
      exact mem_of_mem_sub hsm2
    · rw [← hee]
      exact hle

/-- **The active votes transfer, Algorithm 2 → Algorithm 5** — the converse direction,
    through the same tick's delta pairing. -/
theorem activeVotesExtend_transfer' {x5 : Exec Pr5 S} {x2 : Exec Pr2 S}
    (heq : MfcEquivalent x5 x2)
    (hsync2 : SynchronizedClocks x2) (hmc : S.MonotoneCorruption)
    (hmono2 : TimeMonotone x2) (hah : S.AwakeHonest)
    (hsync5 : SynchronizedClocks x5)
    {t : Nat} {ch : Chain Tx} (h : ActiveVotesExtend2 x2 t ch) :
    ActiveVotesExtend5 x5 t ch := by
  intro p hp
  obtain ⟨i, e, src, tgt, htime, hmem, hle⟩ := h p hp
  have hδ := Q.deltaPos
  have hhon : (⟪vote, e, src, tgt, t, p⟫ :
      SignedMsg Node M).sender ∉ S.adv ((x2[i].time : Int)) := by
    show p ∉ S.adv ((x2[i].time : Int))
    rw [htime]
    have hawk : p ∈ S.awake ((Q.slotLength * t + Q.delta : Nat) : Int) := by
      refine mem_awakeThroughout.mp hp _ ?_ ?_ <;>
        · show _
          unfold Params.voting
          push_cast
          omega
    exact Finset.disjoint_left.mp (hah _) hawk
  obtain ⟨k, hki, hlblk, htimek, -, hem⟩ :=
    vote_provenance2 hsync2 hmc hmono2 hmem hhon rfl
  have hlbl5 : x5.lbl k = .tick p (Q.slotLength * t + Q.delta) :=
    (heq.1 k p _).mpr hlblk
  obtain ⟨sm5, hsm5, hsde⟩ := (heq.2.1 k p _ hlbl5).2 _ hem
  obtain ⟨hsender, hde⟩ := hsde
  rcases hmsg5 : sm5.msg with ⟨chp', chC', qc', ck', t'⟩ | ⟨e5, src5, tgt5, t5⟩ <;>
    rw [hmsg5] at hde
  · cases hde
  · obtain ⟨hee, htt⟩ := hde
    have htime5 : x5[k + 1].time = Q.slotLength * t + Q.delta := by
      have h5 : x5[k + 1] = _ := exec5_succ (x5 := x5) k
      -- p's clock after the tick reads the reading
      have hclock : x5[k + 1][p].clock = Q.slotLength * t + Q.delta := by
        rw [h5, hlbl5]
        simp [applyNodeStepResult_getElem, setClock_getElem]
      -- p stays awake through the tick: time does not move
      have ht5 : x5[k + 1].time = x5[k].time := by
        rw [h5, hlbl5]
        rfl
      have hstep := x5.step k
      rw [hlbl5] at hstep
      have hawk : x5.Awake (k + 1) p := by
        show p ∈ S.awake ((x5[k + 1].time : Int))
        rw [ht5]
        have h1 := hstep.1
        simp only [spec] at h1
        exact h1
      have hs := hsync5 (k + 1) p hawk
      rw [hclock] at hs
      exact hs.symm
    refine ⟨k + 1, e5, src5, tgt5, htime5, ?_, ?_⟩
    · have : sm5 = ⟪vote, e5, src5, tgt5, t, p⟫ := by
        cases sm5 with
        | mk sd mg =>
            simp only at hsender hmsg5
            rw [hsender, hmsg5, htt]
      rw [← this]
      exact mem_of_mem_sub hsm5
    · rw [hee]
      exact hle

/-- **Lemma 11's votes half** (`Lemma 11, arXiv:2601.03862v1 p.20`): if every slot-`t`
    active votes an extension of `ch` in the Algorithm-5 run, so does every
    slot-`t+1` active — across the equivalence and back, through Lemma 2 on the
    Algorithm-2 side. The quorum threshold is the structural validator count, as in
    every paper-facing statement. -/
theorem lemma11_votes (hn : n = Fintype.card Node)
    {x5 : Exec Pr5 S} {x2 : Exec Pr2 S}
    (heq : MfcEquivalent x5 x2) (H5 : SettingGA Q S x5) (H2 : SettingGA Q S x2)
    {t : Nat} (ht : 1 ≤ t) {ch : Chain Tx}
    (h : ActiveVotesExtend5 x5 t ch) :
    ActiveVotesExtend5 x5 (t + 1) ch := by
  subst hn
  exact activeVotesExtend_transfer' heq H2.wellformed.2.2.1 H2.wellformed.1
    H2.wellformed.2.2.2.1 H2.wellformed.2.1 H5.wellformed.2.2.1
    (Analysis2.lemma2 H2 ht
      (activeVotesExtend_transfer heq H5.wellformed.2.2.1 H5.wellformed.1
        H5.wellformed.2.2.2.1 H5.wellformed.2.1 H2.wellformed.2.2.1 h))

/-- `activeAt_le_voting`, on the Algorithm-5 side: a validator awake through the
    activity window has its joining check open at the voting reading. -/
theorem activeAt_le_voting5 {x5 : Exec Pr5 S} (hsync : SynchronizedClocks x5)
    (hmono : TimeMonotone x5) {p : Node} {t1 : Nat}
    (hwin : ∀ r : Int, ((Q.slotLength * t1 + Q.delta : Nat) : Int) - 3 * Q.delta ≤ r →
      r ≤ ((Q.slotLength * t1 + Q.delta : Nat) : Int) → p ∈ S.awake r)
    {j : Nat} (hj : x5[j].time ≤ Q.slotLength * t1 + Q.delta) :
    x5[j][p].st.activeAt ≤ Q.slotLength * t1 + Q.delta := by
  induction j with
  | zero =>
      have h0 := x5.init.2.1 p
      show ((x5.cfg 0)[p]).st.activeAt ≤ Q.slotLength * t1 + Q.delta
      rw [h0]
      exact Nat.zero_le _
  | succ m ih =>
      have hm' : x5[m].time ≤ Q.slotLength * t1 + Q.delta :=
        le_trans (time_le_of_le hmono (Nat.le_succ m)) hj
      have hA := ih hm'
      have hstep : Step Pr5 S (x5.lbl m) x5[m] x5[m + 1] := x5.step m
      refine hstep.elimR (motive := fun _ c c' =>
          c[p].st.activeAt ≤ Q.slotLength * t1 + Q.delta →
          c.time ≤ Q.slotLength * t1 + Q.delta →
          (∀ q : Node, q ∈ S.awake ((c.time : Int)) → c[q].clock = c.time) →
          c'[p].st.activeAt ≤ Q.slotLength * t1 + Q.delta)
        ?_ ?_ ?_ ?_ ?_ ?_ hA hm' (fun q hq => hsync m q hq)
      · intro d t h _ _
        exact h
      · intro d d' q t hen hns h _ _
        rw [nodeStep_iff_exists] at hns
        obtain ⟨res, hres, rfl⟩ := hns
        rw [protocol_step_tick] at hres
        obtain ⟨pk, -, rfl⟩ := mem_handler_iff.mp hres
        by_cases hq : q = p
        · subst hq
          simpa [applyNodeStepResult_getElem, handler_activeAt, setClock_getElem] using h
        · simpa [applyNodeStepResult_getElem, setClock_getElem, hq] using h
      · intro d d' q mm hen hns h _ _
        rw [nodeStep_iff_exists] at hns
        obtain ⟨res, hres, rfl⟩ := hns
        rw [protocol_step_recv] at hres
        subst hres
        by_cases hq : q = p
        · subst hq
          simpa [applyNodeStepResult_getElem, receive_getElem] using h
        · simpa [applyNodeStepResult_getElem, receive_getElem, hq] using h
      · intro d d' q hen hns h hm'' hclocks
        simp only [spec] at hen
        rw [nodeStep_iff_exists] at hns
        obtain ⟨res, hres, rfl⟩ := hns
        rw [protocol_step_wake] at hres
        subst hres
        by_cases hq : q = p
        · subst hq
          have hlow : (d.time : Int) - 1 <
              ((Q.slotLength * t1 + Q.delta : Nat) : Int) - 3 * Q.delta := by
            by_contra hge
            refine hen.2 (hwin ((d.time : Int) - 1) (by omega) ?_)
            have hdt : (d.time : Int) ≤ ((Q.slotLength * t1 + Q.delta : Nat) : Int) := by
              exact_mod_cast hm''
            omega
          have hr : d.time + 3 * Q.delta ≤ Q.slotLength * t1 + Q.delta := by
            have h2 : (d.time : Int) + 3 * Q.delta ≤
                ((Q.slotLength * t1 + Q.delta : Nat) : Int) := by omega
            exact_mod_cast h2
          simpa [applyNodeStepResult_getElem, hclocks q hen.1] using
            activationRound_le_voting Q hr
        · simpa [applyNodeStepResult_getElem, hq] using h
      · intro d d' q ev hen hns
        exact ev.elim
      · intro d q mm hen h _ _
        exact h

set_option maxHeartbeats 1000000 in
/-- The two Algorithm-5 fork-choice bounds at slot `t+1`, from the equivalent run's
    slot-`t` votes — Lemma 11's engine, reused by Lemma 12 at every later slot. -/
theorem mfc_bounds_of_ave2 (hn : n = Fintype.card Node)
    {x5 : Exec Pr5 S} {x2 : Exec Pr2 S}
    (heq : MfcEquivalent x5 x2) (H5 : SettingGA Q S x5) (H2 : SettingGA Q S x2)
    {t : Nat} (ht : 1 ≤ t) {ch : Chain Tx}
    (hvotes2 : ActiveVotesExtend2 x2 t ch) :
    (∀ (k : Nat) (vi : Node), vi ∈ Active Q S ((t : Int) + 1) →
      x5.lbl k = .tick vi (Q.slotLength * (t + 1)) →
      chainLe ch ((components n kappa pool proposer).mfc
        x5[k][vi].view x5[k][vi].view
        ((components n kappa pool proposer).fastConfirm
          x5[k][vi].view t).1 (t + 1))) ∧
    (∀ (k : Nat) (vi : Node), vi ∈ Active Q S ((t : Int) + 1) →
      x5.lbl k = .tick vi (Q.slotLength * (t + 1) + Q.delta) →
      chainLe ch ((components n kappa pool proposer).mfc
        (processProposals (components n kappa pool proposer)
          x5[k][vi].view (t + 1) x5[k][vi].st).vFrozen
        x5[k][vi].view
        (processProposals (components n kappa pool proposer)
          x5[k][vi].view (t + 1) x5[k][vi].st).chFrozen
        (t + 1))) := by
  subst hn
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  have hSL0 : 0 < Q.slotLength := by omega
  have H2' := H2
  obtain ⟨⟨hmc2, hah2, hsync2, hmono2, hcs2, hdiv2, hdil2⟩, hstepw2, hwpt2, hone2,
    ⟨hsyn2, hrel2⟩, hslp, ⟨hcb, hfn⟩, hgst⟩ := H2'
  have hdivP : Q.slotLength * (t + 1) / Q.slotLength = t + 1 :=
    Nat.mul_div_cancel_left _ hSL0
  constructor
  · intro k vi hvi hlbl
    have h21 := heq.2.2.1 k vi _ hlbl (Nat.mul_mod_right _ _)
    rw [hdivP] at h21
    simp only [Nat.add_sub_cancel] at h21
    rw [h21]
    have hlbl2 := (heq.1 k vi _).mp hlbl
    have htb : x2[k].time = Q.slotLength * (t + 1) := tick_reading hsync2 hlbl2
    have hawk2 : x2.Awake k vi := by
      have hstep := x2.step k
      rw [hlbl2] at hstep
      have h1 := hstep.1
      simp only [spec] at h1
      exact h1
    have hbound := le_mfc_at_propose_of_ave hsync2 hstepw2 hdil2 hwpt2 hone2 hmc2
      hsyn2 hslp hcb hfn (le_refl _) hgst ht hvotes2 htb hawk2
    simpa using hbound
  · intro k vi hvi hlbl
    have hgate : x5[k][vi].st.activeAt ≤ Q.slotLength * (t + 1) + Q.delta := by
      refine activeAt_le_voting5 H5.wellformed.2.2.1 H5.wellformed.2.2.2.1
        (t1 := t + 1) ?_ ?_
      · intro r h1 h2
        refine mem_awakeThroughout.mp hvi r ?_ ?_ <;>
          · show _
            unfold Params.voting
            push_cast at h1 h2 ⊢
            omega
      · exact le_of_eq (tick_reading5 H5.wellformed.2.2.1 hlbl)
    have h22 := heq.2.2.2.1 k vi _ hlbl (voting_reading_mod Q (t + 1)) hgate
    rw [voting_reading_div Q (t + 1)] at h22
    rw [h22]
    have hlbl2 := (heq.1 k vi _).mp hlbl
    exact le_mfc_at_vote2 hsync2 hstepw2 hdil2 hwpt2 hone2 hmc2 hsyn2 hslp hcb hfn
      hgst ht hvotes2 hvi hlbl2

set_option maxHeartbeats 1000000 in
/-- **Lemma 11** (`Lemma 11, arXiv:2601.03862v1 p.20`, the analogue of Lemma 2, for
    Algorithm 5): if every slot-`t` active votes an extension of `ch`, then at every
    slot-`t+1` active's propose and vote ticks the fork choice extends `ch`, and every
    slot-`t+1` active votes an extension of `ch`. Proof: transfer the votes to the
    MFC-equivalent Algorithm-2 run, run Lemma 2's engines there
    (`le_mfc_at_propose_of_ave`, `le_mfc_at_vote2`), and carry the fork-choice bounds
    back through conditions 2.1 and 2.2. -/
theorem lemma11 (hn : n = Fintype.card Node)
    {x5 : Exec Pr5 S} {x2 : Exec Pr2 S}
    (heq : MfcEquivalent x5 x2) (H5 : SettingGA Q S x5) (H2 : SettingGA Q S x2)
    {t : Nat} (ht : 1 ≤ t) {ch : Chain Tx}
    (h : ActiveVotesExtend5 x5 t ch) :
    (∀ (k : Nat) (vi : Node), vi ∈ Active Q S ((t : Int) + 1) →
      x5.lbl k = .tick vi (Q.slotLength * (t + 1)) →
      chainLe ch ((components n kappa pool proposer).mfc
        x5[k][vi].view x5[k][vi].view
        ((components n kappa pool proposer).fastConfirm x5[k][vi].view t).1
        (t + 1))) ∧
    (∀ (k : Nat) (vi : Node), vi ∈ Active Q S ((t : Int) + 1) →
      x5.lbl k = .tick vi (Q.slotLength * (t + 1) + Q.delta) →
      chainLe ch ((components n kappa pool proposer).mfc
        (processProposals (components n kappa pool proposer)
          x5[k][vi].view (t + 1) x5[k][vi].st).vFrozen
        x5[k][vi].view
        (processProposals (components n kappa pool proposer)
          x5[k][vi].view (t + 1) x5[k][vi].st).chFrozen
        (t + 1))) ∧
    ActiveVotesExtend5 x5 (t + 1) ch := by
  subst hn
  have hvotes2 : ActiveVotesExtend2 x2 t ch :=
    activeVotesExtend_transfer heq H5.wellformed.2.2.1 H5.wellformed.1
      H5.wellformed.2.2.2.1 H5.wellformed.2.1 H2.wellformed.2.2.1 h
  obtain ⟨hP, hV⟩ := mfc_bounds_of_ave2 rfl heq H5 H2 ht hvotes2
  exact ⟨hP, hV, lemma11_votes rfl heq H5 H2 ht h⟩

/-- **An honest Algorithm-5 proposal pins its emitting tick**: reading `propose(t)`,
    with the emission in that step's log delta — `vote_provenance`'s propose twin,
    trimmed to what the transfers need. -/
theorem propose_provenance5 {x5 : Exec Pr5 S}
    (hsync : SynchronizedClocks x5) (hmc : S.MonotoneCorruption)
    (hmono : TimeMonotone x5) {i : Nat}
    {sm : SignedMsg Node M} {chp chC : Chain Tx} {qc : Option (QCert Node Tx)}
    {ck : Checkpoint (Chain Tx)} {t : Nat}
    (hmem : sm ∈ x5[i].sent) (hhon : sm.sender ∉ S.adv ((x5[i].time : Int)))
    (hmsg : sm.msg = .propose chp chC qc ck t) :
    ∃ k, k < i ∧ x5.lbl k = .tick sm.sender (Q.slotLength * t) ∧
      sm ∈ x5[k + 1].sent - x5[k].sent := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  obtain ⟨k, hki, hem⟩ := emitted_of_mem_sent hmem
  have hhonk : sm.sender ∉ S.adv ((x5[k].time : Int)) := fun hadv =>
    hhon (hmc _ _ (by exact_mod_cast time_le_of_le hmono (Nat.le_of_lt hki)) hadv)
  rcases emitted_step hem with ⟨tk, hlbl, -, -, -, pk, -, hsend⟩ | hadv
  · obtain ⟨-, hshape⟩ := mem_handler_send hsend
    have htk : tk = Q.slotLength * t := by
      rcases hshape with ⟨chp', chC', qc', gj', heq', hmod⟩ | ⟨ch', src', tgt', heq', -⟩
      · rw [hmsg] at heq'
        injection heq' with _ _ _ _ hslot
        have hdm := Nat.div_add_mod tk Q.slotLength
        rw [← hslot] at hdm
        omega
      · rw [hmsg] at heq'
        cases heq'
    subst htk
    exact ⟨k, hki, hlbl, hem⟩
  · exact absurd hadv hhonk


set_option maxHeartbeats 1000000 in
/-- **Lemma 12** (`Lemma 12, arXiv:2601.03862v1 p.20`, the analogue of Lemma 4, for
    Algorithm 5): an honest proposer's slot-`t` proposal is voted for — every later
    slot's actives vote extensions of `chp`, and from `t+1` on both fork choices
    extend it. Proof: the proposal crosses to the equivalent run at its emitting tick
    (`propose_provenance5` + condition 1 — dynamic equivalence preserves the proposed
    chain and slot), Lemma 4 runs there, and the votes and fork-choice bounds come
    back through the transfers and conditions 2.1/2.2. -/
theorem lemma12 (hn : n = Fintype.card Node)
    {x5 : Exec Pr5 S} {x2 : Exec Pr2 S}
    (heq : MfcEquivalent x5 x2) (H5 : SettingGA Q S x5) (H2 : SettingGA Q S x2)
    {t : Nat} (ht : 1 ≤ t)
    {vp : Node} {chp chC : Chain Tx} {qc : Option (QCert Node Tx)}
    {ck : Checkpoint (Chain Tx)} {i : Nat}
    (hsent : (⟨vp, Msg.propose chp chC qc ck t⟩ : SignedMsg Node M) ∈ x5[i].sent)
    (hhon_i : vp ∉ S.adv ((x5[i].time : Int)))
    (hhon_t : vp ∉ S.adv (Q.voting (t : Int))) :
    (∀ t', t ≤ t' → ActiveVotesExtend5 x5 t' chp) ∧
    (∀ t₀, t ≤ t₀ →
      (∀ (k : Nat) (vi : Node), vi ∈ Active Q S ((t₀ : Int) + 1) →
        x5.lbl k = .tick vi (Q.slotLength * (t₀ + 1)) →
        chainLe chp ((components n kappa pool proposer).mfc
          x5[k][vi].view x5[k][vi].view
          ((components n kappa pool proposer).fastConfirm x5[k][vi].view t₀).1
          (t₀ + 1))) ∧
      (∀ (k : Nat) (vi : Node), vi ∈ Active Q S ((t₀ : Int) + 1) →
        x5.lbl k = .tick vi (Q.slotLength * (t₀ + 1) + Q.delta) →
        chainLe chp ((components n kappa pool proposer).mfc
          (processProposals (components n kappa pool proposer)
            x5[k][vi].view (t₀ + 1) x5[k][vi].st).vFrozen
          x5[k][vi].view
          (processProposals (components n kappa pool proposer)
            x5[k][vi].view (t₀ + 1) x5[k][vi].st).chFrozen
          (t₀ + 1)))) := by
  subst hn
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  -- the proposal's emitting tick, and its counterpart in the equivalent run
  obtain ⟨k, hki, hlbl, hem⟩ :=
    propose_provenance5 H5.wellformed.2.2.1 H5.wellformed.1 H5.wellformed.2.2.2.1
      hsent hhon_i rfl
  obtain ⟨sm2, hsm2, hsender, hde⟩ := (heq.2.1 k vp _ hlbl).1 _ hem
  rcases hmsg2 : sm2.msg with ⟨chp2, chC2, qc2, ck2, t2⟩ | ⟨e2, src2, tgt2, τ2⟩ <;>
    rw [hmsg2] at hde
  case vote => cases hde
  case propose =>
  obtain ⟨hchp, ht2⟩ := hde
  -- the counterpart, identified, is in the equivalent run's log
  have hsent2 : (⟨vp, Msg.propose chp chC2 qc2 ck2 t⟩ :
      SignedMsg Node M) ∈ x2[k + 1].sent := by
    have hid : sm2 = ⟨vp, Msg.propose chp chC2 qc2 ck2 t⟩ := by
      cases sm2 with
      | mk sd mg =>
          simp only at hsender hmsg2
          rw [← hsender, hmsg2, ← hchp, ← ht2]
    rw [← hid]
    exact mem_of_mem_sub hsm2
  -- honesty at the counterpart's index: its time is `propose(t) ≤ voting(t)`
  have hlbl2 := (heq.1 k vp _).mp hlbl
  have H2' := H2
  obtain ⟨⟨hmc2, hah2, hsync2, hmono2, -, -, -⟩, -, -, -, -, -, -, -⟩ := H2'
  have htime2 : x2[k + 1].time = Q.slotLength * t := by
    rw [tick_time hlbl2]
    exact tick_reading hsync2 hlbl2
  have hhon_i2 : vp ∉ S.adv ((x2[k + 1].time : Int)) := by
    intro had
    refine hhon_t (hmc2 _ _ ?_ had)
    rw [htime2]
    unfold Params.voting
    push_cast
    omega
  -- Lemma 4 on the equivalent run, at every later slot
  have hvotes2 : ∀ t', t ≤ t' → ActiveVotesExtend2 x2 t' chp :=
    fun t' ht' => Analysis2.lemma4 H2 ht hsent2 hhon_i2 hhon_t ht'
  refine ⟨?_, ?_⟩
  · intro t' ht'
    exact activeVotesExtend_transfer' heq H2.wellformed.2.2.1 H2.wellformed.1
      H2.wellformed.2.2.2.1 H2.wellformed.2.1 H5.wellformed.2.2.1 (hvotes2 t' ht')
  · intro t₀ ht₀
    exact mfc_bounds_of_ave2 rfl heq H5 H2 (le_trans ht ht₀) (hvotes2 t₀ ht₀)

set_option maxHeartbeats 1000000 in
/-- **Lemma 13** (`Lemma 13, arXiv:2601.03862v1 p.20`, the analogue of Lemma 5, for
    Algorithm 5): any honest validator's available chain is below any later active's
    fork choice, at both readings. Proof: the state-level dominance (conditions
    2.3/2.4) hands the chain to some Algorithm-2 confirmed chain of no later a time,
    Lemma 5's engine (`chi_le_mfc`) bounds that by the equivalent run's fork choice,
    and conditions 2.1/2.2 carry the bound back. -/
theorem lemma13 (hn : n = Fintype.card Node)
    {x5 : Exec Pr5 S} {x2 : Exec Pr2 S}
    (heq : MfcEquivalent x5 x2) (H5 : SettingGA Q S x5) (H2 : SettingGA Q S x2)
    (hκ : 1 ≤ kappa) (hwin2 : HonestProposalWindow x2)
    (a : Nat) (vi : Node) (k : Nat) (vj : Node) (s0 : Nat)
    (hv : vj ∈ Active Q S ((s0 : Int) + 1)) :
    (x5.lbl k = .tick vj (Q.slotLength * (s0 + 1)) →
      x5[a].time ≤ Q.slotLength * (s0 + 1) →
      chainLe x5[a][vi].st.chAva
        ((components n kappa pool proposer).mfc x5[k][vj].view x5[k][vj].view
          ((components n kappa pool proposer).fastConfirm x5[k][vj].view s0).1
          (s0 + 1))) ∧
    (x5.lbl k = .tick vj (Q.slotLength * (s0 + 1) + Q.delta) →
      x5[a].time ≤ Q.slotLength * (s0 + 1) + Q.delta →
      chainLe x5[a][vi].st.chAva
        ((components n kappa pool proposer).mfc
          (processProposals (components n kappa pool proposer)
            x5[k][vj].view (s0 + 1) x5[k][vj].st).vFrozen
          x5[k][vj].view
          (processProposals (components n kappa pool proposer)
            x5[k][vj].view (s0 + 1) x5[k][vj].st).chFrozen
          (s0 + 1))) := by
  subst hn
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  have hSL0 : 0 < Q.slotLength := by omega
  have hdivP : Q.slotLength * (s0 + 1) / Q.slotLength = s0 + 1 :=
    Nat.mul_div_cancel_left _ hSL0
  obtain ⟨a2, w2, hta2, hdom⟩ := heq.2.2.2.2 a vi
  have H2' := H2
  obtain ⟨⟨hmc2, hah2, hsync2, hmono2, hcs2, hdiv2, hdil2⟩, hstepw2, hwpt2, hone2,
    ⟨hsyn2, hrel2⟩, hslp, ⟨hcb, hfn⟩, hgst⟩ := H2'
  constructor
  · intro hlbl hta
    have h21 := heq.2.2.1 k vj _ hlbl (Nat.mul_mod_right _ _)
    rw [hdivP] at h21
    simp only [Nat.add_sub_cancel] at h21
    rw [h21]
    have hlbl2 := (heq.1 k vj _).mp hlbl
    have htb : x2[k].time = Q.slotLength * (s0 + 1) := tick_reading hsync2 hlbl2
    have hawk2 : x2.Awake k vj := by
      have hstep := x2.step k
      rw [hlbl2] at hstep
      have h1 := hstep.1
      simp only [spec] at h1
      exact h1
    have hchi := (chi_le_mfc hsync2 hstepw2 hdiv2 hdil2 hone2 hwpt2 hmc2 hsyn2 hrel2
      hslp hcb hfn (le_refl _) hgst hκ hwin2 a2 w2 k vj s0).1 hawk2 htb
      (le_trans hta2 hta)
    exact chainLe_trans hdom hchi
  · intro hlbl hta
    have hgate : x5[k][vj].st.activeAt ≤ Q.slotLength * (s0 + 1) + Q.delta := by
      refine activeAt_le_voting5 H5.wellformed.2.2.1 H5.wellformed.2.2.2.1
        (t1 := s0 + 1) ?_ ?_
      · intro r h1 h2
        refine mem_awakeThroughout.mp hv r ?_ ?_ <;>
          · show _
            unfold Params.voting
            push_cast at h1 h2 ⊢
            omega
      · exact le_of_eq (tick_reading5 H5.wellformed.2.2.1 hlbl)
    have h22 := heq.2.2.2.1 k vj _ hlbl (voting_reading_mod Q (s0 + 1)) hgate
    rw [voting_reading_div Q (s0 + 1)] at h22
    rw [h22]
    have hlbl2 := (heq.1 k vj _).mp hlbl
    have hchi := (chi_le_mfc hsync2 hstepw2 hdiv2 hdil2 hone2 hwpt2 hmc2 hsyn2 hrel2
      hslp hcb hfn (le_refl _) hgst hκ hwin2 a2 w2 k vj s0).2 hv hlbl2
      (le_trans hta2 hta)
    exact chainLe_trans hdom hchi

/-! ### The grand induction's raw pieces -/

/-- An active vote tick writes exactly the `chAva` fold. -/
theorem vote_tick_chAva {x5 : Exec Pr5 S} {k : Nat} {w : Node} {t : Time}
    (hlbl : x5.lbl k = .tick w t) (hmod : t % Q.slotLength = Q.delta)
    (hgate : x5[k][w].st.activeAt ≤ t) :
    x5[k + 1][w].st.chAva = voteChAva x5 k w t := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  have hget : x5[k + 1][w].st
      = (handlerCore (components n kappa pool proposer) Q (pick5 x5 k w t) w t
        x5[k][w].view x5[k][w].st).state := by
    rw [show x5[k + 1] = _ from exec5_succ (x5 := x5) k, hlbl]
    simp only [applyNodeStepResult_getElem, setClock_getElem, if_pos rfl, if_true]
    rfl
  rw [hget]
  simp only [handlerCore, apply_ite NodeStepResult.state]
  rw [if_neg (by omega), if_pos hmod, if_pos hgate]
  unfold voteChAva
  rfl

/-- **The justified-descent, landing on a vote tick**: a checkpoint justified in any
    view reachable by step `i` is genesis-chained, or its chain is below some *earlier
    active vote tick's* `chAva` fold output — the witness form condition 2.3's
    maintenance consumes (the `M2`-bounded form, `justified_le_of_chAva_le`, bounds by
    a fork-choice term; the dominance invariant needs the tick itself). Same descent:
    fresh-mode targets are the fold output, stale-mode targets equal their source,
    which is the voter's own justified `gjFrozen`, one checkpoint slot down. -/
theorem justified_to_voteChAva {x5 : Exec Pr5 S}
    (hsync : SynchronizedClocks x5) (hmc : S.MonotoneCorruption)
    (hmono : TimeMonotone x5)
    (hcb : S.CorruptionBounded Q.f) (hfn : 3 * Q.f < n)
    (hcard : Fintype.card Node ≤ n)
    {i : Nat} (cJ : Nat) :
    ∀ (J : Checkpoint (Chain Tx)), J.c = cJ →
    ∀ (j : Nat) (q : Node), j ≤ i →
      JustifiedIn n x5[j][q].view J →
      J.ch = [] ∨
      ∃ (k : Nat) (w : Node) (t : Time), k < i ∧ x5.lbl k = .tick w t ∧
        t % Q.slotLength = Q.delta ∧ x5[k][w].st.activeAt ≤ t ∧
        chainLe J.ch (voteChAva x5 k w t) := by
  induction cJ using Nat.strong_induction_on with
  | _ cJ IH =>
  intro J hJc j q hji hJ
  cases hJ with
  | genesis => exact Or.inl rfl
  | @link C _ hC hlink =>
      obtain ⟨w, hwA, hwhon⟩ := exists_honest_of_quorum (r := ((x5[j].time : Int)))
        hcb hfn hcard hlink.2.2
      obtain ⟨sm, hsmV, hsmw, e, τ, hsmmsg⟩ := mem_linkVoters hwA
      have hsmsent : sm ∈ x5[j].sent := views_sound x5 j q sm hsmV
      have hhon : sm.sender ∉ S.adv ((x5[j].time : Int)) := by
        rw [hsmw]
        exact hwhon
      obtain ⟨k, hkj, hlblk, htimek, hgate, -, pk, hpk, hsend⟩ :=
        vote_provenance (C := components n kappa pool proposer) hsync hmc hmono
          hsmsent hhon hsmmsg
      have hcontent := handler_vote_fin_content (voting_reading_mod Q τ) hsend
      rw [voting_reading_div Q τ, hsmmsg] at hcontent
      injection hcontent with he hsrc htgt hslot
      by_cases hmode : (processProposals (components n kappa pool proposer)
          x5[k][sm.sender].view τ x5[k][sm.sender].st).gjFrozen.c = τ - 1
      · rw [if_pos hmode] at htgt
        refine Or.inr ⟨k, sm.sender, Q.slotLength * τ + Q.delta,
          lt_of_lt_of_le hkj hji, hlblk, voting_reading_mod Q τ, hgate, ?_⟩
        have hJch : J.ch = voteChAva x5 k sm.sender (Q.slotLength * τ + Q.delta) := by
          rw [htgt]
          unfold voteChAva
          rw [voting_reading_div Q τ]
        rw [hJch]
        exact chainLe_refl _
      · rw [if_neg hmode] at htgt
        have hCsrc : C = (processProposals (components n kappa pool proposer)
            x5[k][sm.sender].view τ x5[k][sm.sender].st).gjFrozen := hsrc
        have hJch : J.ch = C.ch := by
          rw [htgt, hCsrc]
        have hCjust : JustifiedIn n x5[k][sm.sender].view C := by
          rw [hCsrc]
          exact processProposals_gjFrozen_justified (gjFrozen_justified k sm.sender)
        rw [hJch]
        exact IH C.c (hJc ▸ hlink.1) C rfl k sm.sender
          (le_of_lt (lt_of_lt_of_le hkj hji)) hCjust

/-! ### The frozen state at an active vote tick, on the Algorithm-5 side -/

/-- The merge tick freezes the fast confirmation. -/
theorem handler_merge_chFrozen {C : Components Node (Chain Tx) (QCert Node Tx)}
    {pick : Chain Tx} {p : Node} {r : Time} {V : View Node M}
    {s : NodeState Node (Chain Tx) (QCert Node Tx)}
    (hmod : r % Q.slotLength = 3 * Q.delta) :
    (handlerCore C Q pick p r V s).state.chFrozen
      = (C.fastConfirm V (r / Q.slotLength)).1 := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  simp only [handlerCore, apply_ite NodeStepResult.state]
  split_ifs <;> first | rfl | omega

/-- Off the vote and merge phases, the core keeps both frozen fields. -/
theorem handler_frozen_quiet {C : Components Node (Chain Tx) (QCert Node Tx)}
    {pick : Chain Tx} {p : Node} {r : Time} {V : View Node M}
    {s : NodeState Node (Chain Tx) (QCert Node Tx)}
    (h1 : r % Q.slotLength ≠ Q.delta) (h2 : r % Q.slotLength ≠ 3 * Q.delta) :
    (handlerCore C Q pick p r V s).state.vFrozen = s.vFrozen ∧
      (handlerCore C Q pick p r V s).state.chFrozen = s.chFrozen := by
  simp only [handlerCore, apply_ite NodeStepResult.state]
  split_ifs <;>
    first
      | exact ⟨rfl, rfl⟩
      | exact absurd ‹r % Q.slotLength = Q.delta› h1
      | exact absurd ‹r % Q.slotLength = 3 * Q.delta› h2

/-- Off `p`'s vote and merge ticks, one step keeps `p`'s frozen fields. -/
theorem frozen_step5 {x5 : Exec Pr5 S} {m : Nat} {p : Node}
    (hcond : ∀ tr : Time, x5.lbl m = .tick p tr →
      tr % Q.slotLength ≠ Q.delta ∧ tr % Q.slotLength ≠ 3 * Q.delta) :
    x5[m + 1][p].st.vFrozen = x5[m][p].st.vFrozen ∧
      x5[m + 1][p].st.chFrozen = x5[m][p].st.chFrozen := by
  have h5 : x5[m + 1] = _ := exec5_succ (x5 := x5) m
  cases h : x5.lbl m with
  | advance t =>
      rw [h5, h]
      exact ⟨rfl, rfl⟩
  | tick q t =>
      rw [h5, h]
      by_cases hq : p = q
      · subst hq
        have hph := hcond t h
        have hfr := handler_frozen_quiet (C := components n kappa pool proposer)
          (Q := Q) (pick := pick5 x5 m p t) (p := p) (r := t)
          (V := x5[m][p].view) (s := x5[m][p].st) hph.1 hph.2
        constructor
        · simp only [applyNodeStepResult_getElem, setClock_getElem, if_pos rfl,
            if_true]
          exact hfr.1
        · simp only [applyNodeStepResult_getElem, setClock_getElem, if_pos rfl,
            if_true]
          exact hfr.2
      · constructor <;>
          · simp only [applyNodeStepResult_getElem, setClock_getElem, if_true,
              if_neg (fun hh => hq (Eq.symm hh))]
            rfl
  | deliver q msg =>
      rw [h5, h]
      by_cases hq : p = q
      · subst hq
        constructor <;>
          · simp only [applyNodeStepResult_getElem, receive_getElem, if_pos rfl,
              if_true]
            rfl
      · constructor <;>
          · simp only [applyNodeStepResult_getElem, receive_getElem,
              if_neg (fun hh => hq (Eq.symm hh))]
            rfl
  | wake q =>
      rw [h5, h]
      by_cases hq : p = q
      · subst hq
        constructor <;>
          · simp only [applyNodeStepResult_getElem, if_pos rfl, if_true]
            rfl
      · constructor <;>
          · simp only [applyNodeStepResult_getElem,
              if_neg (fun hh => hq (Eq.symm hh))]
            rfl
  | custom q ev => exact ev.elim
  | adversarial q msg =>
      rw [h5, h]
      exact ⟨rfl, rfl⟩

/-- **The frozen state at an active vote tick, traced to its merge** — Algorithm 5's
    `frozen_at_vote_tick`: the merge tick at `4Δt+3Δ` exists inside the activity
    window and froze that moment's view and fast confirmation; no reading in between
    can rewrite them. -/
theorem frozen_at_vote_tick5 {x5 : Exec Pr5 S}
    (hsync : SynchronizedClocks x5) (hstepw : TimeStepwise x5) (hdil : Diligent x5)
    (hone : OneTickPerReading x5)
    {t : Nat} {p : Node} (hp : p ∈ Active Q S ((t : Int) + 1))
    {j : Nat} (hj : x5.lbl j = .tick p (Q.slotLength * (t + 1) + Q.delta)) :
    ∃ im, im < j ∧ x5[im].time = Q.slotLength * t + 3 * Q.delta ∧
      x5.lbl im = .tick p (Q.slotLength * t + 3 * Q.delta) ∧
      x5[j][p].st.vFrozen = x5[im][p].view ∧
      x5[j][p].st.chFrozen
        = ((components n kappa pool proposer).fastConfirm x5[im][p].view t).1 := by
  have hmono := hstepw.timeMonotone
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  have htj : x5[j].time = Q.slotLength * (t + 1) + Q.delta := tick_reading5 hsync hj
  have hexp : Q.slotLength * (t + 1) = Q.slotLength * t + Q.slotLength := Nat.mul_succ ..
  have hvot1 : Q.voting ((t : Int) + 1)
      = ((Q.slotLength * (t + 1) + Q.delta : Nat) : Int) := by
    unfold Params.voting
    push_cast
    omega
  have hawake : ∀ r : Time, Q.slotLength * t + 2 * Q.delta ≤ r →
      r ≤ Q.slotLength * (t + 1) + Q.delta → p ∈ S.awake ((r : Int)) := by
    intro r h1 h2
    refine mem_awakeThroughout.mp hp _ ?_ ?_ <;> rw [hvot1] <;> omega
  have hmt : Q.slotLength * t + 3 * Q.delta ≤ x5[j].time := by
    rw [htj]
    omega
  obtain ⟨i₀, hi₀j, hti₀⟩ := exists_time_eq hstepw hmt
  have hAw0 : x5.Awake i₀ p := by
    show p ∈ S.awake ((x5[i₀].time : Int))
    rw [hti₀]
    exact hawake _ (by omega) (by omega)
  obtain ⟨im, htim, hlblm⟩ := hdil (Q.slotLength * t + 3 * Q.delta) p ⟨i₀, hti₀, hAw0⟩
  have himj : im < j := by
    rcases Nat.lt_or_ge im j with h | h
    · exact h
    · exfalso
      have := time_le_of_le hmono h
      rw [htj, htim] at this
      omega
  have hmstate : x5[im + 1][p].st.vFrozen = x5[im][p].view ∧
      x5[im + 1][p].st.chFrozen
        = ((components n kappa pool proposer).fastConfirm x5[im][p].view t).1 := by
    have hget : x5[im + 1][p].st
        = (handlerCore (components n kappa pool proposer) Q
          (pick5 x5 im p (Q.slotLength * t + 3 * Q.delta)) p
          (Q.slotLength * t + 3 * Q.delta)
          x5[im][p].view x5[im][p].st).state := by
      rw [show x5[im + 1] = _ from exec5_succ (x5 := x5) im, hlblm]
      simp only [applyNodeStepResult_getElem, setClock_getElem, if_pos rfl, if_true]
      rfl
    rw [hget, handler_merge_vFrozen (merge_reading_mod Q t),
      handler_merge_chFrozen (merge_reading_mod Q t), merge_reading_div Q t]
    exact ⟨rfl, rfl⟩
  have hpers : ∀ m, im + 1 ≤ m → m ≤ j →
      x5[m][p].st.vFrozen = x5[im + 1][p].st.vFrozen ∧
        x5[m][p].st.chFrozen = x5[im + 1][p].st.chFrozen := by
    intro m
    induction m with
    | zero => omega
    | succ m ih =>
        intro h1 h2
        rcases Nat.eq_or_lt_of_le h1 with heq | hlt
        · rw [← heq]
          exact ⟨rfl, rfl⟩
        · have hprev := ih (by omega) (by omega)
          have hcond : ∀ tr : Time, x5.lbl m = .tick p tr →
              tr % Q.slotLength ≠ Q.delta ∧ tr % Q.slotLength ≠ 3 * Q.delta := by
            intro tr hltr
            have htr : x5[m].time = tr := tick_reading5 hsync hltr
            have hlo2 : Q.slotLength * t + 3 * Q.delta ≤ tr := by
              rw [← htr]
              calc Q.slotLength * t + 3 * Q.delta = x5[im].time := htim.symm
                _ ≤ x5[m].time := time_le_of_le hmono (by omega)
            have hhi2 : tr ≤ Q.slotLength * (t + 1) + Q.delta := by
              rw [← htr, ← htj]
              exact time_le_of_le hmono (by omega)
            have hpin := phase_pins_reading Q hlo2 hhi2
            constructor
            · intro hphase
              rw [hpin.2 hphase] at hltr
              have := hone m j p _ hltr hj
              omega
            · intro hphase
              rw [hpin.1 hphase] at hltr
              have := hone m im p _ hltr hlblm
              omega
          have hstep := frozen_step5 hcond
          exact ⟨hstep.1.trans hprev.1, hstep.2.trans hprev.2⟩
  have hsj := hpers j (by omega) (le_refl j)
  rw [hmstate.1, hmstate.2] at hsj
  exact ⟨im, himj, htim, hlblm, hsj.1, hsj.2⟩

/-! ### The prefix-guarded fold is a maximum, under comparability -/

/-- **A `⪯`-guarded fold dominates every value comparable with its whole run**: the
    accumulator only grows, so at the position of any value the scan's accumulator is
    below the final one; if the value tops the final accumulator, comparability makes
    the guard fire there — contradiction. Stated over an abstract write-step
    `step acc v = if acc ⪯ v then v else acc` shape via the hypothesis that each fold
    step either keeps the accumulator or moves to something above it, and fires
    whenever the guard holds. -/
theorem chainLe_foldl_of_comparable {l : List (Chain Tx)}
    {seed : Chain Tx} {O : Chain Tx}
    (hseed : chainLe seed O) (hl : ∀ v ∈ l, chainLe v O)
    {v : Chain Tx} (hv : v ∈ l) :
    chainLe v (l.foldl (fun acc c => if chainLe acc c then c else acc) seed) := by
  -- the accumulator is monotone and stays under `O`
  have hmono : ∀ (l' : List (Chain Tx)) (a : Chain Tx),
      chainLe a (l'.foldl (fun acc c => if chainLe acc c then c else acc) a) := by
    intro l'
    induction l' with
    | nil => exact fun a => chainLe_refl a
    | cons c l' ih =>
        intro a
        rw [List.foldl_cons]
        by_cases h : chainLe a c
        · rw [if_pos h]
          exact chainLe_trans h (ih c)
        · rw [if_neg h]
          exact ih a
  -- main induction: once `v` is scanned, the accumulator is at or above it
  induction l generalizing seed with
  | nil => cases hv
  | cons c l ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hv with rfl | hvl
      · -- `v` is scanned now: the guard fires or the accumulator already tops it
        by_cases h : chainLe seed v
        · rw [if_pos h]
          exact hmono l v
        · rw [if_neg h]
          have hcomp := comparable_of_common_extension hseed (hl v hv)
          rcases hcomp with h' | h'
          · exact absurd h' h
          · exact chainLe_trans h' (hmono l seed)
      · by_cases h : chainLe seed c
        · rw [if_pos h]
          exact ih (hl c List.mem_cons_self)
            (fun d hd => hl d (List.mem_cons_of_mem c hd)) hvl
        · rw [if_neg h]
          exact ih hseed (fun d hd => hl d (List.mem_cons_of_mem c hd)) hvl

/-! ### Nothing is justified before the first voting round -/

/-- **Early views justify only genesis**: a supermajority link needs an honest
    fin-voter, an honest fin-vote's target slot is its voting slot, and voting starts
    at `Δ` — so by time `Δ` every link's target has checkpoint slot `0`, below which
    link validity cannot reach. -/
theorem justified_early {x5 : Exec Pr5 S}
    (hsync : SynchronizedClocks x5) (hmc : S.MonotoneCorruption)
    (hmono : TimeMonotone x5)
    (hcb : S.CorruptionBounded Q.f) (hfn : 3 * Q.f < n)
    (hcard : Fintype.card Node ≤ n)
    {j : Nat} (htime : x5[j].time ≤ Q.delta) {q : Node}
    {J : Checkpoint (Chain Tx)} (hJ : JustifiedIn n x5[j][q].view J) :
    J = ⟨[], 0⟩ := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  cases hJ with
  | genesis => rfl
  | @link C _ hC hlink =>
      exfalso
      obtain ⟨w, hwA, hwhon⟩ := exists_honest_of_quorum (r := ((x5[j].time : Int)))
        hcb hfn hcard hlink.2.2
      obtain ⟨sm, hsmV, hsmw, e, τ, hsmmsg⟩ := mem_linkVoters hwA
      have hsmsent : sm ∈ x5[j].sent := views_sound x5 j q sm hsmV
      have hhon : sm.sender ∉ S.adv ((x5[j].time : Int)) := by
        rw [hsmw]
        exact hwhon
      obtain ⟨k, hkj, hlblk, htimek, -, -, pk, hpk, hsend⟩ :=
        vote_provenance (C := components n kappa pool proposer) hsync hmc hmono
          hsmsent hhon hsmmsg
      -- the fin-vote's target slot is its voting slot; its tick's time bounds it
      have hcontent := handler_vote_fin_content (voting_reading_mod Q τ) hsend
      rw [voting_reading_div Q τ, hsmmsg] at hcontent
      injection hcontent with he hsrc htgt hslot
      -- the tick happened at `voting(τ) ≤ time j ≤ Δ`, so `τ = 0`
      have hτ0 : τ = 0 := by
        have h1 : Q.slotLength * τ + Q.delta = x5[k].time := htimek.symm
        have h2 : x5[k].time ≤ x5[j].time := time_le_of_le hmono (le_of_lt hkj)
        have h3 : Q.slotLength * τ = 0 := by omega
        rcases Nat.mul_eq_zero.mp h3 with h | h
        · omega
        · exact h
      -- but then the target's checkpoint slot is `0`, and the link descends below it
      have hJc : J.c = 0 := by
        subst hτ0
        by_cases hmode : (processProposals (components n kappa pool proposer)
            x5[k][sm.sender].view 0 x5[k][sm.sender].st).gjFrozen.c = 0 - 1
        · rw [if_pos hmode] at htgt
          rw [htgt]
        · rw [if_neg hmode] at htgt
          rw [htgt]
      have := hlink.1
      omega

set_option maxHeartbeats 1000000 in
/-- **Condition 2.1, discharged at a tick**: the propose-round fork choices agree,
    from the table invariant (skeleton equality), the dominance invariant, and the
    justified descent — at slot `0` by vacuity (`justified_early`), later through
    `chi_le_mfc`'s propose conjunct at the merely-awake proposer. -/
theorem agree_propose_at_tick (hn : n = Fintype.card Node)
    {x5 : Exec Pr5 S} (H5 : SettingGA Q S x5) (H2 : SettingGA Q S (simulate x5))
    (hκ : 1 ≤ kappa) (hwin2 : HonestProposalWindow (simulate x5))
    {k : Nat} (hTD : TableDynEq x5 k)
    (hD : ∀ (j : Nat), j ≤ k → ∀ (q : Node), ∃ (a : Nat) (w : Node),
      (simulate x5)[a].time ≤ x5[j].time ∧
      chainLe x5[j][q].st.chAva ((simulate x5)[a][w].st.chi))
    {p : Node} {t : Time} (hlbl : x5.lbl k = .tick p t)
    (hmod : t % Q.slotLength = 0) :
    (components n kappa pool proposer).mfc x5[k][p].view x5[k][p].view
        ((components n kappa pool proposer).fastConfirm x5[k][p].view
          (t / Q.slotLength - 1)).1 (t / Q.slotLength)
      = mfc (simulate x5)[k][p].view (simulate x5)[k][p].view
        (fastConfirmSimple n (simulate x5)[k][p].view (t / Q.slotLength - 1)).1
        (t / Q.slotLength) := by
  subst hn
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  have hSL0 : 0 < Q.slotLength := by omega
  obtain ⟨⟨hmc5, hah5, hsync5, hmono5, -, -, -⟩, -, -, hone5, -, -, ⟨hcb5, hfn5⟩, -⟩ :=
    H5
  have H2' := H2
  obtain ⟨⟨hmc2, hah2, hsync2, hmono2, hcs2, hdiv2, hdil2⟩, hstepw2, hwpt2, hone2,
    ⟨hsyn2, hrel2⟩, hslp, ⟨hcb, hfn⟩, hgst⟩ := H2'
  -- the two views correspond, so the skeletons agree
  have hskel : voteSkel x5[k][p].view = voteSkel ((simulate x5)[k][p].view) :=
    voteSkel_eq_of_corr (viewCorr_of_tableDynEq hone5 hmc5 hah5 hmono5 hTD p)
  -- the 2.5 bound on the greatest justified chain
  have h25 : chainLe (gj (Fintype.card Node) x5[k][p].view).ch
      (mfc ((simulate x5)[k][p].view) ((simulate x5)[k][p].view)
        (fastConfirmSimple (Fintype.card Node) ((simulate x5)[k][p].view)
          (t / Q.slotLength - 1)).1 (t / Q.slotLength)) := by
    by_cases hs0 : t / Q.slotLength = 0
    · -- slot 0: nothing but genesis is justified this early
      have ht0 : t = 0 := by
        have h := Nat.div_add_mod t Q.slotLength
        rw [hs0, hmod] at h
        omega
      have htime : x5[k].time ≤ Q.delta := by
        rw [tick_reading5 hsync5 hlbl, ht0]
        omega
      have hgen := justified_early hsync5 hmc5 hmono5 hcb5 hfn5 (le_refl _) htime
        (gj_justified (Fintype.card Node) x5[k][p].view)
      rw [hgen]
      exact chainLe_nil _
    · -- later slots: descend to an earlier vote tick, ride the dominance, bound by
      -- Lemma 5's engine
      obtain ⟨s1, hs1⟩ : ∃ s1, t / Q.slotLength = s1 + 1 :=
        ⟨t / Q.slotLength - 1,
          (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hs0)).symm⟩
      rcases justified_to_voteChAva hsync5 hmc5 hmono5 hcb5 hfn5 (le_refl _)
          (i := k) (gj (Fintype.card Node) x5[k][p].view).c _ rfl k p (le_refl k)
          (gj_justified (Fintype.card Node) x5[k][p].view) with hnil | hdesc
      · rw [hnil]
        exact chainLe_nil _
      · obtain ⟨k', w, t', hk'k, hlbl', hmod', hgate', hle⟩ := hdesc
        rw [← vote_tick_chAva hlbl' hmod' hgate'] at hle
        obtain ⟨a, w2, hta, hdom⟩ := hD (k' + 1) (by omega) w
        have hbound : chainLe (gj (Fintype.card Node) x5[k][p].view).ch
            ((simulate x5)[a][w2].st.chi) := chainLe_trans hle hdom
        -- the tick transfers; its enabledness gives awakeness in the simulated run
        have hlbl2 : (simulate x5).lbl k = .tick p t := simLbl_tick_iff.mpr hlbl
        have hawk2 : (simulate x5).Awake k p := by
          have hstep := (simulate x5).step k
          rw [hlbl2] at hstep
          have h1 := hstep.1
          simp only [spec] at h1
          exact h1
        have h4 : t = Q.slotLength * (s1 + 1) := by
          have h := Nat.div_add_mod t Q.slotLength
          rw [hs1, hmod] at h
          omega
        have htb : (simulate x5)[k].time = Q.slotLength * (s1 + 1) := by
          rw [simulate_time, tick_reading5 hsync5 hlbl, h4]
        have hab : (simulate x5)[a].time ≤ Q.slotLength * (s1 + 1) := by
          refine le_trans hta ?_
          have h1 : x5[k' + 1].time = x5[k'].time := tick_time5 hlbl'
          have h2 : x5[k'].time ≤ x5[k].time :=
            time_le_of_le hmono5 (le_of_lt hk'k)
          have h3 : x5[k].time = t := tick_reading5 hsync5 hlbl
          omega
        have hchi := (chi_le_mfc hsync2 hstepw2 hdiv2 hdil2 hone2 hwpt2 hmc2 hsyn2
          hrel2 hslp hcb hfn (le_refl _) hgst hκ hwin2 a w2 k p s1).1 hawk2 htb hab
        rw [hs1]
        simp only [Nat.add_sub_cancel]
        exact chainLe_trans hbound hchi
  exact mfc_propose_agree hskel h25

/-- **Certificate validity crosses the correspondence**: the certified votes are
    identified by signer, chain and slot — exactly what dynamic equivalence preserves —
    and the fin-vote fields are existential in the check. Stated field-level, for the
    Algorithm-2 side message carrying the same chain, certificate and slot. -/
theorem validProposal2_of_cert {V5 V2 : View Node M}
    (hcorr : ViewCorr V5 V2) {sm2 : SignedMsg Node M}
    {chp chC : Chain Tx} {cert : QCert Node Tx} {ck2 : Checkpoint (Chain Tx)} {t' : Nat}
    (hmsg2 : sm2.msg = .propose chp chC (some cert) ck2 t')
    (hsender : sm2.sender = proposer t') (hpa : proposedAt chp = t')
    (hchCle : chainLe chC chp)
    (hcard : 2 * n ≤ 3 * (cert.image Prod.fst).card)
    (hvotes : ∀ e ∈ cert, chainLe chC e.2.1 ∧ e.2.2 = t' - 1 ∧
      ∃ src tgt : Checkpoint (Chain Tx),
        (⟨e.1, Msg.vote e.2.1 src tgt e.2.2⟩ : SignedMsg Node M) ∈ V5) :
    ValidProposal2 n proposer V2 sm2 := by
  unfold ValidProposal2
  rw [hmsg2]
  refine ⟨hsender, hpa, hchCle, Or.inr ⟨cert, rfl, hcard, ?_⟩⟩
  intro e he
  obtain ⟨h1, h2, src, tgt, hmem⟩ := hvotes e he
  refine ⟨h1, h2, ?_⟩
  obtain ⟨sm', hsm', hsde⟩ := hcorr.1 _ hmem
  obtain ⟨hsend', hde⟩ := hsde
  rcases hm' : sm'.msg with ⟨chp', chC', qc', ck', τ'⟩ | ⟨e', src', tgt', τ'⟩ <;>
    rw [hm'] at hde
  · cases hde
  · obtain ⟨hee, htt⟩ := hde
    refine ⟨src', tgt', ?_⟩
    have : sm' = ⟨e.1, Msg.vote e.2.1 src' tgt' e.2.2⟩ := by
      cases sm' with
      | mk sd mg =>
          simp only at hsend' hm'
          rw [← hsend', hm', ← hee, ← htt]
    rw [← this]
    exact hsm'

/-- **Every table entry is the identity or an honest emission's counterpart**: the
    table is written only at ticks, at their own sends. The identity branch is the
    pure-injection case — the same signed message exists verbatim in the simulated
    run. -/
theorem tau_id_or_emitted (x5 : Exec Pr5 S) (k : Nat) (sm : SignedMsg Node M) :
    (simState x5 k).2 sm = sm ∨
    ∃ k', k' < k ∧ ∃ t, x5.lbl k' = .tick sm.sender t ∧
      sm.msg ∈ (handlerCore (components n kappa pool proposer) Q
        (pick5 x5 k' sm.sender t) sm.sender t
        (setClock sm.sender t (x5.cfg k'))[sm.sender].view
        (setClock sm.sender t (x5.cfg k'))[sm.sender].st).send := by
  induction k with
  | zero => exact Or.inl rfl
  | succ k ih =>
      rcases tau_write x5 k sm with heq | ⟨p, t, hlbl, hsender, hsend⟩
      · rcases ih with h | ⟨k', hk', rest⟩
        · exact Or.inl (heq.trans h)
        · exact Or.inr ⟨k', by omega, rest⟩
      · refine Or.inr ⟨k, by omega, t, ?_, ?_⟩
        · rw [hsender]
          exact hlbl
        · rw [hsender]
          exact hsend

set_option maxHeartbeats 1000000 in
/-- **A justified chain sits below the simulated vote-round fork choice** — the
    composition three of 2.2's subcases share: descend to an earlier active vote
    tick, ride the dominance invariant to a simulated confirmed chain, and bound by
    Lemma 5's vote conjunct at the (Active) tick owner. -/
theorem justified_le_voteMfc (hn : n = Fintype.card Node)
    {x5 : Exec Pr5 S} (H5 : SettingGA Q S x5) (H2 : SettingGA Q S (simulate x5))
    (hκ : 1 ≤ kappa) (hwin2 : HonestProposalWindow (simulate x5))
    {k : Nat}
    (hD : ∀ (j : Nat), j ≤ k → ∀ (q : Node), ∃ (a : Nat) (w : Node),
      (simulate x5)[a].time ≤ x5[j].time ∧
      chainLe x5[j][q].st.chAva ((simulate x5)[a][w].st.chi))
    {p : Node} {s1 : Nat} (hlbl : x5.lbl k = .tick p (Q.slotLength * (s1 + 1) + Q.delta))
    (hact : p ∈ Active Q S ((s1 : Int) + 1))
    {j : Nat} (hjk : j ≤ k) {q : Node}
    {J : Checkpoint (Chain Tx)} (hJ : JustifiedIn n x5[j][q].view J) :
    chainLe J.ch
      (mfc (processProposals2 n proposer ((simulate x5)[k][p].view) (s1 + 1)
          ((simulate x5)[k][p].st)).vFrozen ((simulate x5)[k][p].view)
        (processProposals2 n proposer ((simulate x5)[k][p].view) (s1 + 1)
          ((simulate x5)[k][p].st)).chFrozen (s1 + 1)) := by
  subst hn
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  obtain ⟨⟨hmc5, hah5, hsync5, hmono5, -, -, -⟩, -, -, hone5, -, -, ⟨hcb5, hfn5⟩, -⟩ :=
    H5
  have H2' := H2
  obtain ⟨⟨hmc2, hah2, hsync2, hmono2, hcs2, hdiv2, hdil2⟩, hstepw2, hwpt2, hone2,
    ⟨hsyn2, hrel2⟩, hslp, ⟨hcb, hfn⟩, hgst⟩ := H2'
  rcases justified_to_voteChAva hsync5 hmc5 hmono5 hcb5 hfn5 (le_refl _)
      (i := k) J.c _ rfl j q hjk hJ with hnil | hdesc
  · rw [hnil]
    exact chainLe_nil _
  · obtain ⟨k', w, t', hk'k, hlbl', hmod', hgate', hle⟩ := hdesc
    rw [← vote_tick_chAva hlbl' hmod' hgate'] at hle
    obtain ⟨a, w2, hta, hdom⟩ := hD (k' + 1) (by omega) w
    have hbound : chainLe J.ch ((simulate x5)[a][w2].st.chi) := chainLe_trans hle hdom
    have hlbl2 : (simulate x5).lbl k
        = .tick p (Q.slotLength * (s1 + 1) + Q.delta) := simLbl_tick_iff.mpr hlbl
    have hab : (simulate x5)[a].time ≤ Q.slotLength * (s1 + 1) + Q.delta := by
      refine le_trans hta ?_
      have h1 : x5[k' + 1].time = x5[k'].time := tick_time5 hlbl'
      have h2 : x5[k'].time ≤ x5[k].time := time_le_of_le hmono5 (le_of_lt hk'k)
      have h3 : x5[k].time = Q.slotLength * (s1 + 1) + Q.delta :=
        tick_reading5 hsync5 hlbl
      omega
    have hchi := (chi_le_mfc hsync2 hstepw2 hdiv2 hdil2 hone2 hwpt2 hmc2 hsyn2
      hrel2 hslp hcb hfn (le_refl _) hgst hκ hwin2 a w2 k p s1).2 hact hlbl2 hab
    exact chainLe_trans hbound hchi

set_option maxHeartbeats 1000000 in
/-- **The frozen chain sits below the simulated vote-round fork choice** — `h_b5`'s
    seed case: the merge value is the simulated run's own seed (same merge tick, by
    `OneTickPerReading`; congruent fast confirmations), which rides the monotone
    Algorithm-2 fold under its own base — or the greatest-justified chain, which
    descends. -/
theorem chFrozen5_le_voteMfc (hn : n = Fintype.card Node)
    {x5 : Exec Pr5 S} (H5 : SettingGA Q S x5) (H2 : SettingGA Q S (simulate x5))
    (hκ : 1 ≤ kappa) (hwin2 : HonestProposalWindow (simulate x5))
    {k : Nat} (hTD : ∀ j, j ≤ k → TableDynEq x5 j)
    (hD : ∀ (j : Nat), j ≤ k → ∀ (q : Node), ∃ (a : Nat) (w : Node),
      (simulate x5)[a].time ≤ x5[j].time ∧
      chainLe x5[j][q].st.chAva ((simulate x5)[a][w].st.chi))
    {p : Node} {s1 : Nat}
    (hlbl : x5.lbl k = .tick p (Q.slotLength * (s1 + 1) + Q.delta))
    (hact : p ∈ Active Q S ((s1 : Int) + 1)) :
    chainLe (x5[k][p].st.chFrozen)
      (mfc (processProposals2 n proposer ((simulate x5)[k][p].view) (s1 + 1)
          ((simulate x5)[k][p].st)).vFrozen ((simulate x5)[k][p].view)
        (processProposals2 n proposer ((simulate x5)[k][p].view) (s1 + 1)
          ((simulate x5)[k][p].st)).chFrozen (s1 + 1)) := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  have H5' := H5
  obtain ⟨⟨hmc5, hah5, hsync5, hmono5, -, hdiv5, hdil5⟩, hstepw5, -, hone5, -, -,
    ⟨hcb5, hfn5⟩, -⟩ := H5'
  have H2' := H2
  obtain ⟨⟨hmc2, hah2, hsync2, hmono2, hcs2, hdiv2, hdil2⟩, hstepw2, hwpt2, hone2,
    ⟨hsyn2, hrel2⟩, hslp, ⟨hcb, hfn⟩, hgst⟩ := H2'
  obtain ⟨im, himk, htim, hlblm, -, hcf⟩ :=
    frozen_at_vote_tick5 hsync5 hstepw5 hdil5 hone5 hact hlbl
  rw [hcf]
  unfold Components.fastConfirm
  rw [components_fastConfirmSimple, components_gj, components_prefixLe]
  dsimp only
  by_cases hguard : chainLe (gj n x5[im][p].view).ch
      (fastConfirmSimple n x5[im][p].view s1).1
  · -- the quorum branch: the simulated run froze the congruent value
    rw [if_pos hguard]
    have hlbl2 : (simulate x5).lbl k
        = .tick p (Q.slotLength * (s1 + 1) + Q.delta) := simLbl_tick_iff.mpr hlbl
    obtain ⟨im2, him2k, htim2, hlblm2, -, hcf2⟩ :=
      frozen_at_vote_tick hsync2 hstepw2 hdil2 hone2 hact hlbl2
    have hlblm2' : x5.lbl im2 = .tick p (Q.slotLength * s1 + 3 * Q.delta) :=
      simLbl_tick_iff.mp hlblm2
    have him : im2 = im := hone5 im2 im p _ hlblm2' hlblm
    subst him
    have hskelm : voteSkel x5[im2][p].view = voteSkel ((simulate x5)[im2][p].view) :=
      voteSkel_eq_of_corr (viewCorr_of_tableDynEq hone5 hmc5 hah5 hmono5
        (hTD im2 (le_of_lt him2k)) p)
    have hfcs : fastConfirmSimple n x5[im2][p].view s1
        = fastConfirmSimple n ((simulate x5)[im2][p].view) s1 := by
      subst hn
      exact fastConfirmSimple_congr hskelm _ s1
    rw [hfcs, ← hcf2]
    exact chainLe_trans (processProposals2_chFrozen_mono _ _ _) (base_le_mfc _ _ _ _)
  · -- the greatest-justified branch: descend
    rw [if_neg hguard]
    have hj := gj_justified n x5[im][p].view
    exact justified_le_voteMfc hn H5 H2 hκ hwin2 hD hlbl hact (le_of_lt himk) hj

/-! ### Quorum support, from certificates and across growing views -/

/-- **A certificate's signers support its chain**, in any view holding the certified
    votes: the certificate names one vote per signer, extending `ch` at slot `t`, and
    those votes' senders are exactly the counted quorum. -/
theorem support_of_cert {V : View Node M} {ch : Chain Tx} {t : Nat}
    {cert : QCert Node Tx} (hcard : 2 * n ≤ 3 * (cert.image Prod.fst).card)
    (hvotes : ∀ e ∈ cert, chainLe ch e.2.1 ∧ e.2.2 = t ∧
      ∃ src tgt : Checkpoint (Chain Tx),
        (⟨e.1, Msg.vote e.2.1 src tgt e.2.2⟩ : SignedMsg Node M) ∈ V) :
    2 * n ≤ 3 * (((votes V).filter (fun sm => msgSlot sm.msg = t ∧
      chainLe ch (msgChain sm.msg))).image SignedMsg.sender).card := by
  have hsub : cert.image Prod.fst ⊆ ((votes V).filter (fun sm =>
      msgSlot sm.msg = t ∧ chainLe ch (msgChain sm.msg))).image SignedMsg.sender := by
    intro q hq
    obtain ⟨e, he, hqe⟩ := Finset.mem_image.mp hq
    obtain ⟨hle, hslot, src, tgt, hmem⟩ := hvotes e he
    refine Finset.mem_image.mpr ⟨⟨e.1, Msg.vote e.2.1 src tgt e.2.2⟩, ?_, hqe⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hmem, trivial⟩, ?_, ?_⟩
    · show e.2.2 = t
      exact hslot
    · show chainLe ch e.2.1 = true
      exact hle
  have := Finset.card_le_card hsub
  omega

/-- **Support only grows with the view**: the supporting votes of a smaller view are
    votes of the larger one. -/
theorem support_mono {V V' : View Node M} (hsub : V ⊆ V') {ch : Chain Tx} {t : Nat}
    (h : 2 * n ≤ 3 * (((votes V).filter (fun sm => msgSlot sm.msg = t ∧
      chainLe ch (msgChain sm.msg))).image SignedMsg.sender).card) :
    2 * n ≤ 3 * (((votes V').filter (fun sm => msgSlot sm.msg = t ∧
      chainLe ch (msgChain sm.msg))).image SignedMsg.sender).card := by
  have hs : ((votes V).filter (fun sm => msgSlot sm.msg = t ∧
        chainLe ch (msgChain sm.msg))) ⊆
      ((votes V').filter (fun sm => msgSlot sm.msg = t ∧
        chainLe ch (msgChain sm.msg))) := by
    intro sm hsm
    rw [Finset.mem_filter] at hsm ⊢
    refine ⟨?_, hsm.2⟩
    simp only [votes, Finset.mem_filter] at hsm ⊢
    exact ⟨hsub hsm.1.1, hsm.1.2⟩
  have := Finset.card_le_card (Finset.image_subset_image (f := SignedMsg.sender) hs)
  omega

set_option maxHeartbeats 1000000 in
/-- **Algorithm 2's processed frozen chain is genesis or quorum-supported**, seen from
    the voter's own view: the merge seed is `fastconfirmsimple`'s output (supported where
    it was computed, hence in the grown view), and every proposal write carries the
    certificate the Algorithm-2 validity check demands. -/
theorem frozen2_supported_or_nil {x : Exec Pr2 S}
    (hsync : SynchronizedClocks x) (hstepw : TimeStepwise x) (hdil : Diligent x)
    (hone : OneTickPerReading x)
    {k : Nat} {p : Node} {s1 : Nat}
    (hact : p ∈ Active Q S ((s1 : Int) + 1))
    (hlbl : x.lbl k = .tick p (Q.slotLength * (s1 + 1) + Q.delta)) :
    (processProposals2 n proposer (x[k][p].view) (s1 + 1) (x[k][p].st)).chFrozen = [] ∨
    2 * n ≤ 3 * (((votes (x[k][p].view)).filter (fun sm => msgSlot sm.msg = s1 ∧
      chainLe (processProposals2 n proposer (x[k][p].view) (s1 + 1)
        (x[k][p].st)).chFrozen (msgChain sm.msg))).image SignedMsg.sender).card := by
  rcases processProposals2_chFrozen (n := n) (proposer := proposer) (x[k][p].view)
    (s1 + 1) (x[k][p].st) with hseed | ⟨sm, hsmV, ⟨chp, qc, ck, hmsg⟩, hvalid⟩
  · -- the merge seed: `fastconfirmsimple` at the merge tick, in a smaller view
    obtain ⟨im, himk, -, -, -, hcf⟩ := frozen_at_vote_tick hsync hstepw hdil hone hact hlbl
    rw [hseed, hcf]
    rcases fastConfirmSimple_fst_cases (n := n) (x[im][p].view) s1 with h0 | hsupp
    · exact Or.inl h0
    · exact Or.inr (support_mono (view_mono_le (Pr' := Pr2) (le_of_lt himk) p) hsupp)
  · -- a proposal write: its certificate is the quorum
    obtain ⟨sd, m0⟩ := sm
    have hm0 : m0 = Msg.propose chp ((processProposals2 n proposer (x[k][p].view)
        (s1 + 1) (x[k][p].st)).chFrozen) qc ck (s1 + 1) := hmsg
    subst hm0
    have hvp : (⟨sd, Msg.propose chp ((processProposals2 n proposer (x[k][p].view)
          (s1 + 1) (x[k][p].st)).chFrozen) qc ck (s1 + 1)⟩ :
            SignedMsg Node M).sender = proposer (s1 + 1) ∧
        proposedAt chp = s1 + 1 ∧
        chainLe ((processProposals2 n proposer (x[k][p].view) (s1 + 1)
          (x[k][p].st)).chFrozen) chp ∧
        (((processProposals2 n proposer (x[k][p].view) (s1 + 1) (x[k][p].st)).chFrozen)
            = [] ∨
          ∃ cert : QCert Node Tx, qc = some cert ∧
            2 * n ≤ 3 * (cert.image Prod.fst).card ∧
            ∀ e ∈ cert, chainLe ((processProposals2 n proposer (x[k][p].view) (s1 + 1)
                (x[k][p].st)).chFrozen) e.2.1 ∧
              e.2.2 = s1 + 1 - 1 ∧
              ∃ src tgt : Checkpoint (Chain Tx),
                (⟨e.1, Msg.vote e.2.1 src tgt e.2.2⟩ : SignedMsg Node M)
                  ∈ x[k][p].view) := hvalid
    rcases hvp.2.2.2 with hnil | ⟨cert, -, hcard, hvotes⟩
    · exact Or.inl hnil
    · exact Or.inr (support_of_cert hcard (fun e he => by
        obtain ⟨h1, h2, h3⟩ := hvotes e he
        exact ⟨h1, by omega, h3⟩))

/-! ### The image of an honest emission is the simulated tick's own send -/

/-- What a tick's reaction sends enters the log, signed by the ticking validator. -/
theorem tick_send_mem5 {x5 : Exec Pr5 S} {k : Nat} {p : Node} {t : Time}
    (hlbl : x5.lbl k = .tick p t) {m : M}
    (hm : m ∈ (handlerCore (components n kappa pool proposer) Q (pick5 x5 k p t) p t
      (setClock p t (x5.cfg k))[p].view (setClock p t (x5.cfg k))[p].st).send) :
    (⟨p, m⟩ : SignedMsg Node M) ∈ x5[k + 1].sent := by
  rw [show x5[k + 1] = _ from exec5_succ_tick hlbl, applyNodeStepResult_sent]
  exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_map_of_mem _ hm))

/-- **The table's value at an emission is the simulated tick's send**: the write branch
    fires (the key is the ticking validator's own message), and the Algorithm-2 core does
    send — the two cores' sends are simultaneously empty or not (`sends_align`). -/
theorem tau_emitted_image {x5 : Exec Pr5 S}
    {k : Nat} {p : Node} {t : Time} (hlbl : x5.lbl k = .tick p t)
    {sm : SignedMsg Node M} (hsender : sm.sender = p)
    (hsend : sm.msg ∈ (handlerCore (components n kappa pool proposer) Q
      (pick5 x5 k p t) p t (setClock p t (x5.cfg k))[p].view
      (setClock p t (x5.cfg k))[p].st).send) :
    ∃ m2 ∈ (handler2Core Q n kappa pool proposer simBlank
        (simPick x5 k p t (setClock p t (simState x5 k).1)[p].view
          (setClock p t (simState x5 k).1)[p].st) p t
        (setClock p t (simState x5 k).1)[p].view
        (setClock p t (simState x5 k).1)[p].st).send,
      (simState x5 (k + 1)).2 sm = ⟨p, m2⟩ := by
  show ∃ m2 ∈ _, (simStep x5 k (simState x5 k)).2 sm = _
  simp only [simStep, hlbl]
  rw [if_pos ⟨hsender, hsend⟩]
  cases hso : sendOf (handler2Core Q n kappa pool proposer simBlank
      (simPick x5 k p t (setClock p t (simState x5 k).1)[p].view
        (setClock p t (simState x5 k).1)[p].st) p t
      (setClock p t (simState x5 k).1)[p].view
      (setClock p t (simState x5 k).1)[p].st) with
  | none =>
      exfalso
      have h2 : (handler2Core Q n kappa pool proposer simBlank
          (simPick x5 k p t (setClock p t (simState x5 k).1)[p].view
            (setClock p t (simState x5 k).1)[p].st) p t
          (setClock p t (simState x5 k).1)[p].view
          (setClock p t (simState x5 k).1)[p].st).send = 0 := by
        unfold sendOf at hso
        have hnil : (handler2Core Q n kappa pool proposer simBlank
            (simPick x5 k p t (setClock p t (simState x5 k).1)[p].view
              (setClock p t (simState x5 k).1)[p].st) p t
            (setClock p t (simState x5 k).1)[p].view
            (setClock p t (simState x5 k).1)[p].st).send.toList = [] := by
          cases hl : (handler2Core Q n kappa pool proposer simBlank
              (simPick x5 k p t (setClock p t (simState x5 k).1)[p].view
                (setClock p t (simState x5 k).1)[p].st) p t
              (setClock p t (simState x5 k).1)[p].view
              (setClock p t (simState x5 k).1)[p].st).send.toList with
          | nil => rfl
          | cons a l => rw [hl] at hso; simp at hso
        exact Multiset.toList_eq_nil.mp hnil
      have hact : (setClock p t (simState x5 k).1)[p].st.activeAt
          = (setClock p t (x5.cfg k))[p].st.activeAt := by
        simp only [setClock_getElem, if_pos rfl, if_true]
        exact sim_activeAt k p
      rcases sends_align (Q := Q) (n := n) (kappa := kappa) (pool := pool)
          (proposer := proposer)
          (pk5 := pick5 x5 k p t)
          (pk2 := simPick x5 k p t (setClock p t (simState x5 k).1)[p].view
            (setClock p t (simState x5 k).1)[p].st) p t hact with ⟨h5, -⟩ | ⟨-, hne⟩
      · rw [h5] at hsend
        exact absurd hsend (Multiset.notMem_zero _)
      · exact hne h2
  | some m2 => exact ⟨m2, sendOf_mem hso, rfl⟩

set_option maxHeartbeats 1000000 in
/-- **A certified proposal's counterpart carries the same certificate**: the origin
    dichotomy (`tau_id_or_emitted`) leaves two cases, and in both the simulated view
    holds a slot-`s` proposal with the *same* `chC` and certificate. A pure injection is
    its own image; an honest emission's image is the Algorithm-2 core's send at the same
    tick, whose `chC` and certificate are `fastconfirmsimple`'s — congruence-equal to
    Algorithm 5's, since a certificate rules out the `GJ` branch. -/
theorem cert_counterpart (hn : n = Fintype.card Node)
    {x5 : Exec Pr5 S} (H5 : SettingGA Q S x5)
    {k : Nat} (hTD : ∀ j, j ≤ k → TableDynEq x5 j)
    {p : Node} {sm5 : SignedMsg Node M} (hsm5 : sm5 ∈ x5[k][p].view)
    {chp chC : Chain Tx} {cert : QCert Node Tx} {ck : Checkpoint (Chain Tx)} {s : Nat}
    (hmsg5 : sm5.msg = .propose chp chC (some cert) ck s)
    (hpa : proposedAt chp = s) (hchp : chainLe chC chp) :
    ∃ sm2 ∈ (simulate x5)[k][p].view, ∃ chp2 ck2,
      sm2.sender = sm5.sender ∧ sm2.msg = .propose chp2 chC (some cert) ck2 s ∧
      proposedAt chp2 = s ∧ chainLe chC chp2 := by
  have H5' := H5
  obtain ⟨⟨hmc5, hah5, hsync5, hmono5, -, -, -⟩, -, -, hone5, -, -, -, -⟩ := H5'
  have hmem : (simState x5 k).2 sm5 ∈ (simState x5 k).1[p].view :=
    view_image hone5 hmc5 hah5 hmono5 k p hsm5
  rcases tau_id_or_emitted x5 k sm5 with hid | ⟨k', hk'k, t', hlbl', hsend'⟩
  · -- a pure injection: its own image
    rw [hid] at hmem
    exact ⟨sm5, hmem, chp, ck, rfl, hmsg5, hpa, hchp⟩
  · -- an honest emission: the simulated tick's own send
    have hshape := (mem_handler_send hsend').2
    have hmod : t' % Q.slotLength = 0 := by
      rcases hshape with ⟨-, -, -, -, -, hmod⟩ | ⟨ch', src', tgt', hvote⟩
      · exact hmod
      · exact absurd (hmsg5.symm.trans hvote.1) (by simp)
    obtain ⟨-, -, hm5⟩ := handler_propose_send hmod hsend'
    -- the emitted fields, read off the core's send
    rw [hmsg5] at hm5
    simp only [setClock_getElem, if_pos rfl, if_true] at hm5
    injection hm5 with hchp5 hchC5 hqc5 hgj5 hslot5
    -- a certificate rules out the `GJ` branch, so the merge is `fastconfirmsimple`
    have hqc5' : ((components n kappa pool proposer).fastConfirm
        (x5.cfg k')[sm5.sender].view (t' / Q.slotLength - 1)).2 = some cert := hqc5.symm
    have hfc : (components n kappa pool proposer).fastConfirm (x5.cfg k')[sm5.sender].view
          (t' / Q.slotLength - 1)
        = fastConfirmSimple n (x5.cfg k')[sm5.sender].view (t' / Q.slotLength - 1) := by
      unfold Components.fastConfirm at hqc5' ⊢
      rw [components_fastConfirmSimple, components_gj, components_prefixLe] at hqc5' ⊢
      dsimp only at hqc5' ⊢
      by_cases hg : chainLe (gj n (x5.cfg k')[sm5.sender].view).ch
          (fastConfirmSimple n (x5.cfg k')[sm5.sender].view (t' / Q.slotLength - 1)).1
      · rw [if_pos hg]
      · exfalso
        rw [if_neg hg] at hqc5'
        exact absurd hqc5' (by simp)
    rw [hfc] at hchC5 hqc5 hchp5
    -- the simulated tick's send: the same `fastconfirmsimple`, by the skeleton congruence
    have hskel : voteSkel (x5.cfg k')[sm5.sender].view
        = voteSkel ((simState x5 k').1[sm5.sender].view) :=
      voteSkel_eq_of_corr (viewCorr_of_tableDynEq hone5 hmc5 hah5 hmono5
        (hTD k' (le_of_lt hk'k)) sm5.sender)
    have hfcs2 : fastConfirmSimple n (x5.cfg k')[sm5.sender].view (t' / Q.slotLength - 1)
        = fastConfirmSimple n ((simState x5 k').1[sm5.sender].view)
          (t' / Q.slotLength - 1) := by
      subst hn
      exact fastConfirmSimple_congr hskel _ _
    obtain ⟨m2, hm2mem, hm2eq⟩ := tau_emitted_image hlbl' rfl hsend'
    obtain ⟨-, -, hm2⟩ := handler2_propose_send (n := n) hmod hm2mem
    simp only [setClock_getElem, if_pos rfl, if_true] at hm2
    -- the table's value at `k` is the value written at the emission
    have hsent : sm5 ∈ (x5.cfg (k' + 1)).sent := by
      have h := tick_send_mem5 hlbl' hsend'
      rw [show (⟨sm5.sender, sm5.msg⟩ : SignedMsg Node M) = sm5 from rfl] at h
      exact h
    have hstab : (simState x5 k).2 sm5 = (simState x5 (k' + 1)).2 sm5 :=
      tau_stable hone5 hmc5 hah5 hmono5 hsent (by omega)
    rw [hstab, hm2eq] at hmem
    subst hslot5
    have hm2'' : m2 = Msg.propose (extend pool
        (mfc ((simState x5 k').1[sm5.sender].view) ((simState x5 k').1[sm5.sender].view)
          chC (t' / Q.slotLength)) (t' / Q.slotLength)) chC (some cert) simBlank
        (t' / Q.slotLength) := by
      rw [hm2, ← hfcs2, ← hchC5, ← hqc5]
    refine ⟨⟨sm5.sender, m2⟩, hmem, _, simBlank, rfl, hm2'', proposedAt_extend _ _ _, ?_⟩
    exact chainLe_trans (base_le_mfc _ _ _ _) (chainLe_extend _ _ _)

/-- **A certificate's votes cross the correspondence**: each certified vote is identified
    by signer, chain and slot, which is exactly what dynamic equivalence preserves — the
    fin-vote fields stay existential. -/
theorem cert_votes_transfer {V5 V2 : View Node M} (hcorr : ViewCorr V5 V2)
    {ch : Chain Tx} {t : Nat} {cert : QCert Node Tx}
    (hvotes : ∀ e ∈ cert, chainLe ch e.2.1 ∧ e.2.2 = t ∧
      ∃ src tgt : Checkpoint (Chain Tx),
        (⟨e.1, Msg.vote e.2.1 src tgt e.2.2⟩ : SignedMsg Node M) ∈ V5) :
    ∀ e ∈ cert, chainLe ch e.2.1 ∧ e.2.2 = t ∧
      ∃ src tgt : Checkpoint (Chain Tx),
        (⟨e.1, Msg.vote e.2.1 src tgt e.2.2⟩ : SignedMsg Node M) ∈ V2 := by
  intro e he
  obtain ⟨h1, h2, src, tgt, hmem⟩ := hvotes e he
  refine ⟨h1, h2, ?_⟩
  obtain ⟨sm', hsm', hsend', hde⟩ := hcorr.1 _ hmem
  rcases hm' : sm'.msg with ⟨chp', chC', qc', ck', τ'⟩ | ⟨e', src', tgt', τ'⟩ <;>
    rw [hm'] at hde
  · cases hde
  · obtain ⟨hee, htt⟩ := hde
    refine ⟨src', tgt', ?_⟩
    have hsm'eq : sm' = ⟨e.1, Msg.vote e.2.1 src' tgt' e.2.2⟩ := by
      cases sm' with
      | mk sd mg =>
          simp only at hsend' hm'
          rw [← hsend', hm', ← hee, ← htt]
    rw [← hsm'eq]
    exact hsm'

set_option maxHeartbeats 1000000 in
/-- **A certified proposal's chain sits below the simulated vote-round fork choice** —
    `h_b5`'s certificate case. The counterpart proposal in the simulated view carries the
    same certificate, so it is Algorithm-2-valid there: either the simulated fold adopted
    a chain extending it, or something not below it blocked the write — and the blocker
    cannot happen, because both bases are quorum-supported at slot `s1`, hence comparable,
    and the wrong orientation contradicts the blocker. -/
theorem cert_le_voteMfc (hn : n = Fintype.card Node)
    {x5 : Exec Pr5 S} (H5 : SettingGA Q S x5) (H2 : SettingGA Q S (simulate x5))
    {k : Nat} (hTD : ∀ j, j ≤ k → TableDynEq x5 j)
    {p : Node} {s1 : Nat}
    (hlbl : x5.lbl k = .tick p (Q.slotLength * (s1 + 1) + Q.delta))
    (hact : p ∈ Active Q S ((s1 : Int) + 1))
    {sm5 : SignedMsg Node M} (hsm5 : sm5 ∈ x5[k][p].view)
    {chp chC : Chain Tx} {cert : QCert Node Tx} {ck : Checkpoint (Chain Tx)}
    (hmsg5 : sm5.msg = .propose chp chC (some cert) ck (s1 + 1))
    (hsender : sm5.sender = proposer (s1 + 1))
    (hpa : proposedAt chp = s1 + 1) (hchp : chainLe chC chp)
    (hcard : 2 * n ≤ 3 * (cert.image Prod.fst).card)
    (hvotes : ∀ e ∈ cert, chainLe chC e.2.1 ∧ e.2.2 = s1 ∧
      ∃ src tgt : Checkpoint (Chain Tx),
        (⟨e.1, Msg.vote e.2.1 src tgt e.2.2⟩ : SignedMsg Node M) ∈ x5[k][p].view) :
    chainLe chC
      (mfc (processProposals2 n proposer ((simulate x5)[k][p].view) (s1 + 1)
          ((simulate x5)[k][p].st)).vFrozen ((simulate x5)[k][p].view)
        (processProposals2 n proposer ((simulate x5)[k][p].view) (s1 + 1)
          ((simulate x5)[k][p].st)).chFrozen (s1 + 1)) := by
  have H5' := H5
  obtain ⟨⟨hmc5, hah5, -, hmono5, -, -, -⟩, -, -, hone5, -, -, -, -⟩ := H5'
  have H2' := H2
  obtain ⟨⟨hmc2, -, hsync2, hmono2, -, -, hdil2⟩, hstepw2, -, hone2, -, -,
    ⟨hcb2, hfn2⟩, -⟩ := H2'
  have hcorr : ViewCorr x5[k][p].view ((simulate x5)[k][p].view) :=
    viewCorr_of_tableDynEq hone5 hmc5 hah5 hmono5 (hTD k (le_refl k)) p
  obtain ⟨sm2, hsm2, chp2, ck2, hsend2, hmsg2, hpa2, hchp2⟩ :=
    cert_counterpart hn H5 hTD hsm5 hmsg5 hpa hchp
  have hvalid2 : ValidProposal2 n proposer ((simulate x5)[k][p].view) sm2 :=
    validProposal2_of_cert hcorr hmsg2 (by rw [hsend2, hsender]) hpa2 hchp2 hcard
      (fun e he => by
        obtain ⟨h1, h2, h3⟩ := hvotes e he
        exact ⟨h1, by omega, h3⟩)
  -- the certificate's quorum, in the simulated view
  have hsupp : 2 * n ≤ 3 * (((votes ((simulate x5)[k][p].view)).filter
      (fun sm => msgSlot sm.msg = s1 ∧ chainLe chC (msgChain sm.msg))).image
        SignedMsg.sender).card :=
    support_of_cert hcard (cert_votes_transfer hcorr hvotes)
  -- the simulated base is genesis or quorum-supported, hence comparable with `chC`
  have hlbl2 : (simulate x5).lbl k
      = .tick p (Q.slotLength * (s1 + 1) + Q.delta) := simLbl_tick_iff.mpr hlbl
  have hcompar : chainLe chC ((processProposals2 n proposer ((simulate x5)[k][p].view)
        (s1 + 1) ((simulate x5)[k][p].st)).chFrozen) ∨
      chainLe ((processProposals2 n proposer ((simulate x5)[k][p].view) (s1 + 1)
        ((simulate x5)[k][p].st)).chFrozen) chC := by
    rcases frozen2_supported_or_nil hsync2 hstepw2 hdil2 hone2 hact hlbl2 with hnil | hsupp2
    · rw [hnil]
      exact Or.inr (chainLe_nil _)
    · exact supported_comparable hsync2 hone2 hmc2 hmono2 hcb2 (hn ▸ hfn2)
        (le_of_eq hn.symm) hsupp hsupp2
  rcases processProposals2_chFrozen_lb ((simulate x5)[k][p].view) (s1 + 1)
      ((simulate x5)[k][p].st) hsm2 hmsg2 hvalid2 with h | ⟨y, hy1, hy2⟩
  · exact chainLe_trans h (base_le_mfc _ _ _ _)
  · rcases hcompar with h | h
    · exact chainLe_trans h (base_le_mfc _ _ _ _)
    · exact absurd (chainLe_trans hy2 h) hy1

set_option maxHeartbeats 1000000 in
/-- **Condition 2.2's first cross-bound**, `h_b5`: Algorithm 5's processed frozen chain
    sits below the *simulated* run's vote-round fork choice. Its three provenance cases —
    the merge seed, a certified proposal's chain, a justified checkpoint's chain — are
    `chFrozen5_le_voteMfc`, `cert_le_voteMfc` and `justified_le_voteMfc`; Algorithm 5's
    validity contributes one more justified rung, covered by the same descent. -/
theorem b5_le_voteMfc (hn : n = Fintype.card Node)
    {x5 : Exec Pr5 S} (H5 : SettingGA Q S x5) (H2 : SettingGA Q S (simulate x5))
    (hκ : 1 ≤ kappa) (hwin2 : HonestProposalWindow (simulate x5))
    {k : Nat} (hTD : ∀ j, j ≤ k → TableDynEq x5 j)
    (hD : ∀ (j : Nat), j ≤ k → ∀ (q : Node), ∃ (a : Nat) (w : Node),
      (simulate x5)[a].time ≤ x5[j].time ∧
      chainLe x5[j][q].st.chAva ((simulate x5)[a][w].st.chi))
    {p : Node} {s1 : Nat}
    (hlbl : x5.lbl k = .tick p (Q.slotLength * (s1 + 1) + Q.delta))
    (hact : p ∈ Active Q S ((s1 : Int) + 1)) :
    chainLe (processProposals (components n kappa pool proposer) (x5[k][p].view) (s1 + 1)
        (x5[k][p].st)).chFrozen
      (mfc (processProposals2 n proposer ((simulate x5)[k][p].view) (s1 + 1)
          ((simulate x5)[k][p].st)).vFrozen ((simulate x5)[k][p].view)
        (processProposals2 n proposer ((simulate x5)[k][p].view) (s1 + 1)
          ((simulate x5)[k][p].st)).chFrozen (s1 + 1)) := by
  rcases processProposals_chFrozen (n := n) (kappa := kappa) (pool := pool)
      (proposer := proposer) (x5[k][p].view) (s1 + 1) (x5[k][p].st) with
    hseed | ⟨sm, hsmV, ⟨chp, qc, ck, hmsg⟩, hvalid⟩ | ⟨c, hj⟩
  · rw [hseed]
    exact chFrozen5_le_voteMfc hn H5 H2 hκ hwin2 hTD hD hlbl hact
  · -- a proposal write: Algorithm 5's three validity rungs
    obtain ⟨sd, m0⟩ := sm
    have hm0 : m0 = Msg.propose chp
        ((processProposals (components n kappa pool proposer) (x5[k][p].view) (s1 + 1)
          (x5[k][p].st)).chFrozen) qc ck (s1 + 1) := hmsg
    subst hm0
    have hvp : (⟨sd, Msg.propose chp
            ((processProposals (components n kappa pool proposer) (x5[k][p].view) (s1 + 1)
              (x5[k][p].st)).chFrozen) qc ck (s1 + 1)⟩ : SignedMsg Node M).sender
          = proposer (s1 + 1) ∧
        proposedAt chp = s1 + 1 ∧
        chainLe ((processProposals (components n kappa pool proposer) (x5[k][p].view)
          (s1 + 1) (x5[k][p].st)).chFrozen) chp ∧
        (((processProposals (components n kappa pool proposer) (x5[k][p].view) (s1 + 1)
              (x5[k][p].st)).chFrozen) = [] ∨
          (∃ cert : QCert Node Tx, qc = some cert ∧
            2 * n ≤ 3 * (cert.image Prod.fst).card ∧
            ∀ e ∈ cert, chainLe ((processProposals (components n kappa pool proposer)
                (x5[k][p].view) (s1 + 1) (x5[k][p].st)).chFrozen) e.2.1 ∧
              e.2.2 = s1 + 1 - 1 ∧
              ∃ src tgt : Checkpoint (Chain Tx),
                (⟨e.1, Msg.vote e.2.1 src tgt e.2.2⟩ : SignedMsg Node M)
                  ∈ x5[k][p].view) ∨
          (qc = none ∧ ((processProposals (components n kappa pool proposer)
              (x5[k][p].view) (s1 + 1) (x5[k][p].st)).chFrozen) = ck.ch ∧
            JustifiedIn n (x5[k][p].view) ck)) := hvalid
    rcases hvp.2.2.2 with hnil | ⟨cert, hqc, hcard, hvotes⟩ | ⟨-, hck, hjck⟩
    · rw [hnil]
      exact chainLe_nil _
    · subst hqc
      exact cert_le_voteMfc hn H5 H2 hTD hlbl hact hsmV rfl hvp.1 hvp.2.1 hvp.2.2.1
        hcard (fun e he => by
          obtain ⟨h1, h2, h3⟩ := hvotes e he
          exact ⟨h1, by omega, h3⟩)
    · rw [hck]
      exact justified_le_voteMfc hn H5 H2 hκ hwin2 hD hlbl hact (le_refl k) hjck
  · exact justified_le_voteMfc hn H5 H2 hκ hwin2 hD hlbl hact (le_refl k)
      (J := ⟨_, c⟩) hj

/-! ### Algorithm 5's proposal fold is a maximum once every write sits under one chain -/

/-- **A fold whose every step stays under a bound and never descends**: the conclusion for
    the whole list, from the per-step fact. Stated over an abstract step so the concrete
    fold's guard tree is never spelled out. -/
theorem foldl_bounded_mono {α : Type}
    {f : NodeState Node (Chain Tx) (QCert Node Tx) → α →
      NodeState Node (Chain Tx) (QCert Node Tx)}
    {O : Chain Tx} {l : List α}
    (hf : ∀ (acc : NodeState Node (Chain Tx) (QCert Node Tx)) (a : α), a ∈ l →
      chainLe acc.chFrozen O →
      chainLe (f acc a).chFrozen O ∧ chainLe acc.chFrozen (f acc a).chFrozen)
    {s : NodeState Node (Chain Tx) (QCert Node Tx)} (hs : chainLe s.chFrozen O) :
    chainLe (l.foldl f s).chFrozen O ∧ chainLe s.chFrozen (l.foldl f s).chFrozen := by
  induction l generalizing s with
  | nil => exact ⟨hs, chainLe_refl _⟩
  | cons a l ih =>
      rw [List.foldl_cons]
      obtain ⟨h1, h2⟩ := hf s a List.mem_cons_self hs
      obtain ⟨h3, h4⟩ :=
        ih (fun acc b hb => hf acc b (List.mem_cons_of_mem a hb)) h1
      exact ⟨h3, chainLe_trans h2 h4⟩

/-- **A bounded fold dominates a value its own step would write**: at the scan position the
    accumulator is comparable with the value (both sit under `O`), so either the value is
    already below the accumulator, or the step fires and writes it — and the rest of the
    fold never descends. -/
theorem foldl_ge_of_fires {α : Type}
    {f : NodeState Node (Chain Tx) (QCert Node Tx) → α →
      NodeState Node (Chain Tx) (QCert Node Tx)}
    {O : Chain Tx} {l : List α} {v : Chain Tx}
    (hf : ∀ (acc : NodeState Node (Chain Tx) (QCert Node Tx)) (a : α), a ∈ l →
      chainLe acc.chFrozen O →
      chainLe (f acc a).chFrozen O ∧ chainLe acc.chFrozen (f acc a).chFrozen)
    {a₀ : α} (ha₀ : a₀ ∈ l) (hv : chainLe v O)
    (hfire : ∀ acc : NodeState Node (Chain Tx) (QCert Node Tx),
      chainLe acc.chFrozen O → chainLe acc.chFrozen v → chainLe v (f acc a₀).chFrozen)
    {s : NodeState Node (Chain Tx) (QCert Node Tx)} (hs : chainLe s.chFrozen O) :
    chainLe v (l.foldl f s).chFrozen := by
  induction l generalizing s with
  | nil => cases ha₀
  | cons a l ih =>
      rw [List.foldl_cons]
      have hf' : ∀ (acc : NodeState Node (Chain Tx) (QCert Node Tx)) (b : α), b ∈ l →
          chainLe acc.chFrozen O →
          chainLe (f acc b).chFrozen O ∧ chainLe acc.chFrozen (f acc b).chFrozen :=
        fun acc b hb => hf acc b (List.mem_cons_of_mem a hb)
      rcases List.mem_cons.mp ha₀ with rfl | ha₀l
      · -- the value's own step runs now
        obtain ⟨h1, h2⟩ := hf s a₀ List.mem_cons_self hs
        have hstep : chainLe v (f s a₀).chFrozen := by
          rcases comparable_of_common_extension hs hv with hle | hle
          · exact hfire s hs hle
          · exact chainLe_trans hle h2
        exact chainLe_trans hstep (foldl_bounded_mono hf' h1).2
      · obtain ⟨h1, -⟩ := hf s a List.mem_cons_self hs
        exact ih (fun acc b hb => hf acc b (List.mem_cons_of_mem a hb)) ha₀l h1

/-- **Both conclusions from one step fact**: the bound with monotonicity, and the
    domination of every value the fold's own step would write. `P a v` says "`a` offers the
    write value `v`". -/
theorem foldl_bounded_all {α : Type}
    {f : NodeState Node (Chain Tx) (QCert Node Tx) → α →
      NodeState Node (Chain Tx) (QCert Node Tx)}
    {O : Chain Tx} {l : List α} {P : α → Chain Tx → Prop}
    (hf : ∀ (acc : NodeState Node (Chain Tx) (QCert Node Tx)) (a : α), a ∈ l →
      chainLe acc.chFrozen O →
      chainLe (f acc a).chFrozen O ∧ chainLe acc.chFrozen (f acc a).chFrozen)
    (hfire : ∀ a₀ ∈ l, ∀ v : Chain Tx, P a₀ v →
      ∀ acc : NodeState Node (Chain Tx) (QCert Node Tx), chainLe acc.chFrozen O →
        chainLe acc.chFrozen v → chainLe v (f acc a₀).chFrozen)
    {s : NodeState Node (Chain Tx) (QCert Node Tx)} (hs : chainLe s.chFrozen O) :
    (chainLe (l.foldl f s).chFrozen O ∧ chainLe s.chFrozen (l.foldl f s).chFrozen) ∧
      ∀ a₀ ∈ l, ∀ v : Chain Tx, P a₀ v → chainLe v O →
        chainLe v (l.foldl f s).chFrozen :=
  ⟨foldl_bounded_mono hf hs,
    fun a₀ ha₀ v hP hv => foldl_ge_of_fires hf ha₀ hv (hfire a₀ ha₀ v hP) hs⟩

set_option maxHeartbeats 1000000 in
/-- **Algorithm 5's proposal fold, under a common bound**: with every write value below
    `O` — the certificate writes by `hval`, the justified-chain writes by `hjust` — the
    processed frozen chain stays below `O`, never descends below the seed, and *dominates
    every valid slot-`t` proposal's chain*.

    The last is what condition 2.2's second cross-bound needs, and it is why the bound is
    hypothesized rather than derived: the paper's justified-chain reset
    (`chfrozen ← GJ_p.ch` when the accumulator does not extend it) can move the
    accumulator sideways in general, and only comparability — which the common bound
    supplies — makes it move *up*, turning the fold into a maximum. -/
theorem processProposals_bounded {V : View Node M} {t : Nat}
    {s : NodeState Node (Chain Tx) (QCert Node Tx)} {O : Chain Tx}
    (hseed : chainLe s.chFrozen O)
    (hval : ∀ sm ∈ V, ∀ chp chC qc ck, sm.msg = .propose chp chC qc ck t →
      ValidProposal5 n proposer V sm → chainLe chC O)
    (hjust : ∀ sm ∈ V, ∀ chp chC qc gjp, sm.msg = .propose chp chC qc gjp t →
      JustifiedIn n V gjp → chainLe gjp.ch O) :
    (chainLe (processProposals (components n kappa pool proposer) V t s).chFrozen O ∧
        chainLe s.chFrozen
          (processProposals (components n kappa pool proposer) V t s).chFrozen) ∧
      ∀ sm ∈ V.toList, ∀ v : Chain Tx,
        ((∃ chp qc ck, sm.msg = .propose chp v qc ck t) ∧
          ValidProposal5 n proposer V sm) → chainLe v O →
        chainLe v (processProposals (components n kappa pool proposer) V t s).chFrozen := by
  unfold processProposals
  refine foldl_bounded_all ?_ ?_ hseed
  · -- every step stays under `O` and never descends
    intro acc a ha hacc
    have haV : a ∈ V := Finset.mem_toList.mp ha
    obtain ⟨asd, amsg⟩ := a
    cases amsg with
    | vote ch src tgt t' => exact ⟨hacc, chainLe_refl _⟩
    | propose chp chC qc gjp t' =>
        dsimp only
        by_cases hgj : t' = t ∧ (components n kappa pool proposer).validProposal V
              ⟨asd, .propose chp chC qc gjp t'⟩ ∧
            (components n kappa pool proposer).justified gjp V = true ∧
            acc.gjFrozen.c ≤ gjp.c
        · rw [if_pos hgj]
          have hgjO : chainLe gjp.ch O :=
            hjust _ haV chp chC qc gjp (by rw [hgj.1]) (of_decide_eq_true hgj.2.2.1)
          by_cases h1 : (components n kappa pool proposer).prefixLe gjp.ch acc.chFrozen
          · rw [if_pos h1]
            split_ifs with h2
            · exact ⟨hval _ haV chp chC qc gjp (by rw [h2.1]) h2.2.1, h2.2.2⟩
            · exact ⟨hacc, chainLe_refl _⟩
          · rw [if_neg h1]
            have hup : chainLe acc.chFrozen gjp.ch := by
              rcases comparable_of_common_extension hacc hgjO with h | h
              · exact h
              · exact absurd h h1
            split_ifs with h2
            · exact ⟨hval _ haV chp chC qc gjp (by rw [h2.1]) h2.2.1,
                chainLe_trans hup h2.2.2⟩
            · exact ⟨hgjO, hup⟩
        · rw [if_neg hgj]
          split_ifs with h2
          · exact ⟨hval _ haV chp chC qc gjp (by rw [h2.1]) h2.2.1, h2.2.2⟩
          · exact ⟨hacc, chainLe_refl _⟩
  · -- a valid proposal's own step leaves the fold above its chain
    intro a₀ ha₀ v hP acc hacc hle
    obtain ⟨⟨chp, qc, ck, hmsg⟩, hvalid⟩ := hP
    have haV : a₀ ∈ V := Finset.mem_toList.mp ha₀
    obtain ⟨asd, amsg⟩ := a₀
    have hm0 : amsg = Msg.propose chp v qc ck t := hmsg
    subst hm0
    dsimp only
    by_cases hgj : t = t ∧ (components n kappa pool proposer).validProposal V
          ⟨asd, .propose chp v qc ck t⟩ ∧
        (components n kappa pool proposer).justified ck V = true ∧ acc.gjFrozen.c ≤ ck.c
    · rw [if_pos hgj]
      have hckO : chainLe ck.ch O :=
        hjust _ haV chp v qc ck rfl (of_decide_eq_true hgj.2.2.1)
      by_cases h1 : (components n kappa pool proposer).prefixLe ck.ch acc.chFrozen
      · rw [if_pos h1]
        split_ifs with h2
        · exact chainLe_refl v
        · exact absurd ⟨rfl, hvalid, hle⟩ h2
      · rw [if_neg h1]
        split_ifs with h2
        · exact chainLe_refl v
        · rcases comparable_of_common_extension hckO
            (hval _ haV chp v qc ck rfl hvalid) with h | h
          · exact absurd ⟨rfl, hvalid, h⟩ h2
          · exact h
    · rw [if_neg hgj]
      split_ifs with h2
      · exact chainLe_refl v
      · exact absurd ⟨rfl, hvalid, hle⟩ h2

/-- The view correspondence is symmetric, `SDynEq` being symmetric. -/
theorem ViewCorr.symm {V5 V2 : View Node M} (h : ViewCorr V5 V2) : ViewCorr V2 V5 :=
  ⟨fun sm hsm => let ⟨sm', hsm', hde⟩ := h.2 sm hsm; ⟨sm', hsm', hde.symm⟩,
    fun sm hsm => let ⟨sm', hsm', hde⟩ := h.1 sm hsm; ⟨sm', hsm', hde.symm⟩⟩

set_option maxHeartbeats 2000000 in
/-- **Every Algorithm-2 proposal write has an Algorithm-5 write at or above it**: given a
    valid slot-`s1+1` proposal in the simulated view, the original view holds a valid
    proposal whose own chain extends it. By origin: a pure injection is its own
    counterpart (`ValidProposal2`'s certificate clause is `ValidProposal5`'s, transported
    by `cert_votes_transfer`); an honest emission's counterpart is the very message the
    tick sent, and its `chC` is `fastconfirm`'s — the `fastconfirmsimple` branch gives the
    *same* chain and certificate by congruence, while the `GJ` branch gives the greatest
    justified chain, which the branch guard puts *above* the simulated one (comparability
    under the common bound `O`). Honest relay carries the proposer's evidence into the
    voter's view, so the justified rung is checkable there. -/
theorem valid2_counterpart5 (hn : n = Fintype.card Node)
    {x5 : Exec Pr5 S} (H5 : SettingGA Q S x5)
    {k : Nat} (hTD : ∀ j, j ≤ k → TableDynEq x5 j)
    {p : Node} {s1 : Nat}
    (hlbl : x5.lbl k = .tick p (Q.slotLength * (s1 + 1) + Q.delta))
    {O : Chain Tx}
    (hjustO : ∀ j, j ≤ k → ∀ (q : Node) (J : Checkpoint (Chain Tx)),
      JustifiedIn n x5[j][q].view J → chainLe J.ch O)
    {sm2 : SignedMsg Node M} (hsm2 : sm2 ∈ (simulate x5)[k][p].view)
    {chp2 A : Chain Tx} {qc2 : Option (QCert Node Tx)} {ck2 : Checkpoint (Chain Tx)}
    (hmsg2 : sm2.msg = .propose chp2 A qc2 ck2 (s1 + 1))
    (hvalid2 : ValidProposal2 n proposer ((simulate x5)[k][p].view) sm2)
    (hAO : chainLe A O) :
    ∃ sm5 ∈ x5[k][p].view, ∃ chp5 c qc5 ck5,
      sm5.msg = .propose chp5 c qc5 ck5 (s1 + 1) ∧
      ValidProposal5 n proposer (x5[k][p].view) sm5 ∧ chainLe A c := by
  have hδ := Q.deltaPos
  have H5' := H5
  obtain ⟨⟨hmc5, hah5, hsync5, hmono5, -, -, -⟩, -, -, hone5, ⟨hsyn5, hrel5⟩, -, -,
    hgst5⟩ := H5'
  have hcorr : ViewCorr x5[k][p].view ((simulate x5)[k][p].view) :=
    viewCorr_of_tableDynEq hone5 hmc5 hah5 hmono5 (hTD k (le_refl k)) p
  -- the simulated message's validity data
  have hvp2 : sm2.sender = proposer (s1 + 1) ∧ proposedAt chp2 = s1 + 1 ∧
      chainLe A chp2 ∧
      (A = [] ∨ ∃ cert : QCert Node Tx, qc2 = some cert ∧
        2 * n ≤ 3 * (cert.image Prod.fst).card ∧
        ∀ e ∈ cert, chainLe A e.2.1 ∧ e.2.2 = s1 + 1 - 1 ∧
          ∃ src tgt : Checkpoint (Chain Tx),
            (⟨e.1, Msg.vote e.2.1 src tgt e.2.2⟩ : SignedMsg Node M)
              ∈ (simulate x5)[k][p].view) := by
    have h := hvalid2
    unfold ValidProposal2 at h
    rw [hmsg2] at h
    exact h
  -- the certificate clause, transported into the original view
  have hrung5 : ∀ c : Chain Tx, c = A → ∀ qc : Option (QCert Node Tx), qc = qc2 →
      ∀ gjp : Checkpoint (Chain Tx),
      (c = [] ∨
        (∃ cert : QCert Node Tx, qc = some cert ∧
          2 * n ≤ 3 * (cert.image Prod.fst).card ∧
          ∀ e ∈ cert, chainLe c e.2.1 ∧ e.2.2 = s1 + 1 - 1 ∧
            ∃ src tgt : Checkpoint (Chain Tx),
              (⟨e.1, Msg.vote e.2.1 src tgt e.2.2⟩ : SignedMsg Node M)
                ∈ x5[k][p].view) ∨
        (qc = none ∧ c = gjp.ch ∧ JustifiedIn n (x5[k][p].view) gjp)) := by
    intro c hc qc hqc gjp
    subst hc
    subst hqc
    rcases hvp2.2.2.2 with hnil | ⟨cert, hqc2, hcard, hvotes⟩
    · exact Or.inl hnil
    · exact Or.inr (Or.inl ⟨cert, hqc2, hcard,
        cert_votes_transfer hcorr.symm hvotes⟩)
  -- the original message behind it
  obtain ⟨m5, hm5V, hm5eq⟩ := view_covered hone5 hmc5 hah5 hmono5 k p hsm2
  have hsender5 : sm2.sender = m5.sender := by
    rw [hm5eq]
    exact sim_table_sender k m5
  have hdeq : DynEq m5.msg sm2.msg := by
    rw [hm5eq]
    exact (hTD k (le_refl k) m5).2
  rcases tau_id_or_emitted x5 k m5 with hid | ⟨k', hk'k, t', hlbl', hsend'⟩
  · -- a pure injection: the same message
    have hsm5 : m5 = sm2 := by rw [hm5eq, hid]
    subst hsm5
    refine ⟨m5, hm5V, chp2, A, qc2, ck2, hmsg2, ?_, chainLe_refl A⟩
    unfold ValidProposal5
    rw [hmsg2]
    exact ⟨hvp2.1, hvp2.2.1, hvp2.2.2.1, hrung5 A rfl qc2 rfl ck2⟩
  · -- an honest emission: the counterpart is the simulated tick's own send
    set q := m5.sender with hq
    -- the emitted message is a propose at slot `s1 + 1`
    have hshape := (mem_handler_send hsend').2
    obtain ⟨chp5, c, qc5, gjp5, hm5msg, hmod⟩ : ∃ chp5 c qc5 gjp5,
        m5.msg = .propose chp5 c qc5 gjp5 (t' / Q.slotLength) ∧
        t' % Q.slotLength = 0 := by
      rcases hshape with ⟨a, b, cc, d, heq, hmod⟩ | ⟨a, b, cc, hvote⟩
      · exact ⟨a, b, cc, d, heq, hmod⟩
      · exfalso
        rw [hvote.1, hmsg2] at hdeq
        exact hdeq
    have hslot : t' / Q.slotLength = s1 + 1 := by
      rw [hm5msg, hmsg2] at hdeq
      exact hdeq.2
    rw [hslot] at hm5msg
    -- the tick's own view and its fields
    obtain ⟨-, -, hm5send⟩ := handler_propose_send hmod hsend'
    simp only [setClock_getElem, if_pos rfl, if_true] at hm5send
    rw [hm5msg, hslot] at hm5send
    rw [Msg.propose.injEq] at hm5send
    obtain ⟨hchp5, hc5, hqc5, hgjp5, -⟩ := hm5send
    -- the simulated tick's send is `sm2`
    obtain ⟨m2, hm2mem, hm2eq⟩ := tau_emitted_image hlbl' rfl hsend'
    obtain ⟨-, -, hm2send⟩ := handler2_propose_send (n := n) hmod hm2mem
    simp only [setClock_getElem, if_pos rfl, if_true] at hm2send
    rw [hslot] at hm2send
    have hsent : m5 ∈ (x5.cfg (k' + 1)).sent := by
      have h := tick_send_mem5 hlbl' hsend'
      rw [show (⟨m5.sender, m5.msg⟩ : SignedMsg Node M) = m5 from rfl] at h
      exact h
    have hstab : (simState x5 k).2 m5 = (simState x5 (k' + 1)).2 m5 :=
      tau_stable hone5 hmc5 hah5 hmono5 hsent (by omega)
    have hsm2msg : sm2.msg = m2 := by rw [hm5eq, hstab, hm2eq]
    rw [hsm2msg, hm2send] at hmsg2
    rw [Msg.propose.injEq] at hmsg2
    obtain ⟨-, hA, hqc2, -, -⟩ := hmsg2
    -- the two runs' fast confirmations agree
    have hfcs : fastConfirmSimple n (x5.cfg k')[q].view (s1 + 1 - 1)
        = fastConfirmSimple n ((simState x5 k').1[q].view) (s1 + 1 - 1) := by
      subst hn
      exact fastConfirmSimple_congr (voteSkel_eq_of_corr
        (viewCorr_of_tableDynEq hone5 hmc5 hah5 hmono5 (hTD k' (le_of_lt hk'k)) q)) _ _
    -- honest relay carries the proposer's view into the voter's
    have hawk : x5.Awake k p := by
      have hstep := x5.step k
      rw [hlbl] at hstep
      have h1 := hstep.1
      simp only [spec] at h1
      exact h1
    have hawk' : x5.Awake k' q := by
      have hstep := x5.step k'
      rw [hlbl'] at hstep
      have h1 := hstep.1
      simp only [spec] at h1
      exact h1
    have htimes : x5[k'].time + Q.delta ≤ x5[k].time := by
      have h1 : x5[k'].time = t' := tick_reading5 hsync5 hlbl'
      have h2 : x5[k].time = Q.slotLength * (s1 + 1) + Q.delta :=
        tick_reading5 hsync5 hlbl
      have h3 : Q.slotLength * (t' / Q.slotLength) + t' % Q.slotLength = t' :=
        Nat.div_add_mod t' Q.slotLength
      rw [hslot, hmod] at h3
      omega
    have hview5 : ∀ m ∈ (x5.cfg k')[q].view, m ∈ x5[k][p].view := by
      intro m hm
      refine hrel5 k' k q p m hawk' hm ?_ hawk
      have hg0 : Q.gst = 0 := hgst5
      omega
    -- the merge branch decides which chain the original proposal carries
    unfold Components.fastConfirm at hc5 hqc5 hchp5
    rw [components_fastConfirmSimple, components_gj, components_prefixLe] at hc5 hqc5 hchp5
    rw [components_extend, components_mfc] at hchp5
    dsimp only at hc5 hqc5 hchp5
    by_cases hg : chainLe (gj n (x5.cfg k')[q].view).ch
        (fastConfirmSimple n (x5.cfg k')[q].view (s1 + 1 - 1)).1
    · -- the fast-confirm branch: the same chain and certificate
      rw [if_pos hg] at hc5 hqc5 hchp5
      have hcA : c = A := by rw [hc5, hfcs, hA]
      have hAc : chainLe A c := by
        rw [hcA]
        exact chainLe_refl A
      have hpa5 : proposedAt chp5 = s1 + 1 := by
        rw [hchp5]
        exact proposedAt_extend _ _ _
      have hle5 : chainLe c chp5 := by
        rw [hchp5, hc5]
        exact chainLe_trans (base_le_mfc _ _ _ _) (chainLe_extend _ _ _)
      have hv5 : ValidProposal5 n proposer (x5[k][p].view) m5 := by
        unfold ValidProposal5
        rw [hm5msg]
        exact ⟨by rw [← hq, ← hsender5]; exact hvp2.1, hpa5, hle5,
          hrung5 c hcA qc5 (by rw [hqc5, hfcs, hqc2]) gjp5⟩
      exact ⟨m5, hm5V, chp5, c, qc5, gjp5, hm5msg, hv5, hAc⟩
    · -- the greatest-justified branch: its chain tops the simulated one
      rw [if_neg hg] at hc5 hqc5 hchp5
      have hjust5 : JustifiedIn n (x5.cfg k')[q].view (gj n (x5.cfg k')[q].view) :=
        gj_justified n _
      have hAc : chainLe A c := by
        have hGO : chainLe (gj n (x5.cfg k')[q].view).ch O :=
          hjustO k' (le_of_lt hk'k) q _ hjust5
        rw [hc5]
        rcases comparable_of_common_extension hAO hGO with h | h
        · exact h
        · exfalso
          refine hg (chainLe_trans h ?_)
          rw [hfcs, hA]
          exact chainLe_refl A
      have hpa5 : proposedAt chp5 = s1 + 1 := by
        rw [hchp5]
        exact proposedAt_extend _ _ _
      have hle5 : chainLe c chp5 := by
        rw [hchp5, hc5]
        exact chainLe_trans (base_le_mfc _ _ _ _) (chainLe_extend _ _ _)
      have hv5 : ValidProposal5 n proposer (x5[k][p].view) m5 := by
        unfold ValidProposal5
        rw [hm5msg]
        refine ⟨by rw [← hq, ← hsender5]; exact hvp2.1, hpa5, hle5,
          Or.inr (Or.inr ⟨hqc5, ?_, ?_⟩)⟩
        · rw [hc5, hgjp5]
          exact rfl
        · rw [hgjp5]
          exact justifiedIn_mono hview5 hjust5
      exact ⟨m5, hm5V, chp5, c, qc5, gjp5, hm5msg, hv5, hAc⟩

end Majorum
