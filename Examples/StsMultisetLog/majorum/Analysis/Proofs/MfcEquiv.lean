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
            · -- vote reading: both chains are the (aligned) pick
              obtain ⟨src, tgt, hm5⟩ := handler_vote_content hmod hcond.2
              have hm2' := handler2_vote_content hmod hm2
              rw [hm5, hm2']
              exact ⟨(hV p t hl hmod).symm, rfl⟩
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
          split_ifs with hcond h1 h2 <;>
            first
              | exact h
              | exact of_decide_eq_true hcond.2.2.1
  
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

end Majorum
