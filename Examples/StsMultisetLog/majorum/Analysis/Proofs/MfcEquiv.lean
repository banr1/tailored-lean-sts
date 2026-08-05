import Examples.StsMultisetLog.majorum.Analysis.Proofs.Equivalence
import Examples.StsMultisetLog.majorum.Analysis.Proofs.Finality

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
            rcases handler_vFrozen (components n kappa pool proposer) Q q t
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
        obtain ⟨dt, hst, -⟩ := tick_effect hr
        rw [handler2_merge hph3] at hst
        intro a ha
        rw [hst] at ha
        rw [hview]
        exact ha
      · by_cases hph1 : tr % Q.slotLength = Q.delta
        · -- the vote tick's proposal processing keeps the snapshot
          obtain ⟨dt, hst, -⟩ := tick_effect hr
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

end Majorum
