import Examples.StsMultisetLog.majorum.Analysis.Proofs.Simulation

/-!
# The setting transfers to the simulated run (Lemma 10, stage C2)

The Appendix-A lemmas run on `simulate x5` only if the simulated execution satisfies the
same setting as the original. Everything label- or time-shaped carries over through the
simulation's structural invariants (`sim_time`, `sim_clock`, the label translation);
`Synchrony` and `Relay` need the correspondence table to be *stable* — each key is
written at most once, at its own honest tick — which is where `OneTickPerReading`,
`MonotoneCorruption` and `AwakeHonest` earn their keep: a second tick sending the same
message would share its reading, and an injected message's signer can never be awake at
a later tick of its own.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 400

namespace Majorum

open Framework.StsMultisetLog Classical

variable {Node Tx : Type} [DecidableEq Node] [DecidableEq Tx] [Fintype Node]
  {Q : Params} {S : Schedule Node} {n kappa : Nat} {pool : Nat → Tx}
  {proposer : Nat → Node}

local notation "Pr5" => protocol (components n kappa pool proposer) Q
local notation "Pr2" => protocol2 Q n kappa pool proposer
local notation "M" => Msg (Chain Tx) (QCert Node Tx)

/-! ### Labels, translated -/

theorem simLbl_tick_iff {x5 : Exec Pr5 S} {k : Nat} {p : Node} {t : Time} :
    simLbl x5 k = .tick p t ↔ x5.lbl k = .tick p t := by
  cases h : x5.lbl k <;> simp [simLbl, h]

theorem simLbl_wake_iff {x5 : Exec Pr5 S} {k : Nat} {p : Node} :
    simLbl x5 k = .wake p ↔ x5.lbl k = .wake p := by
  cases h : x5.lbl k <;> simp [simLbl, h]

/-! ### The table is written at most once per key -/

/-- One step moves the table only at a tick, and only at the key the tick itself
    freshly sends. -/
theorem tau_write (x5 : Exec Pr5 S) (k : Nat) (sm : SignedMsg Node M) :
    (simState x5 (k + 1)).2 sm = (simState x5 k).2 sm ∨
    ∃ p t, x5.lbl k = .tick p t ∧ sm.sender = p ∧
      sm.msg ∈ (handlerCore (components n kappa pool proposer) Q (pick5 x5 k p t) p t
        (setClock p t (x5.cfg k))[p].view (setClock p t (x5.cfg k))[p].st).send := by
  show (simStep x5 k (simState x5 k)).2 sm = _ ∨ _
  cases h : x5.lbl k with
  | advance t => exact Or.inl (by simp [simStep, h])
  | tick p t =>
      by_cases hcond : sm.sender = p ∧ sm.msg ∈
          (handlerCore (components n kappa pool proposer) Q (pick5 x5 k p t) p t
            (setClock p t (x5.cfg k))[p].view (setClock p t (x5.cfg k))[p].st).send
      · exact Or.inr ⟨p, t, rfl, hcond.1, hcond.2⟩
      · refine Or.inl ?_
        simp only [simStep, h]
        rw [if_neg hcond]
  | deliver p m => exact Or.inl (by simp [simStep, h])
  | wake p => exact Or.inl (by simp [simStep, h])
  | custom p ev => exact ev.elim
  | adversarial p m => exact Or.inl (by simp [simStep, h])

/-- A message's content pins its tick's reading: two core reactions sending the same
    message ran at the same reading — the shape carries the phase and the slot. -/
theorem reading_of_send_eq {C : Components Node (Chain Tx) (QCert Node Tx)}
    {pk pk' : Chain Tx} {p p' : Node} {r r' : Time}
    {V V' : View Node M} {s s' : NodeState Node (Chain Tx) (QCert Node Tx)} {m : M}
    (h : m ∈ (handlerCore C Q pk p r V s).send)
    (h' : m ∈ (handlerCore C Q pk' p' r' V' s').send) : r = r' := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  obtain ⟨-, hsh⟩ := mem_handler_send h
  obtain ⟨-, hsh'⟩ := mem_handler_send h'
  rcases hsh with ⟨chp, chC, qc, gj, hm, hmod⟩ | ⟨ch, src, tgt, hm, hmod⟩ <;>
    rcases hsh' with ⟨chp', chC', qc', gj', hm', hmod'⟩ | ⟨ch', src', tgt', hm', hmod'⟩ <;>
    rw [hm] at hm'
  · injection hm' with _ _ _ _ hslot
    have hr := Nat.div_add_mod r Q.slotLength
    have hr' := Nat.div_add_mod r' Q.slotLength
    have hmul : Q.slotLength * (r / Q.slotLength)
        = Q.slotLength * (r' / Q.slotLength) := by rw [hslot]
    omega
  · cases hm'
  · cases hm'
  · injection hm' with _ _ _ hslot
    have hr := Nat.div_add_mod r Q.slotLength
    have hr' := Nat.div_add_mod r' Q.slotLength
    have hmul : Q.slotLength * (r / Q.slotLength)
        = Q.slotLength * (r' / Q.slotLength) := by rw [hslot]
    omega

/-- **Table stability**: once a message is in the original log, its image never moves
    again. The two closed doors: a later tick re-sending it would share its reading
    (`reading_of_send_eq` + `OneTickPerReading`), and an injected message's signer is
    corrupt, hence never awake at a later tick of its own (`MonotoneCorruption` +
    `AwakeHonest`). -/
theorem tau_stable {x5 : Exec Pr5 S} (hone : OneTickPerReading x5)
    (hmc : S.MonotoneCorruption) (hah : S.AwakeHonest) (hmono : TimeMonotone x5)
    {k : Nat} {sm : SignedMsg Node M} (hsm : sm ∈ (x5.cfg k).sent)
    {k' : Nat} (hkk : k ≤ k') :
    (simState x5 k').2 sm = (simState x5 k).2 sm := by
  induction k' with
  | zero =>
      have : k = 0 := Nat.le_zero.mp hkk
      subst this
      rfl
  | succ k' ih =>
      rcases Nat.lt_or_ge k (k' + 1) with hlt | hge
      · have hk'le : k ≤ k' := by omega
        rw [← ih hk'le]
        rcases tau_write x5 k' sm with heq | ⟨p, t, hlbl, hsender, hsend⟩
        · exact heq
        · exfalso
          obtain ⟨j, hjk, hem⟩ := emitted_of_mem_sent hsm
          have hjk' : j < k' := by omega
          rcases emitted_step hem with ⟨tj, hlblj, -, -, -, pkj, -, hsendj⟩ | hadv
          · -- a tick already sent it: same reading, same tick — but j < k'
            have ht : tj = t := reading_of_send_eq hsendj (by
              simpa [setClock_getElem] using hsend)
            rw [ht, hsender] at hlblj
            exact absurd (hone j k' p t hlblj hlbl) (by omega)
          · -- injected: the signer is corrupt at `j`, so not awake at the later tick
            have hstep := x5.step k'
            rw [hlbl] at hstep
            have hawk : p ∈ S.awake ((x5.cfg k').time : Int) := by
              have h := hstep.1
              simpa [spec] using h
            have htle : (x5.cfg j).time ≤ (x5.cfg k').time :=
              time_le_of_le hmono (le_of_lt hjk')
            have hadvk' : p ∈ S.adv ((x5.cfg k').time : Int) := by
              rw [← hsender]
              exact hmc _ _ (by exact_mod_cast htle) hadv
            exact absurd hawk (Finset.disjoint_right.mp (hah _) hadvk')
      · have : k = k' + 1 := by omega
        subst this
        rfl

/-! ### Views and log, covered by the table -/

/-- The original views map into the simulated ones: whatever `q` has seen, `q` has
    seen the image of. -/
theorem view_image {x5 : Exec Pr5 S} (hone : OneTickPerReading x5)
    (hmc : S.MonotoneCorruption) (hah : S.AwakeHonest) (hmono : TimeMonotone x5)
    (k : Nat) (q : Node) {m : SignedMsg Node M} (hm : m ∈ (x5.cfg k)[q].view) :
    (simState x5 k).2 m ∈ (simState x5 k).1[q].view := by
  induction k with
  | zero =>
      rw [x5.init.2.1 q] at hm
      cases hm
  | succ k ih =>
      have h5 := exec5_succ (x5 := x5) k
      rw [h5] at hm
      show (simStep x5 k (simState x5 k)).2 m ∈ (simStep x5 k (simState x5 k)).1[q].view
      cases h : x5.lbl k with
      | advance t =>
          rw [h] at hm
          simp only [simStep, h]
          exact ih hm
      | tick p t =>
          rw [h] at hm
          -- views untouched; the table is stable at `m`, which the view already holds
          have hmk : m ∈ (x5.cfg k)[q].view := by
            by_cases hq : q = p
            · subst hq
              simpa [applyNodeStepResult_getElem, setClock_getElem] using hm
            · simpa [applyNodeStepResult_getElem, setClock_getElem,
                if_neg (fun hh => hq (Eq.symm hh))] using hm
          have hsent : m ∈ (x5.cfg k).sent := views_sound x5 k q m hmk
          have hstab : (simState x5 (k + 1)).2 m = (simState x5 k).2 m :=
            tau_stable hone hmc hah hmono hsent (Nat.le_succ k)
          have hstab' : (simStep x5 k (simState x5 k)).2 m = (simState x5 k).2 m := hstab
          rw [hstab']
          simp only [simStep, h]
          by_cases hq : q = p
          · subst hq
            simp only [applyNodeStepResult_getElem, setClock_getElem, if_pos rfl,
              if_true]
            exact ih hmk
          · simp only [applyNodeStepResult_getElem, setClock_getElem,
              if_true, if_neg (fun hh => hq (Eq.symm hh))]
            exact ih hmk
      | deliver p m' =>
          rw [h] at hm
          have hsent' : m' ∈ (x5.cfg k).sent := by
            have hstep := x5.step k
            rw [h] at hstep
            exact hstep.1.1
          have hstab : (simStep x5 k (simState x5 k)).2 m = (simState x5 k).2 m := by
            simp [simStep, h]
          rw [hstab]
          simp only [simStep, h]
          by_cases hq : q = p
          · subst hq
            simp only [applyNodeStepResult_getElem, receive_getElem, if_pos rfl,
              if_true] at hm ⊢
            rcases Finset.mem_insert.mp hm with rfl | hold
            · exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem (ih hold)
          · simp only [applyNodeStepResult_getElem, receive_getElem,
              if_neg (fun hh => hq (Eq.symm hh))] at hm ⊢
            exact ih hm
      | wake p =>
          rw [h] at hm
          have hstab : (simStep x5 k (simState x5 k)).2 m = (simState x5 k).2 m := by
            simp [simStep, h]
          rw [hstab]
          simp only [simStep, h]
          by_cases hq : q = p
          · subst hq
            simp only [applyNodeStepResult_getElem, if_pos rfl, if_true] at hm ⊢
            exact ih hm
          · simp only [applyNodeStepResult_getElem,
              if_neg (fun hh => hq (Eq.symm hh))] at hm ⊢
            exact ih hm
      | custom p ev => exact ev.elim
      | adversarial p m' =>
          rw [h] at hm
          have hstab : (simStep x5 k (simState x5 k)).2 m = (simState x5 k).2 m := by
            simp [simStep, h]
          rw [hstab]
          simp only [simStep, h]
          exact ih hm

/-- The simulated views are covered by the table: everything `q` has seen in the
    simulation is the image of something `q` saw in the original. -/
theorem view_covered {x5 : Exec Pr5 S} (hone : OneTickPerReading x5)
    (hmc : S.MonotoneCorruption) (hah : S.AwakeHonest) (hmono : TimeMonotone x5)
    (k : Nat) (q : Node) {m2 : SignedMsg Node M}
    (hm2 : m2 ∈ (simState x5 k).1[q].view) :
    ∃ m5 ∈ (x5.cfg k)[q].view, m2 = (simState x5 k).2 m5 := by
  induction k with
  | zero => cases hm2
  | succ k ih =>
      have hview5 : ∀ m ∈ (x5.cfg k)[q].view, m ∈ (x5.cfg (k + 1))[q].view :=
        fun m hm => view_mono (Pr' := Pr5) k q hm
      rw [show (simState x5 (k + 1)) = simStep x5 k (simState x5 k) from rfl] at hm2
      cases h : x5.lbl k with
      | advance t =>
          simp only [simStep, h] at hm2
          obtain ⟨m5, hm5, heq⟩ := ih hm2
          refine ⟨m5, hview5 m5 hm5, ?_⟩
          rw [heq]
          exact (tau_stable hone hmc hah hmono
            (views_sound x5 k q m5 hm5) (Nat.le_succ k)).symm
      | tick p t =>
          simp only [simStep, h] at hm2
          have hm2' : m2 ∈ (simState x5 k).1[q].view := by
            by_cases hq : q = p
            · subst hq
              simpa [applyNodeStepResult_getElem, setClock_getElem] using hm2
            · simpa [applyNodeStepResult_getElem, setClock_getElem,
                if_neg (fun hh => hq (Eq.symm hh))] using hm2
          obtain ⟨m5, hm5, heq⟩ := ih hm2'
          refine ⟨m5, hview5 m5 hm5, ?_⟩
          rw [heq]
          exact (tau_stable hone hmc hah hmono
            (views_sound x5 k q m5 hm5) (Nat.le_succ k)).symm
      | deliver p m' =>
          simp only [simStep, h] at hm2
          have h5 := exec5_succ (x5 := x5) k
          rw [h5, h]
          have hsent' : m' ∈ (x5.cfg k).sent := by
            have hstep := x5.step k
            rw [h] at hstep
            exact hstep.1.1
          have hstabm' := tau_stable hone hmc hah hmono hsent' (Nat.le_succ k)
          by_cases hq : q = p
          · subst hq
            simp only [applyNodeStepResult_getElem, receive_getElem, if_pos rfl,
              if_true] at hm2 ⊢
            rcases Finset.mem_insert.mp hm2 with rfl | hold
            · exact ⟨m', Finset.mem_insert_self _ _, hstabm'.symm⟩
            · obtain ⟨m5, hm5, heq⟩ := ih hold
              refine ⟨m5, Finset.mem_insert_of_mem hm5, ?_⟩
              rw [heq]
              exact (tau_stable hone hmc hah hmono
                (views_sound x5 k q m5 hm5) (Nat.le_succ k)).symm
          · simp only [applyNodeStepResult_getElem, receive_getElem,
              if_neg (fun hh => hq (Eq.symm hh))] at hm2 ⊢
            obtain ⟨m5, hm5, heq⟩ := ih hm2
            refine ⟨m5, hm5, ?_⟩
            rw [heq]
            exact (tau_stable hone hmc hah hmono
              (views_sound x5 k q m5 hm5) (Nat.le_succ k)).symm
      | wake p =>
          simp only [simStep, h] at hm2
          have hm2' : m2 ∈ (simState x5 k).1[q].view := by
            by_cases hq : q = p
            · subst hq
              simpa [applyNodeStepResult_getElem] using hm2
            · simpa [applyNodeStepResult_getElem,
                if_neg (fun hh => hq (Eq.symm hh))] using hm2
          obtain ⟨m5, hm5, heq⟩ := ih hm2'
          refine ⟨m5, hview5 m5 hm5, ?_⟩
          rw [heq]
          exact (tau_stable hone hmc hah hmono
            (views_sound x5 k q m5 hm5) (Nat.le_succ k)).symm
      | custom p ev => exact ev.elim
      | adversarial p m' =>
          simp only [simStep, h] at hm2
          obtain ⟨m5, hm5, heq⟩ := ih hm2
          refine ⟨m5, hview5 m5 hm5, ?_⟩
          rw [heq]
          exact (tau_stable hone hmc hah hmono
            (views_sound x5 k q m5 hm5) (Nat.le_succ k)).symm

/-- The simulated log is covered by the table: every simulated message is the image of
    an original one. -/
theorem sent_covered {x5 : Exec Pr5 S} (hone : OneTickPerReading x5)
    (hmc : S.MonotoneCorruption) (hah : S.AwakeHonest) (hmono : TimeMonotone x5)
    (k : Nat) {m2 : SignedMsg Node M} (hm2 : m2 ∈ (simState x5 k).1.sent) :
    ∃ m5 ∈ (x5.cfg k).sent, m2 = (simState x5 k).2 m5 := by
  induction k with
  | zero => cases hm2
  | succ k ih =>
      have hsent5 : ∀ m ∈ (x5.cfg k).sent, m ∈ (x5.cfg (k + 1)).sent := by
        intro m hm
        have h5 := exec5_succ (x5 := x5) k
        rw [h5]
        cases h : x5.lbl k with
        | advance t => exact hm
        | tick p t =>
            rw [← setClock_sent p t (x5.cfg k), applyNodeStepResult_sent] at *
            exact Multiset.mem_add.mpr (Or.inl hm)
        | deliver p m' =>
            rw [← receive_sent p m' (x5.cfg k), applyNodeStepResult_sent] at *
            exact Multiset.mem_add.mpr (Or.inl hm)
        | wake p =>
            rw [applyNodeStepResult_sent]
            exact Multiset.mem_add.mpr (Or.inl hm)
        | custom p ev => exact ev.elim
        | adversarial p m' => exact Multiset.mem_cons_of_mem hm
      have hcarry : ∀ m5 ∈ (x5.cfg k).sent, m2 = (simState x5 k).2 m5 →
          ∃ m5' ∈ (x5.cfg (k + 1)).sent, m2 = (simState x5 (k + 1)).2 m5' := by
        intro m5 hm5 heq
        exact ⟨m5, hsent5 m5 hm5,
          heq.trans (tau_stable hone hmc hah hmono hm5 (Nat.le_succ k)).symm⟩
      rw [show (simState x5 (k + 1)) = simStep x5 k (simState x5 k) from rfl] at hm2
      cases h : x5.lbl k with
      | advance t =>
          simp only [simStep, h] at hm2
          obtain ⟨m5, hm5, heq⟩ := ih hm2
          exact hcarry m5 hm5 heq
      | tick p t =>
          simp only [simStep, h, applyNodeStepResult_sent] at hm2
          rcases Multiset.mem_add.mp hm2 with hold | hnew
          · obtain ⟨m5, hm5, heq⟩ := ih hold
            exact hcarry m5 hm5 heq
          · -- the tick's own send: it is the image of the original tick's send
            obtain ⟨mm, hmm, rfl⟩ := Multiset.mem_map.mp hnew
            -- the original tick sent something too (`sends_align`)
            have halign := sends_align (Q := Q) (n := n) (kappa := kappa) (pool := pool)
              (proposer := proposer) (pk5 := pick5 x5 k p t)
              (pk2 := simPick x5 k p t (setClock p t (simState x5 k).1)[p].view
                (setClock p t (simState x5 k).1)[p].st)
              (view5 := (setClock p t (x5.cfg k))[p].view)
              (st5 := (setClock p t (x5.cfg k))[p].st)
              (view2 := (setClock p t (simState x5 k).1)[p].view)
              (st2 := (setClock p t (simState x5 k).1)[p].st) p t
              (by simp only [setClock_getElem, if_pos rfl]
                  exact sim_activeAt (x5 := x5) k p)
            rcases halign with ⟨-, h20⟩ | ⟨h5ne, -⟩
            · exfalso
              rw [h20] at hmm
              cases hmm
            · have hne5 : ((handlerCore (components n kappa pool proposer) Q
                  (pick5 x5 k p t) p t (setClock p t (x5.cfg k))[p].view
                  (setClock p t (x5.cfg k))[p].st).send).toList ≠ [] := by
                intro h0
                exact h5ne (by
                  have := congrArg Multiset.ofList h0
                  simpa [Multiset.coe_toList] using this)
              obtain ⟨m5m, hm5m⟩ := List.exists_mem_of_ne_nil _ hne5
              have hm5m' : m5m ∈ (handlerCore (components n kappa pool proposer) Q
                  (pick5 x5 k p t) p t (setClock p t (x5.cfg k))[p].view
                  (setClock p t (x5.cfg k))[p].st).send := Multiset.mem_toList.mp hm5m
              -- τ at k+1 maps ⟨p, m5m⟩ to the tick's send image
              have hτ : (simStep x5 k (simState x5 k)).2 ⟨p, m5m⟩ = ⟨p, mm⟩ := by
                simp only [simStep, h, true_and]
                rw [if_pos hm5m']
                cases hso : sendOf (handler2Core Q n kappa pool proposer simBlank
                    (simPick x5 k p t (setClock p t (simState x5 k).1)[p].view
                      (setClock p t (simState x5 k).1)[p].st) p t
                    (setClock p t (simState x5 k).1)[p].view
                    (setClock p t (simState x5 k).1)[p].st) with
                | none =>
                    exfalso
                    unfold sendOf at hso
                    rw [List.head?_eq_none_iff] at hso
                    have h20 : (handler2Core Q n kappa pool proposer simBlank
                        (simPick x5 k p t (setClock p t (simState x5 k).1)[p].view
                          (setClock p t (simState x5 k).1)[p].st) p t
                        (setClock p t (simState x5 k).1)[p].view
                        (setClock p t (simState x5 k).1)[p].st).send = 0 := by
                      have := congrArg Multiset.ofList hso
                      simpa [Multiset.coe_toList] using this
                    rw [h20] at hmm
                    cases hmm
                | some m2' =>
                    have hsub := handler2_send_subsingleton (sendOf_mem hso) hmm
                    rw [hsub]
              -- the original tick's send is in the original next log
              have hm5sent : (⟨p, m5m⟩ : SignedMsg Node M) ∈ (x5.cfg (k + 1)).sent := by
                have h5 := exec5_succ (x5 := x5) k
                rw [h5, h]
                rw [← setClock_sent p t (x5.cfg k), applyNodeStepResult_sent]
                exact Multiset.mem_add.mpr
                  (Or.inr (Multiset.mem_map.mpr ⟨m5m, hm5m', rfl⟩))
              exact ⟨⟨p, m5m⟩, hm5sent, hτ.symm⟩
      | deliver p m' =>
          simp only [simStep, h, applyNodeStepResult_sent] at hm2
          rcases Multiset.mem_add.mp hm2 with hold | hnew
          · obtain ⟨m5, hm5, heq⟩ := ih hold
            exact hcarry m5 hm5 heq
          · simp at hnew
      | wake p =>
          simp only [simStep, h, applyNodeStepResult_sent] at hm2
          rcases Multiset.mem_add.mp hm2 with hold | hnew
          · obtain ⟨m5, hm5, heq⟩ := ih hold
            exact hcarry m5 hm5 heq
          · simp at hnew
      | custom p ev => exact ev.elim
      | adversarial p m' =>
          simp only [simStep, h] at hm2
          rcases Multiset.mem_cons.mp hm2 with rfl | hold
          · -- the routed injection: the image of the injected original
            have hs := sim_table_sender (x5 := x5) k (⟨p, m'⟩ : SignedMsg Node M)
            have himg : (⟨p, ((simState x5 k).2 ⟨p, m'⟩).msg⟩ : SignedMsg Node M)
                = (simState x5 k).2 ⟨p, m'⟩ := by
              cases htau : (simState x5 k).2 ⟨p, m'⟩ with
              | mk sd mg =>
                  rw [htau] at hs
                  simp only at hs ⊢
                  rw [hs]
            have hm5sent : (⟨p, m'⟩ : SignedMsg Node M) ∈ (x5.cfg (k + 1)).sent := by
              have h5 := exec5_succ (x5 := x5) k
              rw [h5, h]
              exact Multiset.mem_cons_self _ _
            refine ⟨⟨p, m'⟩, hm5sent, ?_⟩
            rw [himg]
            have : (simState x5 (k + 1)).2 ⟨p, m'⟩ = (simState x5 k).2 ⟨p, m'⟩ := by
              show (simStep x5 k (simState x5 k)).2 ⟨p, m'⟩ = _
              simp [simStep, h]
            rw [this]
          · obtain ⟨m5, hm5, heq⟩ := ih hold
            exact hcarry m5 hm5 heq

/-! ### The setting, transferred -/

theorem simulate_getElem (x5 : Exec Pr5 S) (i : Nat) :
    (simulate x5)[i] = (simState x5 i).1 := rfl

theorem simulate_time (x5 : Exec Pr5 S) (i : Nat) :
    (simulate x5)[i].time = x5[i].time := sim_time i

theorem simulate_clock (x5 : Exec Pr5 S) (i : Nat) (q : Node) :
    (simulate x5)[i][q].clock = x5[i][q].clock := sim_clock i q

theorem sim_awake_iff {x5 : Exec Pr5 S} {i : Nat} {p : Node} :
    (simulate x5).Awake i p ↔ x5.Awake i p := by
  unfold Execution.Awake
  rw [simulate_time]

theorem sim_synchronizedClocks {x5 : Exec Pr5 S} (h : SynchronizedClocks x5) :
    SynchronizedClocks (simulate x5) := by
  intro i p hp
  rw [simulate_clock, simulate_time]
  exact h i p (sim_awake_iff.mp hp)

theorem sim_timeMonotone {x5 : Exec Pr5 S} (h : TimeMonotone x5) :
    TimeMonotone (simulate x5) := by
  intro i
  rw [simulate_time, simulate_time]
  exact h i

theorem sim_timeStepwise {x5 : Exec Pr5 S} (h : TimeStepwise x5) :
    TimeStepwise (simulate x5) := by
  intro i
  rw [simulate_time, simulate_time]
  exact h i

theorem sim_clocksSound {x5 : Exec Pr5 S} (h : ClocksSound x5) :
    ClocksSound (simulate x5) := by
  intro i p
  rw [simulate_clock, simulate_time]
  exact h i p

theorem sim_timeDiverges {x5 : Exec Pr5 S} (h : TimeDiverges x5) :
    TimeDiverges (simulate x5) := by
  intro r
  obtain ⟨i, hi⟩ := h r
  exact ⟨i, by rw [simulate_time]; exact hi⟩

theorem sim_diligent {x5 : Exec Pr5 S} (h : Diligent x5) :
    Diligent (simulate x5) := by
  intro r p ⟨i, hti, hawk⟩
  rw [simulate_time] at hti
  obtain ⟨j, htj, hlblj⟩ := h r p ⟨i, hti, sim_awake_iff.mp hawk⟩
  exact ⟨j, by rw [simulate_time]; exact htj, simLbl_tick_iff.mpr hlblj⟩

theorem sim_wakePrecedesTick {x5 : Exec Pr5 S} (h : WakePrecedesTick x5) :
    WakePrecedesTick (simulate x5) := by
  intro j p t hlbl hsleep
  rw [simulate_time] at hsleep
  obtain ⟨k, hkj, hlblk, htk⟩ := h j p t (simLbl_tick_iff.mp hlbl) hsleep
  refine ⟨k, hkj, simLbl_wake_iff.mpr hlblk, ?_⟩
  rw [simulate_time, simulate_time]
  exact htk

theorem sim_oneTickPerReading {x5 : Exec Pr5 S} (h : OneTickPerReading x5) :
    OneTickPerReading (simulate x5) := fun i j p t hi hj =>
  h i j p t (simLbl_tick_iff.mp hi) (simLbl_tick_iff.mp hj)

/-- `Synchrony` transfers: every simulated message is a table image, the original
    reaches every awake view, the image rides along, and the table has stabilized. -/
theorem sim_synchrony {x5 : Exec Pr5 S} (hone : OneTickPerReading x5)
    (hmc : S.MonotoneCorruption) (hah : S.AwakeHonest) (hmono : TimeMonotone x5)
    (hsyn : Synchrony 0 Q.delta x5) : Synchrony 0 Q.delta (simulate x5) := by
  intro i j p m2 hm2 htime hawake
  have hδ := Q.deltaPos
  rw [simulate_getElem] at hm2
  obtain ⟨m5, hm5, rfl⟩ := sent_covered hone hmc hah hmono i hm2
  rw [simulate_time, simulate_time] at htime
  have hij : i ≤ j := by
    by_contra hlt
    push_neg at hlt
    have := time_le_of_le hmono (le_of_lt hlt)
    simp only [ge_iff_le, max_eq_left (Nat.zero_le _)] at htime
    omega
  have hm5view : m5 ∈ (x5.cfg j)[p].view :=
    hsyn i j p m5 hm5 htime (sim_awake_iff.mp hawake)
  have himg := view_image hone hmc hah hmono j p hm5view
  rw [tau_stable hone hmc hah hmono hm5 hij] at himg
  exact himg

/-- `Relay` transfers, by the same route through the covered views. -/
theorem sim_relay {x5 : Exec Pr5 S} (hone : OneTickPerReading x5)
    (hmc : S.MonotoneCorruption) (hah : S.AwakeHonest) (hmono : TimeMonotone x5)
    (hrel : Relay 0 Q.delta x5) : Relay 0 Q.delta (simulate x5) := by
  intro i j p q m2 hawakei hm2 htime hawakej
  have hδ := Q.deltaPos
  rw [simulate_getElem] at hm2
  obtain ⟨m5, hm5, rfl⟩ := view_covered hone hmc hah hmono i p hm2
  rw [simulate_time, simulate_time] at htime
  have hij : i ≤ j := by
    by_contra hlt
    push_neg at hlt
    have := time_le_of_le hmono (le_of_lt hlt)
    simp only [ge_iff_le, max_eq_left (Nat.zero_le _)] at htime
    omega
  have hm5view : m5 ∈ (x5.cfg j)[q].view :=
    hrel i j p q m5 (sim_awake_iff.mp hawakei) hm5 htime (sim_awake_iff.mp hawakej)
  have himg := view_image hone hmc hah hmono j q hm5view
  rw [tau_stable hone hmc hah hmono
    (views_sound x5 i p m5 hm5) hij] at himg
  exact himg

/-- **The whole setting transfers**: the simulated run satisfies `SettingGA` whenever
    the original does — the schedule-level groups verbatim, the execution-level ones
    through the invariants above. Lemmas 2–7 now run on `simulate x5`. -/
theorem sim_settingGA {x5 : Exec Pr5 S} (H : SettingGA Q S x5) :
    SettingGA Q S (simulate x5) where
  wellformed :=
    ⟨H.wellformed.1, H.wellformed.2.1,
      sim_synchronizedClocks H.wellformed.2.2.1,
      sim_timeMonotone H.wellformed.2.2.2.1,
      sim_clocksSound H.wellformed.2.2.2.2.1,
      sim_timeDiverges H.wellformed.2.2.2.2.2.1,
      sim_diligent H.wellformed.2.2.2.2.2.2⟩
  stepwise := sim_timeStepwise H.stepwise
  wakePrecedesTick := sim_wakePrecedesTick H.wakePrecedesTick
  oneTick := sim_oneTickPerReading H.oneTick
  synchronous :=
    ⟨sim_synchrony H.oneTick H.wellformed.1 H.wellformed.2.1
        H.wellformed.2.2.2.1 H.synchronous.1,
      sim_relay H.oneTick H.wellformed.1 H.wellformed.2.1
        H.wellformed.2.2.2.1 H.synchronous.2⟩
  sleepiness := H.sleepiness
  resilience := H.resilience
  gstZero := H.gstZero

end Majorum
