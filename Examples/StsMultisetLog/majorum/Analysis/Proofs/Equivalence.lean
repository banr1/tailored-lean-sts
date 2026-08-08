import Examples.StsMultisetLog.majorum.Analysis.Proofs.Simulation

/-!
# Skeleton congruences for dynamic equivalence (Lemma 10, stage C1)

Definition 8's dynamic equivalence preserves exactly the **vote skeleton** — signer,
chain, slot — and every function of the fork-choice layer factors through it: the
filters' survival conditions, `voters`, `candidates`, `fastconfirmsimple`, the
`Majority` test and `MFC` read nothing else. This file proves that factoring, so that
stage C's slot induction can replace "the views are dynamically equivalent" by "the
skeletons are equal" and conclude that both executions compute the same fork choice.

The one delicate point is `Majority`'s numerator: it intersects two views'
`votesFor` **as message sets**, which dynamic equivalence does not preserve — but at
every call site the first view is a frozen snapshot of the second, and under that
subset hypothesis a sender is in the numerator iff some skeleton triple survives both
views' (skeleton-expressible) filters, which transfers.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 400

namespace Majorum

open Framework.StsMultisetLog Classical

variable {Node Tx : Type} [DecidableEq Node] [DecidableEq Tx]

local notation "M" => Msg (Chain Tx) (QCert Node Tx)

/-- Signed dynamic equivalence: same signer, dynamically equivalent payloads. -/
def SDynEq (sm sm' : SignedMsg Node M) : Prop :=
  sm.sender = sm'.sender ∧ DynEq sm.msg sm'.msg

/-- **Definition 8's set form**: every message has a dynamically equivalent counterpart,
    both ways. -/
def ViewCorr (V5 V2 : View Node M) : Prop :=
  (∀ sm ∈ V5, ∃ sm' ∈ V2, SDynEq sm sm') ∧ (∀ sm' ∈ V2, ∃ sm ∈ V5, SDynEq sm sm')

/-- A view's **vote skeleton**: the (signer, chain, slot) triples of its votes —
    everything the fork-choice layer reads. -/
noncomputable def voteSkel (V : View Node M) : Finset (Node × Chain Tx × Nat) :=
  (votes V).image (fun sm => (sm.sender, msgChain sm.msg, msgSlot sm.msg))

theorem mem_voteSkel {V : View Node M} {q : Node} {c : Chain Tx} {s : Nat} :
    (q, c, s) ∈ voteSkel V ↔ ∃ sm ∈ votes V,
      sm.sender = q ∧ msgChain sm.msg = c ∧ msgSlot sm.msg = s := by
  simp only [voteSkel, Finset.mem_image, Prod.mk.injEq]

/-- Dynamic equivalence is symmetric. -/
theorem DynEq.symm {m m' : M} (h : DynEq m m') : DynEq m' m := by
  cases m with
  | vote e src tgt s =>
      cases m' with
      | vote e' src' tgt' s' =>
          obtain ⟨h1, h2⟩ := h
          exact ⟨h1.symm, h2.symm⟩
      | propose a b c d e2 => cases h
  | propose chp chC qc gj s =>
      cases m' with
      | vote e' src' tgt' s' => cases h
      | propose chp' chC' qc' gj' s' =>
          obtain ⟨h1, h2⟩ := h
          exact ⟨h1.symm, h2.symm⟩

/-- So is its signed form. -/
theorem SDynEq.symm {sm sm' : SignedMsg Node M} (h : SDynEq sm sm') : SDynEq sm' sm :=
  ⟨h.1.symm, h.2.symm⟩

/-- Votes correspond to votes, with the same skeleton. -/
theorem SDynEq.vote_skel {sm sm' : SignedMsg Node M} (h : SDynEq sm sm')
    {e : Chain Tx} {src tgt : Checkpoint (Chain Tx)} {s : Nat}
    (hm : sm.msg = .vote e src tgt s) :
    ∃ src' tgt', sm'.msg = .vote e src' tgt' s ∧ sm'.sender = sm.sender := by
  obtain ⟨hs, hd⟩ := h
  cases hm' : sm'.msg with
  | vote e' src' tgt' s' =>
      rw [hm, hm'] at hd
      obtain ⟨rfl, rfl⟩ := hd
      exact ⟨src', tgt', rfl, hs.symm⟩
  | propose a b c d e2 =>
      rw [hm, hm'] at hd
      cases hd

/-- Dynamic equivalence of views equalizes their vote skeletons. -/
theorem voteSkel_eq_of_corr {V5 V2 : View Node M} (h : ViewCorr V5 V2) :
    voteSkel V5 = voteSkel V2 := by
  ext ⟨q, c, s⟩
  simp only [mem_voteSkel]
  constructor
  · rintro ⟨sm, hsm, rfl, rfl, rfl⟩
    have hv : sm ∈ V5 := by
      simp only [votes, Finset.mem_filter] at hsm
      exact hsm.1
    obtain ⟨e, src, tgt, s0, hm⟩ := exists_vote_of_mem_votes hsm
    obtain ⟨sm', hsm', hsd⟩ := h.1 sm hv
    obtain ⟨src', tgt', hm', hsend⟩ := hsd.vote_skel hm
    refine ⟨sm', ?_, hsend.symm ▸ rfl, ?_, ?_⟩
    · simp only [votes, Finset.mem_filter]
      exact ⟨hsm', by rw [hm']; trivial⟩
    · rw [hm', hm]
      rfl
    · rw [hm', hm]
      rfl
  · rintro ⟨sm', hsm', rfl, rfl, rfl⟩
    have hv : sm' ∈ V2 := by
      simp only [votes, Finset.mem_filter] at hsm'
      exact hsm'.1
    obtain ⟨e, src, tgt, s0, hm'⟩ := exists_vote_of_mem_votes hsm'
    obtain ⟨sm, hsm, hsd⟩ := h.2 sm' hv
    obtain ⟨src', tgt', hm, hsend⟩ := hsd.symm.vote_skel hm'
    refine ⟨sm, ?_, hsend.symm ▸ rfl, ?_, ?_⟩
    · simp only [votes, Finset.mem_filter]
      exact ⟨hsm, by rw [hm]; trivial⟩
    · rw [hm, hm']
      rfl
    · rw [hm, hm']
      rfl

/-! ### The fork-choice layer factors through the skeleton -/

/-- After `FIL_1-exp` every surviving slot is `t − 1`, so `FIL_lmd` keeps everything:
    there is nothing later to defer to. -/
theorem filLmd_fil1Exp {QC : Type} [DecidableEq QC]
    (W : Finset (SignedMsg Node (Msg (Chain Tx) QC))) (t : Nat) :
    filLmd (fil1Exp W t) = fil1Exp W t := by
  refine Finset.filter_true_of_mem ?_
  intro sm hsm
  rintro ⟨sm', hsm', -, hlt⟩
  have h1 : t = msgSlot sm.msg + 1 := (Finset.mem_filter.mp hsm).2
  have h2 : t = msgSlot sm'.msg + 1 := (Finset.mem_filter.mp hsm').2
  omega

/-- `votesFor`, characterized on the skeleton: a vote of the expiring slot whose sender
    has exactly one chain there, extending `ch`. -/
theorem mem_votesFor_skel {V : View Node M} {ch : Chain Tx} {t : Nat}
    {sm : SignedMsg Node M} :
    sm ∈ votesFor V ch t ↔
      sm ∈ votes V ∧ t = msgSlot sm.msg + 1 ∧
      (∀ c', (sm.sender, c', msgSlot sm.msg) ∈ voteSkel V → c' = msgChain sm.msg) ∧
      chainLe ch (msgChain sm.msg) := by
  unfold votesFor
  rw [filLmd_fil1Exp]
  simp only [fil1Exp, filEq, Finset.mem_filter]
  constructor
  · rintro ⟨⟨⟨hv, hneq⟩, hslot⟩, hch⟩
    refine ⟨hv, hslot, ?_, hch⟩
    intro c' hc'
    obtain ⟨sm', hsm', hs', hc'', hslot'⟩ := mem_voteSkel.mp hc'
    by_contra hne
    exact hneq ⟨sm', hsm', hs', hslot', by rw [hc'']; exact hne⟩
  · rintro ⟨hv, hslot, huniq, hch⟩
    refine ⟨⟨⟨hv, ?_⟩, hslot⟩, hch⟩
    rintro ⟨sm', hsm', hs', hslot', hne⟩
    exact hne (huniq (msgChain sm'.msg)
      (mem_voteSkel.mpr ⟨sm', hsm', hs', rfl, hslot'⟩) ▸ rfl)

/-- `Majority`'s numerator, characterized on the two skeletons — under the call sites'
    subset discipline (the first view is a snapshot of the second), a sender is counted
    iff some triple of the smaller skeleton survives both views' filters. -/
theorem numerator_skel {Va Vb : View Node M} (hsub : Va ⊆ Vb) (ch : Chain Tx) (t : Nat) :
    (votesFor Va ch t ∩ votesFor Vb ch t).image SignedMsg.sender
    = ((voteSkel Va).filter (fun tr => t = tr.2.2 + 1 ∧
        (∀ c', (tr.1, c', tr.2.2) ∈ voteSkel Va → c' = tr.2.1) ∧
        (∀ c', (tr.1, c', tr.2.2) ∈ voteSkel Vb → c' = tr.2.1) ∧
        chainLe ch tr.2.1)).image Prod.fst := by
  ext q
  simp only [Finset.mem_image, Finset.mem_inter, Finset.mem_filter]
  constructor
  · rintro ⟨sm, ⟨ha, hb⟩, rfl⟩
    obtain ⟨hva, hslot, huna, hch⟩ := mem_votesFor_skel.mp ha
    obtain ⟨hvb, -, hunb, -⟩ := mem_votesFor_skel.mp hb
    refine ⟨(sm.sender, msgChain sm.msg, msgSlot sm.msg),
      ⟨mem_voteSkel.mpr ⟨sm, hva, rfl, rfl, rfl⟩, hslot, huna, hunb, hch⟩, rfl⟩
  · rintro ⟨⟨q', c, s⟩, ⟨htr, hslot, huna, hunb, hch⟩, rfl⟩
    dsimp only at hslot huna hunb hch
    obtain ⟨sm, hva, hs, hc, hs'⟩ := mem_voteSkel.mp htr
    have hmemVa : sm ∈ Va := by
      simp only [votes, Finset.mem_filter] at hva
      exact hva.1
    have hvb : sm ∈ votes Vb := by
      simp only [votes, Finset.mem_filter] at hva ⊢
      exact ⟨hsub hva.1, hva.2⟩
    refine ⟨sm, ⟨?_, ?_⟩, hs⟩
    · refine mem_votesFor_skel.mpr ⟨hva, by omega, ?_, ?_⟩
      · intro c' hc'
        rw [hs, hs'] at hc'
        rw [hc]
        exact huna c' hc'
      · rw [hc]
        exact hch
    · refine mem_votesFor_skel.mpr ⟨hvb, by omega, ?_, ?_⟩
      · intro c' hc'
        rw [hs, hs'] at hc'
        rw [hc]
        exact hunb c' hc'
      · rw [hc]
        exact hch

/-- `voters`, on the skeleton. -/
theorem voters_skel (V : View Node M) (t : Nat) :
    voters V t
    = ((voteSkel V).filter (fun tr => t = tr.2.2 + 1)).image Prod.fst := by
  ext q
  simp only [voters, fil1Exp, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨sm, ⟨hv, hslot⟩, rfl⟩
    exact ⟨(sm.sender, msgChain sm.msg, msgSlot sm.msg),
      ⟨mem_voteSkel.mpr ⟨sm, hv, rfl, rfl, rfl⟩, hslot⟩, rfl⟩
  · rintro ⟨⟨q', c, s⟩, ⟨htr, hslot⟩, rfl⟩
    dsimp only at hslot
    obtain ⟨sm, hv, hs, -, hs'⟩ := mem_voteSkel.mp htr
    exact ⟨sm, ⟨hv, by omega⟩, hs⟩

/-- **`Majority` transfers across skeleton-equal view pairs** (with the call sites'
    snapshot discipline on both sides). -/
theorem Majority_congr {Va5 Vb5 Va2 Vb2 : View Node M}
    (ha : voteSkel Va5 = voteSkel Va2) (hb : voteSkel Vb5 = voteSkel Vb2)
    (hsub5 : Va5 ⊆ Vb5) (hsub2 : Va2 ⊆ Vb2) (t : Nat) (ch : Chain Tx) :
    Majority Va5 Vb5 t ch ↔ Majority Va2 Vb2 t ch := by
  unfold Majority
  rw [numerator_skel hsub5, numerator_skel hsub2, voters_skel, voters_skel, ha, hb]

/-- `candidates`, on the skeleton. -/
theorem candidates_skel (V : View Node M) (b : Chain Tx) :
    candidates V b
    = insert b ((voteSkel V).biUnion (fun tr => tr.2.1.inits.toFinset)) := by
  unfold candidates voteSkel
  rw [Finset.image_biUnion]

/-- `fastconfirmsimple`'s support count, on the skeleton. -/
theorem support_skel (V : View Node M) (t : Nat) (ch : Chain Tx) :
    ((votes V).filter (fun sm => msgSlot sm.msg = t ∧
      chainLe ch (msgChain sm.msg))).image SignedMsg.sender
    = ((voteSkel V).filter (fun tr => tr.2.2 = t ∧ chainLe ch tr.2.1)).image Prod.fst := by
  ext q
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨sm, ⟨hv, hslot, hch⟩, rfl⟩
    exact ⟨(sm.sender, msgChain sm.msg, msgSlot sm.msg),
      ⟨mem_voteSkel.mpr ⟨sm, hv, rfl, rfl, rfl⟩, hslot, hch⟩, rfl⟩
  · rintro ⟨⟨q', c, s⟩, ⟨htr, hslot, hch⟩, rfl⟩
    dsimp only at hslot hch
    obtain ⟨sm, hv, hs, hc, hs'⟩ := mem_voteSkel.mp htr
    exact ⟨sm, ⟨hv, by rw [hs', hslot], by rw [hc]; exact hch⟩, hs⟩

/-- `fastconfirmsimple`'s certificate, on the skeleton. -/
theorem qcert_skel (V : View Node M) (t : Nat) (ch : Chain Tx) :
    ((votes V).filter (fun sm => msgSlot sm.msg = t ∧
      chainLe ch (msgChain sm.msg))).image
        (fun sm => (sm.sender, msgChain sm.msg, msgSlot sm.msg))
    = (voteSkel V).filter (fun tr => tr.2.2 = t ∧ chainLe ch tr.2.1) := by
  ext ⟨q, c, s⟩
  simp only [Finset.mem_image, Finset.mem_filter, Prod.mk.injEq]
  constructor
  · rintro ⟨sm, ⟨hv, hslot, hch⟩, rfl, rfl, rfl⟩
    exact ⟨mem_voteSkel.mpr ⟨sm, hv, rfl, rfl, rfl⟩, hslot, hch⟩
  · rintro ⟨htr, hslot, hch⟩
    obtain ⟨sm, hv, hs, hc, hs'⟩ := mem_voteSkel.mp htr
    exact ⟨sm, ⟨hv, by rw [hs', hslot], by rw [hc]; exact hch⟩, hs, hc, hs'⟩

set_option maxHeartbeats 2000000 in
/-- **`fastconfirmsimple` transfers across skeleton-equal views** — output chain *and*
    certificate. -/
theorem fastConfirmSimple_congr {V5 V2 : View Node M}
    (h : voteSkel V5 = voteSkel V2) (n t : Nat) :
    fastConfirmSimple n V5 t = fastConfirmSimple n V2 t := by
  simp only [fastConfirmSimple]
  have hsup : ∀ ch : Chain Tx,
      ((votes V5).filter (fun sm => msgSlot sm.msg = t ∧
        chainLe ch (msgChain sm.msg))).image SignedMsg.sender
      = ((votes V2).filter (fun sm => msgSlot sm.msg = t ∧
        chainLe ch (msgChain sm.msg))).image SignedMsg.sender := by
    intro ch
    rw [support_skel, support_skel, h]
  have hcands : (candidates V5 ([] : Chain Tx)).filter
        (fun ch => 2 * n ≤ 3 * (((votes V5).filter (fun sm => msgSlot sm.msg = t ∧
          chainLe ch (msgChain sm.msg))).image SignedMsg.sender).card)
      = (candidates V2 ([] : Chain Tx)).filter
        (fun ch => 2 * n ≤ 3 * (((votes V2).filter (fun sm => msgSlot sm.msg = t ∧
          chainLe ch (msgChain sm.msg))).image SignedMsg.sender).card) := by
    rw [candidates_skel, candidates_skel, h]
    refine Finset.filter_congr ?_
    intro ch _
    rw [hsup ch]
  rw [hcands]
  have hqc : ∀ ch : Chain Tx,
      ((votes V5).filter (fun sm => msgSlot sm.msg = t ∧
        chainLe ch (msgChain sm.msg))).image
          (fun sm => (sm.sender, msgChain sm.msg, msgSlot sm.msg))
      = ((votes V2).filter (fun sm => msgSlot sm.msg = t ∧
        chainLe ch (msgChain sm.msg))).image
          (fun sm => (sm.sender, msgChain sm.msg, msgSlot sm.msg)) := by
    intro ch
    rw [qcert_skel, qcert_skel, h]
  simp only [hqc]

/-- The `MFC` fold, congruent in its majority test — the predicate kept abstract so
    that neither the elaborator nor the kernel ever unfolds `Majority`'s counting. -/
theorem foldl_mfc_congr {P P' : Chain Tx → Prop} [DecidablePred P] [DecidablePred P']
    (hPP : ∀ ch, P ch ↔ P' ch) (b : Chain Tx) :
    ∀ (l : List (Chain Tx)) (best : Chain Tx),
      l.foldl (fun best ch =>
        if chainLe b ch ∧ P ch ∧ best.length < ch.length then ch else best) best
      = l.foldl (fun best ch =>
        if chainLe b ch ∧ P' ch ∧ best.length < ch.length then ch else best) best := by
  intro l
  induction l with
  | nil => intro best; rfl
  | cons a l ih =>
      intro best
      rw [List.foldl_cons, List.foldl_cons]
      by_cases hm : P a
      · by_cases hrest : chainLe b a ∧ best.length < a.length
        · rw [if_pos ⟨hrest.1, hm, hrest.2⟩, if_pos ⟨hrest.1, (hPP a).mp hm, hrest.2⟩]
          exact ih a
        · rw [if_neg (fun hh => hrest ⟨hh.1, hh.2.2⟩),
            if_neg (fun hh => hrest ⟨hh.1, hh.2.2⟩)]
          exact ih best
      · rw [if_neg (fun hh => hm hh.2.1),
          if_neg (fun hh => hm ((hPP a).mpr hh.2.1))]
        exact ih best

/-- **`MFC` transfers across skeleton-equal view pairs**, base fixed. -/
theorem mfc_congr {Va5 Vb5 Va2 Vb2 : View Node M}
    (ha : voteSkel Va5 = voteSkel Va2) (hb : voteSkel Vb5 = voteSkel Vb2)
    (hsub5 : Va5 ⊆ Vb5) (hsub2 : Va2 ⊆ Vb2) (b : Chain Tx) (t : Nat) :
    mfc Va5 Vb5 b t = mfc Va2 Vb2 b t := by
  have hc : candidates Va5 b = candidates Va2 b := by
    rw [candidates_skel, candidates_skel, ha]
  unfold mfc
  rw [hc]
  exact foldl_mfc_congr (fun ch => Majority_congr ha hb hsub5 hsub2 t ch) b _ b

end Majorum
