import Examples.StsMultisetLog.majorum.Analysis.Proofs.Mfc

/-!
# Appendix B: the finality component's accountable safety

Lemmas 8 and 9 in full, plus their machinery. Everything here is **view-local counting**
— no executions, no schedule, no synchrony, no corruption bound: the `f ∈ [0, n]` regime
the accountable-safety analysis is proved in. The only quantitative input is that the
validator universe is no larger than the quorum denominator (`Fintype.card Node ≤ n`),
which the paper-facing statements discharge with the structural count.

The paper's minimality contradiction in Lemma 8 becomes a strong induction on the
justified checkpoint's slot; the three evidence sites (same-slot double justification,
the `cⱼ = c_f + 1` double vote, and the surround) all close through `slash_of_links`,
the quorum-intersection endgame.
-/

set_option autoImplicit false

namespace Majorum

open the framework's flat multiset-log flavour Classical

variable {Node Tx QC : Type} [DecidableEq Node] [DecidableEq Tx] [DecidableEq QC]

/-- **Two supermajorities share a third.** Over a universe of at most `n` validators,
    two sets counted at `2n/3` intersect in at least `n/3`. -/
theorem third_inter [Fintype Node] {n : Nat} (hcard : Fintype.card Node ≤ n)
    {A B : Finset Node} (hA : 2 * n ≤ 3 * A.card) (hB : 2 * n ≤ 3 * B.card) :
    n ≤ 3 * (A ∩ B).card := by
  have hsum := Finset.card_union_add_card_inter A B
  have hle := Finset.card_le_univ (A ∪ B)
  have huniv : (Finset.univ : Finset Node).card = Fintype.card Node := Finset.card_univ
  omega

/-- Justification is monotone in the view: a link's voters survive view growth. -/
theorem justifiedIn_mono {n : Nat} {V V' : View Node (Msg (Chain Tx) QC)}
    (hVV' : V ⊆ V') {C : Checkpoint (Chain Tx)} (h : JustifiedIn n V C) :
    JustifiedIn n V' C := by
  induction h with
  | genesis => exact .genesis
  | @link C₀ C₁ _ hlink ih =>
      refine .link ih ⟨hlink.1, hlink.2.1, le_trans hlink.2.2 ?_⟩
      have hsub : linkVoters V C₀ C₁ ⊆ linkVoters V' C₀ C₁ := by
        unfold linkVoters
        exact Finset.image_subset_image (Finset.filter_subset_filter _ (by
          unfold votes
          exact Finset.filter_subset_filter _ hVV'))
      have := Finset.card_le_card hsub
      omega

/-- The greatest justified checkpoint is justified: the fold starts at genesis and
    only ever adopts members of the justified-filtered set. -/
theorem gj_justified (n : Nat) (V : View Node (Msg (Chain Tx) QC)) :
    JustifiedIn n V (gj n V) := by
  unfold gj greatestBySlot
  have hfold : ∀ (l : List (Checkpoint (Chain Tx))) (b : Checkpoint (Chain Tx)),
      JustifiedIn n V b → (∀ C ∈ l, JustifiedIn n V C) →
      JustifiedIn n V
        (l.foldl (fun best C => if best.c ≤ C.c then C else best) b) := by
    intro l
    induction l with
    | nil =>
        intro b hb _
        exact hb
    | cons a l ih =>
        intro b hb hmem
        rw [List.foldl_cons]
        refine ih _ ?_ (fun C hC => hmem C (List.mem_cons_of_mem a hC))
        by_cases hle : b.c ≤ a.c
        · rw [if_pos hle]
          exact hmem a List.mem_cons_self
        · rw [if_neg hle]
          exact hb
  refine hfold _ _ .genesis ?_
  intro C hC
  exact (Finset.mem_filter.mp (Finset.mem_toList.mp hC)).2

/-- A link voter's fin-vote, extracted: a vote message in the view, signed by it, with
    exactly the link's endpoints. -/
theorem mem_linkVoters {V : View Node (Msg (Chain Tx) QC)}
    {C C' : Checkpoint (Chain Tx)} {w : Node} (h : w ∈ linkVoters V C C') :
    ∃ sm ∈ V, sm.sender = w ∧ ∃ (e : Chain Tx) (τ : Nat), sm.msg = .vote e C C' τ := by
  simp only [linkVoters, Finset.mem_image] at h
  obtain ⟨sm, hsm, rfl⟩ := h
  rw [Finset.mem_filter] at hsm
  obtain ⟨hv, hcond⟩ := hsm
  have hmemV : sm ∈ V := by
    simp only [votes, Finset.mem_filter] at hv
    exact hv.1
  refine ⟨sm, hmemV, rfl, ?_⟩
  cases hmsg : sm.msg with
  | vote e src tgt τ =>
      rw [hmsg] at hcond
      obtain ⟨rfl, rfl⟩ := hcond
      exact ⟨e, τ, rfl⟩
  | propose a b c d e =>
      rw [hmsg] at hcond
      exact absurd hcond not_false

/-- A source voter's fin-vote, extracted: a vote message in the view, signed by it, out of
    `C` into some target of slot `c` — the target being the voter's own choice. -/
theorem mem_sourceVoters {V : View Node (Msg (Chain Tx) QC)}
    {C : Checkpoint (Chain Tx)} {c : Nat} {w : Node} (h : w ∈ sourceVoters V C c) :
    ∃ sm ∈ V, sm.sender = w ∧ ∃ (e : Chain Tx) (tgt : Checkpoint (Chain Tx)) (τ : Nat),
      sm.msg = .vote e C tgt τ ∧ tgt.c = c ∧ C.ch ⪯ tgt.ch := by
  simp only [sourceVoters, Finset.mem_image] at h
  obtain ⟨sm, hsm, rfl⟩ := h
  rw [Finset.mem_filter] at hsm
  obtain ⟨hv, hcond⟩ := hsm
  have hmemV : sm ∈ V := by
    simp only [votes, Finset.mem_filter] at hv
    exact hv.1
  refine ⟨sm, hmemV, rfl, ?_⟩
  cases hmsg : sm.msg with
  | vote e src tgt τ =>
      rw [hmsg] at hcond
      obtain ⟨rfl, hc, hch⟩ := hcond
      exact ⟨e, tgt, τ, rfl, hc, hch⟩
  | propose a b c' d e =>
      rw [hmsg] at hcond
      exact absurd hcond not_false

/-- **The evidence endgame, with the finalization side counted by source**: a supermajority
    voting out of `C1` into slot `c` and a supermajority link `C3 → C4` put `n/3` validators
    on record, provided *every* admissible target of the first side violates a slashing
    condition against the second. The violation is therefore hypothesised parametrically in
    that target, which is what per-voter targets cost — and all it costs, since E1 and E2 read
    only the target's slot and the source pair. -/
theorem slash_of_source_link [Fintype Node] {n : Nat} (hcard : Fintype.card Node ≤ n)
    {V1 V2 : View Node (Msg (Chain Tx) QC)} {C1 C3 C4 : Checkpoint (Chain Tx)} {c : Nat}
    (hl1 : 2 * n ≤ 3 * (sourceVoters V1 C1 c).card)
    (hl2 : 2 * n ≤ 3 * (linkVoters V2 C3 C4).card)
    (hviol : ∀ C2 : Checkpoint (Chain Tx), C2.c = c → C1.ch ⪯ C2.ch →
      E1 C1 C2 C3 C4 ∨ E2 C1 C2 C3 C4) :
    ∃ W : Finset Node, n ≤ 3 * W.card ∧ ∀ w ∈ W, SlashableIn (V1 ∪ V2) w := by
  refine ⟨sourceVoters V1 C1 c ∩ linkVoters V2 C3 C4, third_inter hcard hl1 hl2, ?_⟩
  intro w hw
  obtain ⟨sm1, hsm1V, hs1, e1, tgt, τ1, hm1, htgtc, htgtch⟩ :=
    mem_sourceVoters (Finset.mem_inter.mp hw).1
  obtain ⟨sm2, hsm2V, hs2, e2, τ2, hm2⟩ := mem_linkVoters (Finset.mem_inter.mp hw).2
  exact ⟨sm1, Finset.mem_union_left _ hsm1V, sm2, Finset.mem_union_right _ hsm2V,
    hs1, hs2, e1, e2, C1, tgt, C3, C4, τ1, τ2, hm1, hm2, hviol tgt htgtc htgtch⟩

/-- **The evidence endgame**: two supermajority links whose fin-votes jointly violate a
    slashing condition put `n/3` validators on record — the intersection of the two
    quorums, each member holding both fin-votes. -/
theorem slash_of_links [Fintype Node] {n : Nat} (hcard : Fintype.card Node ≤ n)
    {V1 V2 : View Node (Msg (Chain Tx) QC)} {C1 C2 C3 C4 : Checkpoint (Chain Tx)}
    (hl1 : 2 * n ≤ 3 * (linkVoters V1 C1 C2).card)
    (hl2 : 2 * n ≤ 3 * (linkVoters V2 C3 C4).card)
    (hviol : E1 C1 C2 C3 C4 ∨ E2 C1 C2 C3 C4) :
    ∃ W : Finset Node, n ≤ 3 * W.card ∧ ∀ w ∈ W, SlashableIn (V1 ∪ V2) w := by
  refine ⟨linkVoters V1 C1 C2 ∩ linkVoters V2 C3 C4, third_inter hcard hl1 hl2, ?_⟩
  intro w hw
  obtain ⟨sm1, hsm1V, hs1, e1, τ1, hm1⟩ := mem_linkVoters (Finset.mem_inter.mp hw).1
  obtain ⟨sm2, hsm2V, hs2, e2, τ2, hm2⟩ := mem_linkVoters (Finset.mem_inter.mp hw).2
  exact ⟨sm1, Finset.mem_union_left _ hsm1V, sm2, Finset.mem_union_right _ hsm2V,
    hs1, hs2, e1, e2, C1, C2, C3, C4, τ1, τ2, hm1, hm2, hviol⟩

/-- At checkpoint slot `0` only genesis is justified: fin-vote validity forbids links
    into slot `0`. -/
theorem justified_counter_zero {n : Nat} {V : View Node (Msg (Chain Tx) QC)}
    {C : Checkpoint (Chain Tx)} (h : JustifiedIn n V C) (hc : C.c = 0) :
    C = ⟨[], 0⟩ := by
  cases h with
  | genesis => rfl
  | link hj hl =>
      have := hl.1
      omega

/-- **Double justification at one slot is `n/3`-slashable**: the two links into the
    slot share `n/3` voters, and their fin-votes differ in the target chain — E1. -/
theorem justified_same_counter_slash [Fintype Node] {n : Nat}
    (hcard : Fintype.card Node ≤ n) {V1 V2 : View Node (Msg (Chain Tx) QC)}
    {ch1 ch2 : Chain Tx} {c : Nat}
    (h1 : JustifiedIn n V1 ⟨ch1, c⟩) (h2 : JustifiedIn n V2 ⟨ch2, c⟩)
    (hne : ch1 ≠ ch2) :
    ∃ W : Finset Node, n ≤ 3 * W.card ∧ ∀ w ∈ W, SlashableIn (V1 ∪ V2) w := by
  cases h1 with
  | genesis =>
      -- `ch1 = []`, `c = 0`: the other justification is genesis too
      have h2z := justified_counter_zero h2 rfl
      exact absurd (congrArg Checkpoint.ch h2z).symm hne
  | link hj1 hl1 =>
      cases h2 with
      | genesis =>
          exact absurd hl1.1 (Nat.not_lt_zero _)
      | link hj2 hl2 =>
          refine slash_of_links hcard hl1.2.2 hl2.2.2 (Or.inl ⟨?_, rfl⟩)
          intro hpair
          exact hne (congrArg (fun p => (Prod.snd p).ch) hpair)

namespace Finality

variable [Fintype Node]

/-- **Lemma 8, in full** (`Lemma 8, arXiv:2601.03862v1 p.17`). Let `C_f = (ch_f, c_f)`
    be finalized and `C_j = (ch_j, c_j)` justified, `c_j ≥ c_f`, according to any two
    views. Either `ch_j ⪰ ch_f`, or at least `n/3` validators are slashable — with the
    evidence in the two views' union.

    The paper's "smallest counterexample slot" becomes a strong induction on `c_j`,
    with the justification chain unwound one link at a time:

    * `c_j = c_f`: double justification at one slot — E1 (`justified_same_counter_slash`).
    * the link into `(ch_j, c_j)` comes from a justified `(A, c_a)`:
      * `c_f ≤ c_a < c_j`: the induction hypothesis at `c_a` bounds `ch_f ⪯ A ⪯ ch_j`
        (the second step is fin-vote validity), a contradiction — or slashes.
      * `c_a < c_f` and `c_j = c_f + 1`: that link's fin-votes and the finalization
        link's target the same slot `c_f + 1` from different sources — E1.
      * `c_a < c_f` and `c_f + 1 < c_j`: the finalization link's fin-vote
        `(ch_f, c_f) → (·, c_f + 1)` is surrounded — E2. -/
theorem lemma8 {n : Nat} (hcard : Fintype.card Node ≤ n)
    {V1 V2 : View Node (Msg (Chain Tx) QC)} {chf chj : Chain Tx} {cf cj : Nat}
    (hfin : FinalizedIn n V1 ⟨chf, cf⟩) (hjust : JustifiedIn n V2 ⟨chj, cj⟩)
    (hcle : cf ≤ cj) :
    chf ⪯ chj ∨ ∃ W : Finset Node, n ≤ 3 * W.card ∧
      ∀ w ∈ W, SlashableIn (V1 ∪ V2) w := by
  suffices h : ∀ cj chj, cf ≤ cj → JustifiedIn n V2 ⟨chj, cj⟩ →
      (chf ⪯ chj) = true ∨ ∃ W : Finset Node, n ≤ 3 * W.card ∧
        ∀ w ∈ W, SlashableIn (V1 ∪ V2) w by
    exact h cj chj hcle hjust
  intro cj
  induction cj using Nat.strong_induction_on with
  | _ cj IH =>
  intro chj hcle hjust
  by_cases hle : (chf ⪯ chj : Bool)
  · exact Or.inl hle
  right
  cases hjust with
  | genesis =>
      -- `c_j = 0`, so `c_f = 0` and the finalized chain is genesis: `ch_f ⪯ []` after all
      exfalso
      have hz := justified_counter_zero hfin.1 (show cf = 0 by omega)
      have : chf = [] := congrArg Checkpoint.ch hz
      subst this
      exact hle (chainLe_refl [])
  | @link C₀ _ hjA hl =>
      obtain ⟨A, ca⟩ := C₀
      have hca : ca < cj := hl.1
      have hAchj : (A ⪯ chj : Bool) := hl.2.1
      rcases Nat.eq_or_lt_of_le hcle with heq | hcflt
      · -- `c_f = c_j`: double justification at one slot
        subst heq
        refine justified_same_counter_slash hcard hfin.1
          (JustifiedIn.link hjA hl) (fun h => ?_)
        subst h
        exact hle (chainLe_refl chf)
      · rcases Nat.lt_or_ge ca cf with hlt | hge
        · -- the link reaches below the finalized slot; the finalization side is counted by
          -- source, so the witness is parametric in each voter's own target
          rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hcflt) with heq1 | hlt1
          · -- `c_j = c_f + 1`: both sides target slot `c_f + 1` — E1
            refine slash_of_source_link hcard hfin.2 hl.2.2 ?_
            intro C2 hC2c _
            have hC2 : C2.c = cf + 1 := hC2c
            refine Or.inl ⟨?_, ?_⟩
            · intro hpair
              have : cf = ca := congrArg (fun p => (Prod.fst p).c) hpair
              omega
            · show C2.c = cj
              omega
          · -- `c_f + 1 < c_j`: the finalization fin-vote is surrounded — E2
            refine slash_of_source_link hcard hfin.2 hl.2.2 ?_
            intro C2 hC2c _
            have hC2 : C2.c = cf + 1 := hC2c
            refine Or.inr ⟨hlt, ?_, ?_⟩
            · show cf < C2.c
              omega
            · show C2.c < cj
              omega
        · -- `c_f ≤ c_a < c_j`: the induction hypothesis bounds the source
          rcases IH ca hca A hge hjA with hfA | hslash
          · exfalso
            exact hle (chainLe_trans hfA hAchj)
          · exact hslash

/-- **Lemma 9, in full** (`Lemma 9, arXiv:2601.03862v1 p.18`). Two conflicting chains
    finalized according to any two views put `n/3` validators on record: finalization
    implies justification, Lemma 8 makes the finalized checkpoints' chains nested, and
    two prefixes of one chain cannot conflict. -/
theorem lemma9 {n : Nat} (hcard : Fintype.card Node ≤ n)
    {V1 V2 : View Node (Msg (Chain Tx) QC)} {ch1 ch2 ch1' ch2' : Chain Tx}
    {c1 c2 : Nat}
    (h1 : FinalizedIn n V1 ⟨ch1', c1⟩) (h1le : ch1 ⪯ ch1')
    (h2 : FinalizedIn n V2 ⟨ch2', c2⟩) (h2le : ch2 ⪯ ch2')
    (hc12 : ¬ (ch1 ⪯ ch2 : Bool)) (hc21 : ¬ (ch2 ⪯ ch1 : Bool)) :
    ∃ W : Finset Node, n ≤ 3 * W.card ∧ ∀ w ∈ W, SlashableIn (V1 ∪ V2) w := by
  rcases Nat.le_total c1 c2 with hc | hc
  · rcases lemma8 hcard h1 h2.1 hc with hpre | hslash
    · exfalso
      have h1le' : (ch1 ⪯ ch2' : Bool) := chainLe_trans h1le hpre
      rcases comparable_of_common_extension h1le' h2le with h | h
      · exact hc12 h
      · exact hc21 h
    · exact hslash
  · rcases lemma8 hcard h2 h1.1 hc with hpre | hslash
    · exfalso
      have h2le' : (ch2 ⪯ ch1' : Bool) := chainLe_trans h2le hpre
      rcases comparable_of_common_extension h2le' h1le with h | h
      · exact hc21 h
      · exact hc12 h
    · rw [Finset.union_comm] at hslash
      exact hslash

end Finality

end Majorum
