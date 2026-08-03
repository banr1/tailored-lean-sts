import Examples.StsMultisetLog.majorum.Components

/-!
# The view-local layer: vote filters, majorities, and `MFC`

Helper theorems about views — no executions, no paper-numbered lemma. Per this directory's
convention, theorems corresponding one-to-one to the paper's numbered lemmas live in
`Lemmas.lean`; this file (and `Provenance.lean` for the execution layer) is where their
supporting material goes.

Most of what is here serves **Lemma 2**: if every validator in `H_{vote(t)}` votes in slot
`t` for a chain extending `ch`, then `MFC ⪰ ch` at every honest validator a slot later, and
the votes repeat. Its view-local content:

**Where this stands** (2026-08-03). The model defects that had made Lemma 2 false are
fixed — `candidates` is prefix-closed, `Majority` counts senders, the handler implements
the joining protocol — and `OneTickPerReading` exists in `Assumptions.lean`; only
`validProposal`'s certificate check stays deferred to the vote-round half. On top of the
fixes, the view-local layer is now complete and hypothesis-light:

* **Case 2** ("by definition `MFC ⪰ chfrozen`") — `base_le_mfc`.
* **Case 1's conclusion** — `le_mfc_of_majority`: majority alone gives `MFC ⪰ ch`, since a
  majority chain is automatically a candidate (`mem_candidates_of_majority`) and any two
  majority chains are comparable through a common supporter (`majority_comparable`, whose
  linchpin is `chain_eq_of_same_sender`: after `FIL_eq` and `FIL_lmd`, one sender has one
  chain).
* **Case 1's counting** — `voters_lt_two_mul_honest`, the paper's displayed inequality
  chain.

What remains for the propose-round half is the execution layer: provenance (an honest
validator's votes in any view came from its vote-phase ticks — adversarial injection under
that signature is excluded up to `voting(t+1)` by `MonotoneCorruption`), the containment of
`S(V_i, t+1)` in `(H_{vote(t)} \ A_{vote(t+1)}) ∪ A_{vote(t+1)}`, and their assembly. The
vote-round half additionally needs the `chfrozen` comparability invariant through `merge`
and `processProposals`. See `CONTEXT.md`.
-/

set_option autoImplicit false

namespace Majorum

open the framework's flat multiset-log flavour

variable {Node Tx QC : Type} [DecidableEq Node] [DecidableEq Tx] [DecidableEq QC]

/-- **Quorum intersection.** Two subsets of a pool, each holding more than half of it, share
    a member. The `2 * card` spelling avoids dividing, as in `mfc`. -/
theorem quorum_inter {S A B : Finset Node} (hA : A ⊆ S) (hB : B ⊆ S)
    (ha : S.card < 2 * A.card) (hb : S.card < 2 * B.card) : (A ∩ B).Nonempty := by
  rw [← Finset.card_pos]
  have hunion : (A ∪ B).card ≤ S.card := Finset.card_le_card (Finset.union_subset hA hB)
  have hsum : (A ∪ B).card + (A ∩ B).card = A.card + B.card :=
    Finset.card_union_add_card_inter A B
  omega

/-- Chains that a common chain extends are comparable — the prefix order is a tree order, so
    two prefixes of one chain are nested. -/
theorem comparable_of_common_extension {a b c : Chain Tx}
    (ha : chainLe a c) (hb : chainLe b c) : chainLe a b ∨ chainLe b a := by
  simp only [chainLe, List.isPrefixOf_iff_prefix] at ha hb ⊢
  exact List.prefix_or_prefix_of_prefix ha hb

/-- `chainLe` unfolded to Mathlib's prefix order. -/
theorem chainLe_iff_prefix {a b : Chain Tx} : chainLe a b ↔ a <+: b := by
  simp [chainLe, List.isPrefixOf_iff_prefix]

/-! ### Reading the vote filters

Small extraction lemmas, plus the one structural fact the comparability argument turns on:
after `FIL_eq` and `FIL_lmd`, **one sender has one chain** — a sender's surviving votes all
carry its maximal slot (`FIL_lmd`), and same-slot votes with different chains were both
removed (`FIL_eq`). -/

theorem votesFor_subset_filtered (V : View Node (Msg (Chain Tx) QC)) (ch : Chain Tx)
    (t : Nat) : votesFor V ch t ⊆ filLmd (fil1Exp (filEq V) t) := by
  intro sm h
  simp only [votesFor, Finset.mem_filter] at h
  exact h.1

theorem votesFor_subset_votes (V : View Node (Msg (Chain Tx) QC)) (ch : Chain Tx)
    (t : Nat) : votesFor V ch t ⊆ votes V := by
  intro sm h
  simp only [votesFor, filLmd, fil1Exp, filEq, Finset.mem_filter] at h
  exact h.1.1.1.1

theorem votesFor_extends {V : View Node (Msg (Chain Tx) QC)} {ch : Chain Tx} {t : Nat}
    {sm : SignedMsg Node (Msg (Chain Tx) QC)} (h : sm ∈ votesFor V ch t) :
    chainLe ch (msgChain sm.msg) := by
  simp only [votesFor, Finset.mem_filter] at h
  exact h.2

/-- A supporter is a voter: its message is a vote in the view with a non-expired slot. -/
theorem sender_mem_voters {V : View Node (Msg (Chain Tx) QC)} {ch : Chain Tx} {t : Nat}
    {sm : SignedMsg Node (Msg (Chain Tx) QC)} (h : sm ∈ votesFor V ch t) :
    sm.sender ∈ voters V t := by
  simp only [votesFor, filLmd, fil1Exp, filEq, Finset.mem_filter] at h
  obtain ⟨⟨⟨⟨hv, -⟩, hexp⟩, -⟩, -⟩ := h
  simp only [voters, fil1Exp, Finset.mem_image]
  exact ⟨sm, Finset.mem_filter.2 ⟨hv, hexp⟩, rfl⟩

/-- One sender, one chain, after the filters. -/
theorem chain_eq_of_same_sender {V : View Node (Msg (Chain Tx) QC)} {t : Nat}
    {m m' : SignedMsg Node (Msg (Chain Tx) QC)}
    (hm : m ∈ filLmd (fil1Exp (filEq V) t)) (hm' : m' ∈ filLmd (fil1Exp (filEq V) t))
    (hs : m'.sender = m.sender) : msgChain m'.msg = msgChain m.msg := by
  simp only [filLmd, Finset.mem_filter] at hm hm'
  obtain ⟨hmS, hmlmd⟩ := hm
  obtain ⟨hm'S, hm'lmd⟩ := hm'
  -- equal slots: each forbids a strictly later same-sender vote in the filtered set
  have h1 : ¬ msgSlot m.msg < msgSlot m'.msg := fun hlt => hmlmd ⟨m', hm'S, hs, hlt⟩
  have h2 : ¬ msgSlot m'.msg < msgSlot m.msg := fun hlt => hm'lmd ⟨m, hmS, hs.symm, hlt⟩
  have hslot : msgSlot m'.msg = msgSlot m.msg := by omega
  -- equal chains: otherwise `m'` witnesses `m`'s equivocation clause in `FIL_eq`
  simp only [fil1Exp, Finset.mem_filter] at hmS hm'S
  simp only [filEq, Finset.mem_filter] at hmS hm'S
  by_contra hne
  exact hmS.1.2 ⟨m', hm'S.1.1, hs, hslot, hne⟩

/-- **Any two majority-supported chains are comparable** — the intersection of two strict
    sender-majorities of `S(V', t)` is inhabited, and the common supporter's single
    post-filter chain extends both. This is what makes `mfc`'s "the longest chain such
    that …" a definite description rather than a choice among incomparable options. -/
theorem majority_comparable {V V' : View Node (Msg (Chain Tx) QC)} {t : Nat}
    {a b : Chain Tx} (ha : Majority V V' t a) (hb : Majority V V' t b) :
    chainLe a b ∨ chainLe b a := by
  have hsub : ∀ c : Chain Tx,
      ((votesFor V c t ∩ votesFor V' c t).image SignedMsg.sender) ⊆ voters V' t := by
    intro c q hq
    obtain ⟨sm, hsm, rfl⟩ := Finset.mem_image.1 hq
    exact sender_mem_voters (Finset.mem_inter.1 hsm).2
  obtain ⟨q, hq⟩ := quorum_inter (hsub a) (hsub b) ha hb
  rw [Finset.mem_inter] at hq
  obtain ⟨sma, hsma, hqa⟩ := Finset.mem_image.1 hq.1
  obtain ⟨smb, hsmb, hqb⟩ := Finset.mem_image.1 hq.2
  have hma : sma ∈ votesFor V' a t := (Finset.mem_inter.1 hsma).2
  have hmb : smb ∈ votesFor V' b t := (Finset.mem_inter.1 hsmb).2
  have hchain : msgChain smb.msg = msgChain sma.msg :=
    chain_eq_of_same_sender (votesFor_subset_filtered V' a t hma)
      (votesFor_subset_filtered V' b t hmb) (by rw [hqb, hqa])
  exact comparable_of_common_extension (votesFor_extends hma)
    (hchain ▸ votesFor_extends hmb)

/-- **A chain some vote extends is a candidate** — the prefix closure of `candidates`,
    on its own. -/
theorem mem_candidates_of_extends {V : View Node (Msg (Chain Tx) QC)} {b ch : Chain Tx}
    {sm : SignedMsg Node (Msg (Chain Tx) QC)} (hv : sm ∈ votes V)
    (hle : chainLe ch (msgChain sm.msg)) : ch ∈ candidates V b := by
  simp only [candidates, Finset.mem_insert, Finset.mem_biUnion]
  exact Or.inr ⟨sm, hv, List.mem_toFinset.2 ((List.mem_inits _ _).2 (chainLe_iff_prefix.1 hle))⟩

/-- **A majority chain is a candidate**: a strict majority forces at least one supporting
    vote, and a chain some vote extends is among that vote's prefixes — which is where the
    prefix closure of `candidates` earns its place. -/
theorem mem_candidates_of_majority {V V' : View Node (Msg (Chain Tx) QC)} {chC : Chain Tx}
    {t : Nat} {ch : Chain Tx} (h : Majority V V' t ch) : ch ∈ candidates V chC := by
  have hne : ((votesFor V ch t ∩ votesFor V' ch t).image SignedMsg.sender).Nonempty := by
    rw [← Finset.card_pos]
    omega
  obtain ⟨q, hq⟩ := hne
  obtain ⟨sm, hsm, -⟩ := Finset.mem_image.1 hq
  have hv : sm ∈ votes V := votesFor_subset_votes V ch t (Finset.mem_inter.1 hsm).1
  have hle : chainLe ch (msgChain sm.msg) := votesFor_extends (Finset.mem_inter.1 hsm).1
  simp only [candidates, Finset.mem_insert, Finset.mem_biUnion]
  exact Or.inr ⟨sm, hv, List.mem_toFinset.2 ((List.mem_inits _ _).2 (chainLe_iff_prefix.1 hle))⟩

/-! ### Case 2 of the paper's proof

"Given that by definition `MFC^{propose(t+1)}_i ⪰ chfrozen`, we have `MFC ⪰ ch`." That is a
property of `mfc` and nothing else, so it is provable here in full. -/

/-- Fold invariant, in the form the two `mfc` lemmas need. -/
private theorem foldl_invariant {α β : Type} (P : β → Prop) (f : β → α → β) :
    ∀ (l : List α) (b : β), P b → (∀ b a, P b → P (f b a)) → P (l.foldl f b)
  | [], _, hb, _ => hb
  | x :: xs, b, hb, hf => foldl_invariant P f xs (f b x) (hf b x hb) hf

/-- `chainLe` is reflexive. -/
theorem chainLe_refl (a : Chain Tx) : chainLe a a := by
  simp [chainLe]

/-- **`MFC(V, V', chC, t) ⪰ chC`.** The fork-choice never returns something that fails to
    extend its base, because the fold only ever moves to a candidate that does.

    This is Case 2 of Lemma 2's proof for both `MFC^{propose(t+1)}` and `MFC^{vote(t+1)}`:
    once `chfrozen ⪰ ch`, the conclusion is immediate. -/
theorem base_le_mfc (V V' : View Node (Msg (Chain Tx) QC)) (chC : Chain Tx) (t : Nat) :
    chainLe chC (mfc V V' chC t) := by
  unfold mfc
  refine foldl_invariant (fun b => chainLe chC b) _ _ chC (chainLe_refl chC) ?_
  intro b a hb
  by_cases h : chainLe chC a ∧ Majority V V' t a ∧ b.length < a.length
  · simp [h]
  · simpa [h] using hb

/-! ### `MFC` returns an extension of every majority-supported chain

The other half of Case 1. Three fold invariants — the result never shortens, it is at least
as long as any majority candidate, and it is either the base or itself majority-supported —
combine with `majority_chains_comparable` to give the conclusion the paper draws from
`|V^{ch,t+1}| > |S(V_i,t+1)|/2`. -/

/-- The fold never shortens what it holds. -/
private theorem foldl_length_mono (V V' : View Node (Msg (Chain Tx) QC)) (chC : Chain Tx)
    (t : Nat) : ∀ (l : List (Chain Tx)) (b : Chain Tx),
      b.length ≤ (l.foldl (fun best ch =>
        if chainLe chC ch ∧ Majority V V' t ch ∧ best.length < ch.length then ch else best)
        b).length
  | [], _ => le_refl _
  | x :: xs, b => by
      simp only [List.foldl_cons]
      refine le_trans ?_ (foldl_length_mono V V' chC t xs _)
      split
      · rename_i h; exact le_of_lt h.2.2
      · exact le_refl _

/-- The fold ends at least as long as every candidate that extends the base and carries a
    majority. -/
private theorem foldl_length_ge (V V' : View Node (Msg (Chain Tx) QC)) (chC : Chain Tx)
    (t : Nat) : ∀ (l : List (Chain Tx)) (b x : Chain Tx), x ∈ l → chainLe chC x →
      Majority V V' t x →
      x.length ≤ (l.foldl (fun best ch =>
        if chainLe chC ch ∧ Majority V V' t ch ∧ best.length < ch.length then ch else best)
        b).length
  | y :: ys, b, x, hx, hbase, hmaj => by
      simp only [List.foldl_cons]
      rcases List.mem_cons.1 hx with rfl | hx'
      · by_cases h : chainLe chC x ∧ Majority V V' t x ∧ b.length < x.length
        · rw [if_pos h]; exact foldl_length_mono V V' chC t ys x
        · rw [if_neg h]
          have : x.length ≤ b.length := by
            by_contra hlt
            exact h ⟨hbase, hmaj, by omega⟩
          exact le_trans this (foldl_length_mono V V' chC t ys b)
      · exact foldl_length_ge V V' chC t ys _ x hx' hbase hmaj

/-- The fold's result is the base or carries a majority itself. -/
private theorem foldl_base_or_majority (V V' : View Node (Msg (Chain Tx) QC)) (chC : Chain Tx)
    (t : Nat) : ∀ (l : List (Chain Tx)) (b : Chain Tx), (b = chC ∨ Majority V V' t b) →
      (l.foldl (fun best ch =>
        if chainLe chC ch ∧ Majority V V' t ch ∧ best.length < ch.length then ch else best)
        b = chC ∨
       Majority V V' t (l.foldl (fun best ch =>
        if chainLe chC ch ∧ Majority V V' t ch ∧ best.length < ch.length then ch else best) b))
  | [], _, hb => hb
  | x :: xs, b, hb => by
      simp only [List.foldl_cons]
      refine foldl_base_or_majority V V' chC t xs _ ?_
      split
      · rename_i h; exact Or.inr h.2.1
      · exact hb

/-- `Extend` stamps its slot: the appended block is the last. -/
theorem proposedAt_extend (pool : Nat → Tx) (ch : Chain Tx) (t : Nat) :
    proposedAt (extend pool ch t) = t := by
  unfold proposedAt extend
  rw [List.getLast?_concat]
  rfl

/-- `Extend` appends a block, so its input is a prefix of its output. -/
theorem chainLe_extend (pool : Nat → Tx) (ch : Chain Tx) (t : Nat) :
    chainLe ch (extend pool ch t) := by
  rw [chainLe_iff_prefix]
  exact List.prefix_append _ _

/-- **`MFC` returns its base or a majority-supported chain** — the dichotomy Lemma 4's
    base case analyzes. -/
theorem mfc_base_or_majority (V V' : View Node (Msg (Chain Tx) QC)) (chC : Chain Tx)
    (t : Nat) : mfc V V' chC t = chC ∨ Majority V V' t (mfc V V' chC t) := by
  unfold mfc
  exact foldl_base_or_majority V V' chC t _ chC (Or.inl rfl)

/-- A prefix that is at least as long is the whole thing, so comparable chains are ordered
    by length. -/
theorem chainLe_of_comparable (a b : Chain Tx) (hc : chainLe a b ∨ chainLe b a)
    (hl : a.length ≤ b.length) : chainLe a b := by
  rcases hc with h | h
  · exact h
  · simp only [chainLe, List.isPrefixOf_iff_prefix] at h ⊢
    rw [h.eq_of_length_le hl]

/-- **`MFC(V, V', chC, t) ⪰ ch` for every majority-supported `ch ⪰ chC`** — the step
    Case 1 of Lemma 2 takes once the counting has produced the majority.

    Majority alone suffices: it forces a supporting vote, which puts `ch` among the
    prefix-closed candidates (`mem_candidates_of_majority`), and any two majority chains
    are comparable through a common supporter (`majority_comparable`). Earlier versions
    took both as extra hypotheses; the model fixes of 2026-08-03 made them derivable. -/
theorem le_mfc_of_majority (V V' : View Node (Msg (Chain Tx) QC)) (chC : Chain Tx) (t : Nat)
    (ch : Chain Tx) (hbase : chainLe chC ch) (hmaj : Majority V V' t ch) :
    chainLe ch (mfc V V' chC t) := by
  have hlen : ch.length ≤ (mfc V V' chC t).length :=
    foldl_length_ge V V' chC t _ chC ch
      (Finset.mem_toList.2 (mem_candidates_of_majority (chC := chC) hmaj)) hbase hmaj
  rcases foldl_base_or_majority V V' chC t (candidates V chC).toList chC (Or.inl rfl)
    with h | h
  · -- the fold never left the base, so the base is at least as long as `ch`, hence equal
    have : chC = mfc V V' chC t := h.symm
    rw [← this] at hlen ⊢
    exact chainLe_of_comparable ch chC (Or.inr hbase) hlen
  · exact chainLe_of_comparable ch _ (majority_comparable hmaj h) hlen

/-! ### The counting in Case 1

The paper's displayed chain of inequalities:

    |S(V_i, t+1)| = |H_{vote(t)} \ A_{vote(t+1)}| + |S(V_i,t+1) \ (H_{vote(t)} \ A_{vote(t+1)})|
                  ≤ |H_{vote(t)} \ A_{vote(t+1)}| + |A_{vote(t+1)} ∪ (H_{…} \ H_{vote(t)})|
                  < 2 |H_{vote(t)} \ A_{vote(t+1)}|

the last step "comes from Equation (1)". Both steps are pure `Finset` arithmetic, so both are
proved; what is *not* proved is the containment they start from, which is where synchrony
and the joining protocol enter. -/

/-- The paper's inequality chain. `S` is `S(V_i, t+1)`, `honest` is
    `H_{vote(t)} \ A_{vote(t+1)}`, and `other` is
    `A_{vote(t+1)} ∪ (H_{vote(t-η+1),vote(t-1)} \ H_{vote(t)})` — the two sets Constraint (1)
    compares.

    The hypothesis `hsub` is the paper's "any vote in `S(V_i, t+1)` that is not from a
    validator in `H_{vote(t)} \ A_{vote(t+1)}` must be either from a validator Byzantine at
    `vote(t+1)` or from one active between `vote(t-η+1)` and `vote(t-1)` but not at
    `vote(t)`". -/
theorem voters_lt_two_mul_honest {S honest other : Finset Node}
    (hsub : S ⊆ honest ∪ other) (hc1 : other.card < honest.card) :
    S.card < 2 * honest.card := by
  have h₁ : S.card ≤ (honest ∪ other).card := Finset.card_le_card hsub
  have h₂ : (honest ∪ other).card ≤ honest.card + other.card := Finset.card_union_le _ _
  omega

/-- The same, in the shape Constraint (1) actually supplies it: `Sleepiness` gives
    `|A_{vote(t)}| < |Active(t-1) \ A_{vote(t)}|`, so the "other" set is the adversary. -/
theorem voters_lt_of_sleepiness {S honest : Finset Node} {adv : Finset Node}
    (hsub : S ⊆ honest ∪ adv) (hc1 : adv.card < honest.card) :
    S.card < 2 * honest.card :=
  voters_lt_two_mul_honest hsub hc1

end Majorum
