import Examples.StsMultisetLog.majorum.Components

/-!
# Towards Lemma 2

**Lemma 2** of arXiv:2601.03862v1: if every validator in `H_{vote(t)}` votes in slot
`t` for a chain extending `ch`, then every validator in `H_{vote(t+1)}` has
`MFC^{propose(t+1)} ⪰ ch` and `MFC^{vote(t+1)} ⪰ ch`, and so votes in slot `t+1` for a chain
extending `ch` too. It is the induction step behind reorg resilience.

**It is not proved here, and this file does not claim it.** What is proved is the counting
core that the paper's argument turns on, stated over this model:

* `quorum_inter` — two sets of validators each more than half of a common pool must meet.
* `comparable_of_common_extension` — chains extended by a common chain are comparable.
* `majority_chains_comparable` — putting those together: two chains that each carry a
  majority of `S(V', t)` are comparable, so `MFC`'s "longest such chain" is well posed and
  every majority-supported chain is a prefix of it.

What Lemma 2 needs beyond this, and why it is a much larger job:

1. **The execution layer.** "All validators in `H_{vote(t)}` send vote messages for chains
   extending `ch`" is a statement about what happened in an execution, not about a view. It
   has to be connected to `handler`'s vote branch actually having run for each of them, which
   needs `the framework's flat multiset-log flavour.Execution` and `Diligent`.
2. **Synchrony.** The proof's first move is that every vote from `H_{vote(t)} \ A_{vote(t+1)}`
   is in `V_i` by `propose(t+1)`, which is `Synchrony` plus `Relay` plus the slot arithmetic.
3. **The joining protocol.** `v_i ∈ H_{vote(t+1)}` gives that `v_i` was awake at `merge(t)`,
   which is exactly what `Assumptions.Active` encodes — so this step should be short, and it
   is the one place the groundwork already pays.
4. **Constraint (1)**, to turn "the honest voters of slot `t` outnumber the adversary" into
   the majority `MFC` needs.
5. **A case analysis on `chfrozen`**, which the paper splits into two, and which needs the
   `merge` branch of `handler` related to the `vote` branch a slot later.

So the honest position is that the arithmetic is done and the protocol reasoning is not.

## Status

Both of Lemma 2's cases are now proved *as statements about `MFC`*:

* **Case 2** — `base_le_mfc`: `MFC(V, V', chC, t) ⪰ chC`, so once `chfrozen ⪰ ch` the
  conclusion is immediate.
* **Case 1's conclusion** — `le_mfc_of_majority`: `MFC ⪰ ch` for every candidate `ch` that
  extends the base and carries a majority of `S(V', t)`.
* **Case 1's counting** — `voters_lt_two_mul_honest`: the paper's displayed inequality chain,
  which is what supplies that majority from Constraint (1).

**The rest was believed to be "exactly one thing" — the execution-level containment. It is
not.** Attempting it found that Lemma 2 is **false for the model as it stands**, in two
independent ways, with three further gaps behind them:

* `candidates` misses chains that are only *prefixes* of voted chains, so `mfc` can return
  `genesis` where the paper's MFC — which quantifies over all chains — returns `ch`;
* the handler does not implement the joining protocol, so just-woken honest validators vote
  before they are active and Constraint (1) cannot bound the voter set;
* nothing prevents two ticks at one reading, so an honest validator can equivocate and be
  dropped by `FIL_eq`;
* `Majority` counts messages where the paper counts validators, so fin-vote variants from
  one sender can fake a majority;
* `validProposal` does not check the certificate, which the vote-round half leans on.

The full accounting, the fix each needs, and a hole found in the paper's own proof are in
`CONTEXT.md` (majorum, 2026-08-03). Everything proved in this file is true as stated and
stays — the fifth item even dissolves the sender/message mismatch that left
`majority_chains_comparable` taking comparability as a hypothesis. Nothing further of
Lemma 2 is provable before the model changes, which are awaiting approval.
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

/-- **Majority-supported chains are comparable.**

    If a validator's latest non-expired vote is for a chain extending both `a` and `b`, then
    `a` and `b` are nested; so if each of `a` and `b` is supported by more than half of
    `S(V', t)`, quorum intersection supplies such a validator.

    This is what makes `mfc`'s "the longest chain such that …" a definite description rather
    than a choice among incomparable options, and it is the step Lemma 2 uses to conclude
    that `MFC` returns an extension of `ch` once `ch` itself carries a majority. -/
theorem majority_chains_comparable {V' : View Node (Msg (Chain Tx) QC)} {t : Nat}
    {a b : Chain Tx} {A B : Finset Node}
    (hA : A ⊆ voters V' t) (hB : B ⊆ voters V' t)
    (ha : (voters V' t).card < 2 * A.card) (hb : (voters V' t).card < 2 * B.card)
    (wit : Node → Chain Tx)
    (hwa : ∀ p ∈ A, chainLe a (wit p)) (hwb : ∀ p ∈ B, chainLe b (wit p)) :
    chainLe a b ∨ chainLe b a := by
  obtain ⟨p, hp⟩ := quorum_inter hA hB ha hb
  rw [Finset.mem_inter] at hp
  exact comparable_of_common_extension (hwa p hp.1) (hwb p hp.2)

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
  by_cases h : chainLe chC a ∧
      (voters V' t).card < 2 * ((votesFor V a t) ∩ (votesFor V' a t)).card ∧
      b.length < a.length
  · simpa [h] using h.1
  · simpa [h] using hb

/-! ### `MFC` returns an extension of every majority-supported chain

The other half of Case 1. Three fold invariants — the result never shortens, it is at least
as long as any majority candidate, and it is either the base or itself majority-supported —
combine with `majority_chains_comparable` to give the conclusion the paper draws from
`|V^{ch,t+1}| > |S(V_i,t+1)|/2`. -/

/-- The majority condition `mfc` tests. An `abbrev`, so instance search can see through it:
    as a plain `def` it is opaque and every `Decidable` goal about it fails. -/
abbrev Majority (V V' : View Node (Msg (Chain Tx) QC)) (t : Nat) (a : Chain Tx) : Prop :=
  (voters V' t).card < 2 * ((votesFor V a t) ∩ (votesFor V' a t)).card

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

/-- A prefix that is at least as long is the whole thing, so comparable chains are ordered
    by length. -/
theorem chainLe_of_comparable (a b : Chain Tx) (hc : chainLe a b ∨ chainLe b a)
    (hl : a.length ≤ b.length) : chainLe a b := by
  rcases hc with h | h
  · exact h
  · simp only [chainLe, List.isPrefixOf_iff_prefix] at h ⊢
    rw [h.eq_of_length_le hl]

/-- **`MFC(V, V', chC, t) ⪰ ch` for every majority-supported candidate `ch`.**

    This is what Case 1 of Lemma 2 concludes once it has shown `|V^{ch,t+1}| >
    |S(V_i,t+1)|/2`. The `wit`/`hw` hypotheses are what `majority_chains_comparable` needs:
    a supporter of a chain has a latest vote extending it, which holds of `votesFor` by
    construction but is supplied here rather than re-derived. -/
theorem le_mfc_of_majority (V V' : View Node (Msg (Chain Tx) QC)) (chC : Chain Tx) (t : Nat)
    (ch : Chain Tx) (hmem : ch ∈ candidates V chC) (hbase : chainLe chC ch)
    (hmaj : Majority V V' t ch)
    (hcomp : ∀ b, Majority V V' t b → chainLe ch b ∨ chainLe b ch) :
    chainLe ch (mfc V V' chC t) := by
  have hlen : ch.length ≤ (mfc V V' chC t).length :=
    foldl_length_ge V V' chC t _ chC ch (Finset.mem_toList.2 hmem) hbase hmaj
  rcases foldl_base_or_majority V V' chC t (candidates V chC).toList chC (Or.inl rfl) with h | h
  · -- the fold never left the base, so the base is at least as long as `ch`, hence equal
    have : chC = mfc V V' chC t := h.symm
    rw [← this] at hlen ⊢
    exact chainLe_of_comparable ch chC (Or.inr hbase) hlen
  · exact chainLe_of_comparable ch _ (hcomp _ h) hlen

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
