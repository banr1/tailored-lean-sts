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

## Status after a second attempt

Case 2 of the paper's proof is now proved outright (`base_le_mfc`), as is the counting chain
in Case 1 (`voters_lt_two_mul_honest`). What is still missing for Case 1, in order:

* the **containment** `S(V_i, t+1) ⊆ (H_{vote(t)} \ A_{vote(t+1)}) ∪ (A_{vote(t+1)} ∪ …)`,
  which is where synchrony and the joining protocol enter and which needs the execution
  layer;
* a **maximality lemma for `mfc`** — that it returns a chain at least as long as every
  candidate carrying a majority — which with `majority_chains_comparable` would give
  `ch ⪯ MFC`.

  A first attempt failed with "failed to synthesize `Decidable (mfcGuard …)`", which I read
  as the model's fold guard needing to be a `Bool`. **That was wrong.** The guard is
  decidable; what defeated instance search was naming it with a plain `def`, which is not
  reducible, so the conjunction was opaque. An `abbrev` — or `@[reducible] def` — is found
  immediately, needing only `noncomputable` on anything that then produces data, since the
  instance mentions `voters`. Nothing in `Components.lean` needs to change; the remaining
  work is the induction itself.
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
