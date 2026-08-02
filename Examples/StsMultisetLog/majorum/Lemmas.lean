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

end Majorum
