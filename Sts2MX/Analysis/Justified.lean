import Sts2MX.Analysis.Reachable

/-!
# Signed messages are justified by their signer's state

Statement and proof together. `Justified` and `Justifies` are here rather than under `Spec/`
because nothing in the model mentions them: they are a predicate coined to be this theorem's
conclusion and a bundle coined to be its hypotheses, referred to by no other file and by no
downstream consumer.

The same invariant as `Framework.Sts2.Justified`, proved the way this attempt makes
available: from the **frame lemmas**, with the successor never replaced by a term.
`justified_nodeStep` reasons about `c'` through `NodeStep.other` and `NodeStep.sent_signed`, and
`Step.elimR` is the eliminator that suits that — it hands each reacting case a `NodeStep` and
leaves `c'` alone, where `Step.elim` would bind a reaction and substitute a concrete
successor.

The comparison is recorded in `CONTEXT.md`; the statement and the protocol's obligations are
identical to `Sts2`'s, so only the proofs differ.
-/

set_option autoImplicit false

namespace Framework.Sts2MX

variable {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
  {Pr : Protocol Node Msg NodeState Ev} {S : Schedule Node}
  {H : Set Node} {Just : Node → NodeState → Msg → Prop}
variable (q : Node) (t : Time) (m : SignedMsg Node Msg) (d : Config Node Msg NodeState)

/-- Every message in the log signed by a validator in `H` is justified by that validator's
    current state. -/
def Justified (H : Set Node) (Just : Node → NodeState → Msg → Prop)
    (c : Config Node Msg NodeState) : Prop :=
  ∀ sm ∈ c.sent, sm.sender ∈ H → Just sm.sender c[sm.sender].st sm.msg

/-- What a protocol must supply for `justified` to hold of it. -/
structure Justifies (Pr : Protocol Node Msg NodeState Ev) (S : Schedule Node) (H : Set Node)
    (Just : Node → NodeState → Msg → Prop) : Prop where
  /-- A justification survives its signer's own later steps. -/
  mono : ∀ p r view s e res, Pr.step p r view s e res → ∀ m, Just p s m → Just p res.state m
  /-- Whatever a validator sends is justified by the state it moves to. -/
  sends : ∀ p r view s e res, Pr.step p r view s e res → ∀ m ∈ res.send, Just p res.state m
  /-- `H` really is honest: the adversary never signs on its behalf. -/
  honest : ∀ (t : Int) (p : Node), p ∈ S.adv t → p ∉ H

/-! ### The two helpers that keep the six cases short -/

omit [DecidableEq Msg] in
/-- Moving a clock justifies nothing new and invalidates nothing. -/
theorem justified_setClock (hJ : Justified H Just d) : Justified H Just (setClock q t d) := by
  intro sm hm hH
  have : (setClock q t d)[sm.sender].st = d[sm.sender].st := by
    by_cases hs : q = sm.sender <;> simp [setClock_getElem, hs]
  rw [this]
  exact hJ sm hm hH

/-- Filing a delivery likewise. -/
theorem justified_receive (hJ : Justified H Just d) :
    Justified H Just (receive q m d) := by
  intro sm hm hH
  have : (receive q m d)[sm.sender].st = d[sm.sender].st := by
    by_cases hs : q = sm.sender <;> simp [receive_getElem, hs]
  rw [this]
  exact hJ sm hm hH

/-- The reaction, through the frame lemmas. `c'` is never replaced by a term: what the proof
    uses is that the signer's state is unchanged unless it is `p`, and that any message the
    log gained was signed by `p`. -/
theorem justified_nodeStep (hj : Justifies Pr S H Just) (p : Node) (e : Event Node Msg Ev)
    (pre c' : Config Node Msg NodeState) (h : NodeStep Pr p e pre c')
    (hJ : Justified H Just pre) : Justified H Just c' := by
  intro sm hm hH
  by_cases hs : sm.sender = p
  · -- the signer is the validator that acted; `extract`'s state *is* `c'[p].st`
    rw [hs]
    by_cases hold : sm ∈ pre.sent
    · exact hj.mono p pre[p].clock pre[p].view pre[p].st e (extract p pre c') h.1 sm.msg
        (hs ▸ hJ sm hold hH)
    · -- not there before, so the log gained it, so this reaction sent it
      have hdelta : sm ∈ c'.sent - pre.sent := by
        rw [← Multiset.count_pos, Multiset.count_sub,
          Multiset.count_eq_zero_of_notMem hold, Nat.sub_zero]
        exact Multiset.count_pos.mpr hm
      have : sm.msg ∈ (extract p pre c').send :=
        Multiset.mem_map_of_mem _ hdelta
      exact hj.sends p pre[p].clock pre[p].view pre[p].st e (extract p pre c') h.1 sm.msg this
  · -- another validator's signature: its state did not move, and it was already in the log
    rw [h.other sm.sender hs]
    refine hJ sm ?_ hH
    by_contra hold
    exact hs (h.sent_signed sm (by
      rw [← Multiset.count_pos, Multiset.count_sub,
        Multiset.count_eq_zero_of_notMem hold, Nat.sub_zero]
      exact Multiset.count_pos.mpr hm))

/-! ### The invariant -/

/-- Everything an honest validator signed is justified by its current state, everywhere
    reachable.

    Through `Step.elimR`, whose reacting cases hand over exactly the `NodeStep` the helper
    wants. Going through `Step.elim` instead costs a `nodeStep_iff_exists` wrap per case, and
    doing the case analysis by hand costs the eliminator — both land six lines longer. -/
theorem justified (hj : Justifies Pr S H Just) {c : Config Node Msg NodeState}
    (h : Reachable Pr S c) : Justified H Just c := by
  induction h with
  | init hi =>
      obtain ⟨-, -, hsent⟩ := hi
      intro sm hm
      simp [hsent] at hm
  | step _ hstep ih =>
      refine hstep.elimR (motive := fun _ d d' => Justified H Just d → Justified H Just d')
        ?_ ?_ ?_ ?_ ?_ ?_ ih
      -- advance: neither the log nor any state moves
      · intro d t hJ sm hm hH
        exact hJ sm hm hH
      -- the four reacting actions differ only in the configuration the reaction reads
      · intro d d' q t _ hr hJ
        exact justified_nodeStep hj q .tick _ d' hr (justified_setClock q t d hJ)
      · intro d d' q msg _ hr hJ
        exact justified_nodeStep hj q (.recv msg) _ d' hr (justified_receive q msg d hJ)
      · intro d d' q _ hr hJ
        exact justified_nodeStep hj q .wake _ d' hr hJ
      · intro d d' q ev _ hr hJ
        exact justified_nodeStep hj q (.custom ev) _ d' hr hJ
      -- adversarial: the new signature is not one of `H`'s, and no state moves
      · intro d q msg hen hJ sm hm hH
        rcases Multiset.mem_cons.1 hm with rfl | hold
        · exact absurd hH (hj.honest _ q hen)
        · exact hJ sm hold hH

end Framework.Sts2MX
