import StsRelationalSetLog.Reachable

/-!
# Signed messages are justified by their signer's state

The framework's first *parameterised* invariant, and the one `CONTEXT.md` records as the
schema this framework will eventually owe: everything an honest validator signed is
justified by that validator's current state.

It is deeper than `viewsSound` in the way that matters for a comparison between attempts —
the induction hypothesis is used non-trivially in two different places per action (an old
message whose signer just changed state, and an old message whose signer did not), and the
proof needs both of the protocol's own obligations.

The justification predicate is a parameter, because what justifies a signature is protocol
business: "I signed a vote for `v` in view `w`" is justified by "my state records that I
locked `v` at `w`". `Justifies` is what a protocol must prove to use this.
-/

set_option autoImplicit false

namespace Framework.StsRelationalSetLog

variable {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
  {Pr : Protocol Node Msg NodeState Ev} {S : Schedule Node}
  {H : Set Node} {Just : Node → NodeState → Msg → Prop}

/-- Every message in the log signed by a validator in `H` is justified by that validator's
    current state. -/
def Justified (H : Set Node) (Just : Node → NodeState → Msg → Prop)
    (c : Config Node Msg NodeState) : Prop :=
  ∀ sm ∈ c.sent, sm.sender ∈ H → Just sm.sender c[sm.sender].st sm.msg

/-- What a protocol must supply for `justified` to hold of it. -/
structure Justifies (Pr : Protocol Node Msg NodeState Ev) (S : Schedule Node) (H : Set Node)
    (Just : Node → NodeState → Msg → Prop) : Prop where
  /-- A justification survives its signer's own later steps. Without this an honest
      validator could invalidate what it already signed. -/
  mono : ∀ p r view s e res, Pr.step p r view s e res → ∀ m, Just p s m → Just p res.state m
  /-- Whatever a validator sends is justified by the state it moves to. -/
  sends : ∀ p r view s e res, Pr.step p r view s e res → ∀ m ∈ res.send, Just p res.state m
  /-- `H` really is honest: the adversary never signs on its behalf. -/
  honest : ∀ (t : Int) (p : Node), p ∈ S.adv t → p ∉ H

/-! ### The two helpers that keep the six cases short -/

omit [DecidableEq Msg] in
/-- Moving a clock justifies nothing new and invalidates nothing. -/
theorem justified_setClock (q : Node) (t : Time) (d : Config Node Msg NodeState)
    (hJ : Justified H Just d) : Justified H Just (setClock q t d) := by
  intro sm hm hH
  have : (setClock q t d)[sm.sender].st = d[sm.sender].st := by
    by_cases hs : q = sm.sender <;> simp [setClock_getElem, hs]
  rw [this]
  exact hJ sm hm hH

/-- Filing a delivery likewise. -/
theorem justified_receive (q : Node) (m : SignedMsg Node Msg)
    (d : Config Node Msg NodeState) (hJ : Justified H Just d) :
    Justified H Just (receive q m d) := by
  intro sm hm hH
  have : (receive q m d)[sm.sender].st = d[sm.sender].st := by
    by_cases hs : q = sm.sender <;> simp [receive_getElem, hs]
  rw [this]
  exact hJ sm hm hH

/-- The reaction itself: the only place the protocol's obligations are used. -/
theorem justified_nodeStep (hj : Justifies Pr S H Just) (p : Node) (e : Event Node Msg Ev)
    (pre : Config Node Msg NodeState) (res : NodeStepResult NodeState Msg)
    (hstep : Pr.step p pre[p].clock pre[p].view pre[p].st e res)
    (hJ : Justified H Just pre) :
    Justified H Just (applyNodeStepResult p res pre) := by
  intro sm hm hH
  by_cases hs : sm.sender = p
  · -- the signer is the validator that just acted, so its state moved to `res.state`
    rw [hs]
    have hst : (applyNodeStepResult p res pre)[p].st = res.state := by
      simp [applyNodeStepResult_getElem]
    rw [hst]
    rcases hm with hold | hnew
    · -- signed earlier: the justification has to survive this step
      exact hj.mono p pre[p].clock pre[p].view pre[p].st e res hstep sm.msg
        (hs ▸ hJ sm hold hH)
    · -- signed now: it is one of the messages this reaction sent
      obtain ⟨m, hmem, rfl⟩ := hnew
      exact hj.sends p pre[p].clock pre[p].view pre[p].st e res hstep m hmem
  · -- some other validator's signature: its state did not move
    have hst : (applyNodeStepResult p res pre)[sm.sender].st = pre[sm.sender].st := by
      simp [applyNodeStepResult_getElem, Ne.symm hs]
    rw [hst]
    rcases hm with hold | hnew
    · exact hJ sm hold hH
    · obtain ⟨m, -, rfl⟩ := hnew
      exact absurd rfl hs

/-! ### The invariant -/

/-- Everything an honest validator signed is justified by its current state, everywhere
    reachable. -/
theorem justified (hj : Justifies Pr S H Just) {c : Config Node Msg NodeState}
    (h : Reachable Pr S c) : Justified H Just c := by
  induction h with
  | init hi =>
      obtain ⟨-, -, hsent⟩ := hi
      intro sm hm
      simp [hsent] at hm
  | step _ hstep ih =>
      refine hstep.elim (motive := fun _ d d' => Justified H Just d → Justified H Just d')
        ?_ ?_ ?_ ?_ ?_ ?_ ih
      -- advance: neither the log nor any state moves
      · intro d t hJ sm hm hH
        exact hJ sm hm hH
      -- the four reacting actions differ only in the configuration the reaction reads
      · intro d q t res _ hp hJ
        exact justified_nodeStep hj q .tick _ res hp (justified_setClock q t d hJ)
      · intro d q msg res _ hp hJ
        exact justified_nodeStep hj q (.recv msg) _ res hp (justified_receive q msg d hJ)
      · intro d q res _ hp hJ
        exact justified_nodeStep hj q .wake _ res hp hJ
      · intro d q ev res _ hp hJ
        exact justified_nodeStep hj q (.custom ev) _ res hp hJ
      -- adversarial: the new signature is not one of `H`'s, and no state moves
      · intro d q msg hen hJ sm hm hH
        rcases hm with rfl | hold
        · exact absurd hH (hj.honest _ q hen)
        · exact hJ sm hold hH

end Framework.StsRelationalSetLog
