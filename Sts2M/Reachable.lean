import Framework.Sts2M.Lemmas

/-!
# Reachability, and one invariant proved through the eliminator

The framework's first inductive-invariant proof, added to test whether `Step.elim`
really recovers the ergonomics of case analysis on an inductive step relation.

The property chosen is one `Execution.lean` currently *assumes* — `ViewsSound`, that
everything in a validator's view was really signed and sent. It should not need to be
an assumption: a message enters a view only via `deliver`, whose enabling condition
requires it to be in `sent` already, and `sent` never shrinks.
-/

set_option autoImplicit false

namespace Framework.Sts2M

variable {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
  {Pr : Protocol Node Msg NodeState Ev} {S : Schedule Node}

/-- Configurations reachable from an initial one. -/
inductive Reachable (Pr : Protocol Node Msg NodeState Ev) (S : Schedule Node) :
    Config Node Msg NodeState → Prop where
  | init {c : Config Node Msg NodeState} : Init Pr c → Reachable Pr S c
  | step {a : Action Node Msg Ev} {c c' : Config Node Msg NodeState} :
      Reachable Pr S c → Step Pr S a c c' → Reachable Pr S c'

/-- Everything in a validator's view was signed and sent. -/
def ViewsSound (c : Config Node Msg NodeState) : Prop :=
  ∀ (p : Node) (m : SignedMsg Node Msg), m ∈ c[p].view → m ∈ c.sent

/-- `ViewsSound` holds everywhere reachable — so `Execution.ViewsSound` need not be
    assumed.

    Note how the induction hypothesis reaches the cases: the motive is an *implication*,
    `ViewsSound d → ViewsSound d'`, and the eliminator's result is applied to `ih`. That
    is the one idiom `Step.elim` needs that `cases` on an inductive would not. -/
theorem viewsSound {c : Config Node Msg NodeState} (h : Reachable Pr S c) : ViewsSound c := by
  induction h with
  | init hi =>
      obtain ⟨-, hnodes, -⟩ := hi
      intro p m hm
      simp [hnodes p] at hm
  | step _ hstep ih =>
      refine hstep.elim (motive := fun _ d d' => ViewsSound d → ViewsSound d')
        ?_ ?_ ?_ ?_ ?_ ?_ ih
      -- advance: only `time` moves
      · intro d t hv p m hm
        exact hv p m hm
      -- tick: the view is untouched, the network only grows
      · intro d q t res _ _ hv p m hm
        simp at hm
        exact Multiset.mem_add.mpr (Or.inl (hv p m hm))
      -- deliver: the one new message was in `sent` by the action's own condition
      · intro d q msg res hen _ hv p m hm
        by_cases hpq : p = q
        · subst hpq
          simp at hm
          rcases hm with rfl | hm
          · exact Multiset.mem_add.mpr (Or.inl hen.1)
          · exact Multiset.mem_add.mpr (Or.inl (hv p m hm))
        · simp [hpq] at hm
          exact Multiset.mem_add.mpr (Or.inl (hv p m hm))
      -- wake and custom: as tick
      · intro d q res _ _ hv p m hm
        simp at hm
        exact Multiset.mem_add.mpr (Or.inl (hv p m hm))
      · intro d q ev res _ _ hv p m hm
        simp at hm
        exact Multiset.mem_add.mpr (Or.inl (hv p m hm))
      -- adversarial: the view is untouched, one message is added
      · intro d q msg _ hv p m hm
        exact Multiset.mem_cons.mpr (Or.inr (hv p m hm))

end Framework.Sts2M
