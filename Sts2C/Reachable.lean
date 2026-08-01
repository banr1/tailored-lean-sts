import Framework.Sts2C.Protocol

/-!
# Reachability, and one invariant by case analysis on the label

The same inductive-invariant proof the other attempts do. Here the case split is on the
*label*, after substituting the single successor equation `c' = act a c`.

The property chosen is one `Execution.lean` currently *assumes* — `ViewsSound`, that
everything in a validator's view was really signed and sent. It should not need to be
an assumption: a message enters a view only via `deliver`, whose enabling condition
requires it to be in `sent` already, and `sent` never shrinks.
-/

set_option autoImplicit false

namespace Framework.Sts2C

variable {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
  {Pr : Protocol Node Msg NodeState Ev} {S : Schedule Node}

/-- Configurations reachable from an initial one. -/
inductive Reachable (Pr : Protocol Node Msg NodeState Ev) (S : Schedule Node) :
    Config Node Msg NodeState → Prop where
  | init {c : Config Node Msg NodeState} : Init Pr c → Reachable Pr S c
  | step {a : Action Node Msg NodeState Ev} {c c' : Config Node Msg NodeState} :
      Reachable Pr S c → Step Pr S a c c' → Reachable Pr S c'

/-- Everything in a validator's view was signed and sent. -/
def ViewsSound (c : Config Node Msg NodeState) : Prop :=
  ∀ (p : Node) (m : SignedMsg Node Msg), m ∈ c[p].view → m ∈ c.sent

/-- `ViewsSound` holds everywhere reachable — so `Execution.ViewsSound` need not be
    assumed.

    The `obtain ⟨hen, rfl⟩` is paid once, not per case, because every label produces
    `act a c`. The label is then split into its kind and its reaction, and the case analysis
    is on the kind. What each case needs from the guard it reads out of `hen`, whose shape
    `enabled` fixes per kind — `hen.1` for `deliver` is `m ∈ c.sent`. -/
theorem viewsSound {c : Config Node Msg NodeState} (h : Reachable Pr S c) : ViewsSound c := by
  induction h with
  | init hi =>
      obtain ⟨-, hnodes, -⟩ := hi
      intro p m hm
      simp [hnodes p] at hm
  | @step a d d' _ hstep ih =>
      obtain ⟨hen, rfl⟩ := hstep
      obtain ⟨k, res⟩ := a
      cases k with
      -- advance: only `time` moves
      | advance t => exact ih
      -- tick: the view is untouched, the network only grows
      | tick q t =>
          intro p m hm
          simp [act] at hm
          exact Or.inl (ih p m hm)
      -- deliver: the one new message was in `sent` by the label's own guard
      | deliver q msg =>
          intro p m hm
          by_cases hpq : p = q
          · subst hpq
            simp [act] at hm
            rcases hm with rfl | hm
            · exact Or.inl hen.1
            · exact Or.inl (ih p m hm)
          · simp [act, hpq] at hm
            exact Or.inl (ih p m hm)
      -- wake and custom: as tick
      | wake q =>
          intro p m hm
          simp [act] at hm
          exact Or.inl (ih p m hm)
      | custom q ev =>
          intro p m hm
          simp [act] at hm
          exact Or.inl (ih p m hm)
      -- adversarial: the view is untouched, one message is added
      | adversarial q msg =>
          intro p m hm
          exact Or.inr (ih p m hm)

end Framework.Sts2C
