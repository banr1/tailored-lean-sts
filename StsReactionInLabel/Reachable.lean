import StsReactionInLabel.Protocol

/-!
# Reachability, and one invariant by case analysis

The same inductive-invariant proof `StsRelationalSetLog` does through `Step.elim`. Here the transition is
destructured once — there is no existential and the successor is a single term — and the case
analysis is on the action.

The property chosen is one `Execution.lean` currently *assumes* — `ViewsSound`, that
everything in a validator's view was really signed and sent. It should not need to be
an assumption: a message enters a view only via `deliver`, whose enabling condition
requires it to be in `sent` already, and `sent` never shrinks.
-/

set_option autoImplicit false

namespace Framework.StsReactionInLabel

variable {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
  {Pr : Protocol Node Msg NodeState Ev} {S : Schedule Node}

/-- Configurations reachable from an initial one. -/
inductive Reachable (Pr : Protocol Node Msg NodeState Ev) (S : Schedule Node) :
    Config Node Msg NodeState → Prop where
  | init {c : Config Node Msg NodeState} : Init Pr c → Reachable Pr S c
  | step {l : Move Node Msg NodeState Ev} {c c' : Config Node Msg NodeState} :
      Reachable Pr S c → Step Pr S l c c' → Reachable Pr S c'

/-- Everything in a validator's view was signed and sent. -/
def ViewsSound (c : Config Node Msg NodeState) : Prop :=
  ∀ (p : Node) (m : SignedMsg Node Msg), m ∈ c[p].view → m ∈ c.sent

/-- `ViewsSound` holds everywhere reachable — so `Execution.ViewsSound` need not be
    assumed.

    Against `StsRelationalSetLog`'s version: no motive to supply, no eliminator to have written, and the
    `obtain` is paid once rather than per case. What each case needs from the condition it reads
    out of `hen` — for `deliver`, `hen.1` is `m ∈ c.sent`, exactly as in `StsRelationalSetLog`, because
    `ActionSpec.Enabled` is unchanged from it. -/
theorem viewsSound {c : Config Node Msg NodeState} (h : Reachable Pr S c) : ViewsSound c := by
  induction h with
  | init hi =>
      obtain ⟨-, hnodes, -⟩ := hi
      intro p m hm
      simp [hnodes p] at hm
  | @step l d d' _ hstep ih =>
      obtain ⟨hen, -, rfl⟩ := hstep
      obtain ⟨a, res⟩ := l
      cases a with
      -- advance: only `time` moves
      | advance t => exact ih
      -- tick: the view is untouched, the network only grows
      | tick q t =>
          intro p m hm
          simp [spec] at hm
          exact Or.inl (ih p m hm)
      -- deliver: the one new message was in `sent` by the action's own condition
      | deliver q msg =>
          intro p m hm
          by_cases hpq : p = q
          · subst hpq
            simp [spec] at hm
            rcases hm with rfl | hm
            · exact Or.inl hen.1
            · exact Or.inl (ih p m hm)
          · simp [spec, hpq] at hm
            exact Or.inl (ih p m hm)
      -- wake and custom: as tick
      | wake q =>
          intro p m hm
          simp [spec] at hm
          exact Or.inl (ih p m hm)
      | custom q ev =>
          intro p m hm
          simp [spec] at hm
          exact Or.inl (ih p m hm)
      -- adversarial: the view is untouched, one message is added
      | adversarial q msg =>
          intro p m hm
          exact Or.inr (ih p m hm)

end Framework.StsReactionInLabel
