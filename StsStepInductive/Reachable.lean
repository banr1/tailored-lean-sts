import StsStepInductive.Protocol

/-!
# Reachability, and one invariant by case analysis

The same inductive-invariant proof `StsRelationalSetLog` does through `Step.elim`, here by plain `cases`
on the step. It is the comparison this attempt exists for.

The property chosen is one `Execution.lean` currently *assumes* — `ViewsSound`, that
everything in a validator's view was really signed and sent. It should not need to be
an assumption: a message enters a view only via `deliver`, whose enabling condition
requires it to be in `sent` already, and `sent` never shrinks.
-/

set_option autoImplicit false

namespace Framework.StsStepInductive

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

    Against `StsRelationalSetLog`'s version of this proof: `cases hstep` needs no motive, and the
    induction hypothesis `ih` is simply in context. `StsRelationalSetLog` has to make the motive an
    *implication*, `ViewsSound d → ViewsSound d'`, and apply the eliminator's result to
    `ih`, because `Step.elim` is a theorem about a fixed motive rather than a real
    eliminator. The case bodies are otherwise identical, line for line. -/
theorem viewsSound {c : Config Node Msg NodeState} (h : Reachable Pr S c) : ViewsSound c := by
  induction h with
  | init hi =>
      obtain ⟨-, hnodes, -⟩ := hi
      intro p m hm
      simp [hnodes p] at hm
  | step _ hstep ih =>
      cases hstep with
      -- advance: only `time` moves
      | advance t => exact ih
      -- tick: the view is untouched, the network only grows
      | tick res _ _ =>
          intro p m hm
          simp at hm
          exact Or.inl (ih p m hm)
      -- deliver: the one new message was in `sent` by the constructor's own hypothesis
      | @deliver _ q msg res hsent _ _ =>
          intro p m hm
          by_cases hpq : p = q
          · subst hpq
            simp at hm
            rcases hm with rfl | hm
            · exact Or.inl hsent
            · exact Or.inl (ih p m hm)
          · simp [hpq] at hm
            exact Or.inl (ih p m hm)
      -- wake and custom: as tick
      | wake res _ _ _ =>
          intro p m hm
          simp at hm
          exact Or.inl (ih p m hm)
      | custom res _ _ _ =>
          intro p m hm
          simp at hm
          exact Or.inl (ih p m hm)
      -- adversarial: the view is untouched, one message is added
      | adversarial _ =>
          intro p m hm
          exact Or.inr (ih p m hm)

end Framework.StsStepInductive
