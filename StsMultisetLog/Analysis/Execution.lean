import StsMultisetLog.Analysis.Reachable
import StsMultisetLog.Spec.Execution

/-!
# What holds of every execution

The three facts that `Spec/Execution.lean` states its definitions well enough to support:
that `TimeStepwise` is the stronger of the two monotonicity assumptions, that every
configuration of an execution is reachable, and — via `viewsSound` — that a view never
contains a message that was not signed and sent. The last used to be an *assumption* in both
models.
-/

set_option autoImplicit false

namespace Framework.StsMultisetLog

variable {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
  {Pr : Protocol Node Msg NodeState Ev} {S : Schedule Node}

/-- `TimeStepwise` is the stronger assumption. -/
theorem TimeStepwise.timeMonotone {x : Exec Pr S} (h : TimeStepwise x) : TimeMonotone x :=
  fun i => by rcases h i with heq | heq <;> omega

variable (x : Exec Pr S) (i : Nat)

/-- Every configuration in an execution is reachable. -/
theorem Execution.reachable : Reachable Pr S x[i] := by
  induction i with
  | zero => exact .init x.init
  | succ i ih => exact .step ih (x.step i)

/-- Nothing appears in a view unless it was signed and sent.

    This used to be an **assumption** in both models. It is a theorem: a message enters a
    view only through `deliver`, whose enabling condition requires it to be in `sent`
    already, and `sent` never shrinks. See `Framework.StsMultisetLog.viewsSound`. -/
theorem views_sound (p : Node) (m : SignedMsg Node Msg) (hm : m ∈ x[i][p].view) : m ∈ x[i].sent :=
  viewsSound (x.reachable i) p m hm

end Framework.StsMultisetLog
