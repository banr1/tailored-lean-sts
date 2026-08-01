/-!
# Labelled transition systems

The framework's own, so that it depends on nothing outside `Framework/`.

Only the structure itself lives here, because that is all the framework currently
uses: it carries no proofs while its shape is still being iterated on. The
reachability and inductive-invariant machinery that goes with it — `Reachable`,
`Invariant`, `Invariant.reachable` — is in `Common/System.lean`, where the `Sts`
modelling attempt uses it. **When proofs come back, bring that machinery here
rather than importing `Common`**: liveness needs statements over executions
(`Framework.Sts2.Execution`) that `Common`'s state-based `Invariant` cannot
express, so the two will diverge.
-/

set_option autoImplicit false

universe u v

namespace Framework.Sts2

/-- A labelled transition system: a predicate picking out initial states, and a
    labelled step relation. The relation is deliberately allowed to be
    nondeterministic and partial — an action need not be enabled everywhere. -/
structure System (State : Type u) (Label : Type v) where
  /-- States the system may start in. -/
  Init : State → Prop
  /-- Labelled transition relation. -/
  Step : Label → State → State → Prop

end Framework.Sts2
