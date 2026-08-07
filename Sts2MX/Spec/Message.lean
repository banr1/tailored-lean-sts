import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Int.Interval

/-!
# Time, messages, views

Vocabulary shared by every model. Nothing here commits to a network model, an
adversary, or a protocol.
-/

set_option autoImplicit false

namespace Framework.Sts2MX

/-- Discrete time, counted in rounds — Majorum §Model has "time is divided into
    discrete rounds", TOB-SVD counts time steps.

    `Config.time` is the true current round and `Local.clock` is one node's belief
    about it; both are measured in this. Nothing at the type level distinguishes the
    two, so the discipline is that only the environment reads `Config.time` and only
    `Local.clock` is ever handed to a protocol.

    Slots are deliberately absent: Majorum's `4Δ`-round slot is a property of
    that model, and it defines its own `proposing`/`voting` rounds over `Time`
    (see `Models.Majorum`). TOB-SVD has no round-aligned slots at all.

    **Notation, not an `abbrev`.** Measured twice in this repository now: `omega` does
    not see through a reducible alias, so `abbrev Time := Nat` makes arithmetic on
    rounds unprovable by it. Notation expands at parse time, leaving nothing to hide
    the `Nat`. -/
scoped notation "Time" => Nat

/-- A message together with its signer. Signing is structural: appearing under
    `sender = p` *is* being signed by `p`. -/
structure SignedMsg (Node Msg : Type) where
  /-- The signer. -/
  sender : Node
  /-- The message. -/
  msg : Msg
  deriving DecidableEq

/-- A validator's view: every message it has received so far (Majorum's `V^r_i`,
    TOB-SVD's received-message state). Maintained by the framework, so a
    protocol can neither forget nor fabricate a delivery. -/
abbrev View (Node Msg : Type) := Finset (SignedMsg Node Msg)

end Framework.Sts2MX
