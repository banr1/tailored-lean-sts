import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Int.Interval

/-!
# Time, messages, views

Vocabulary shared by every model. Nothing here commits to a network model, an
adversary, or a protocol.
-/

set_option autoImplicit false

namespace Framework.Sts2

/-- Discrete rounds, as in Majorum §Model ("time is divided into discrete
    rounds") and TOB-SVD's time steps.

    Slots are deliberately absent: Majorum's `4Δ`-round slot is a property of
    that model, and it defines its own `proposing`/`voting` rounds over `Round`
    (see `Models.Majorum`). TOB-SVD has no round-aligned slots at all. -/
abbrev Round := Nat

/-- A message together with its signer. Signing is structural: appearing under
    `sender = p` *is* being signed by `p`. -/
structure SignedMsg (V Msg : Type) where
  /-- The signer. -/
  sender : V
  /-- The message. -/
  msg : Msg
  deriving DecidableEq

/-- A validator's view: every message it has received so far (Majorum's `V^r_i`,
    TOB-SVD's received-message state). Maintained by the framework, so a
    protocol can neither forget nor fabricate a delivery. -/
abbrev View (V Msg : Type) := Finset (SignedMsg V Msg)

end Framework.Sts2
