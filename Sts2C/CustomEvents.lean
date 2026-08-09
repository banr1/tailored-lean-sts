import Sts2C.Protocol

/-!
# Custom events: two timers

`Framework.Sts2C.Example` uses `Ev := Empty`, so it never exercises `custom` or
`enabled`. This is the counterpart: a toy protocol with **two** protocol-specific
events, which is where the interesting behaviour lives, since the two need
different enabling conditions and reschedule themselves differently.

The three things worth seeing:

1. `Ev` is just an inductive type the protocol chooses — here two timers.
2. `Protocol.enabled` discriminates on the event, so the two have independent
   conditions. `resend` additionally depends on state beyond its deadline, which
   is why `enabled` takes the state and not only the round.
3. A reaction must **push its own deadline forward**. `enabled` is re-checked
   against the new state, so a timer that does not reschedule stays enabled and
   the scheduler may fire it again immediately. Unlike tick-idempotence — which
   `Step.clock` now rules out structurally — this one is genuinely the protocol's
   responsibility, and the framework cannot fix it.
-/

set_option autoImplicit false

namespace Framework.Sts2C.CustomEvents

/-- Four validators. -/
abbrev Node := Fin 4

/-- Votes carry a view and a value; complaints carry the abandoned view. -/
inductive Msg where
  /-- "In view `v` I vote for `k`." -/
  | vote (v : Nat) (k : Nat)
  /-- "I have given up on view `v`." -/
  | complain (v : Nat)
  deriving DecidableEq

/-- The protocol's own events: two timers. -/
inductive Ev where
  /-- The view timer expired: abandon the current view. -/
  | viewTimeout
  /-- The retransmission timer expired: re-broadcast our vote. -/
  | resend
  deriving DecidableEq

/-- Local state. The two deadlines are what `enabled` reads. -/
structure St where
  /-- Current view. -/
  view : Nat
  /-- What we voted for in the current view, if anything. -/
  voted : Option Nat
  /-- Votes heard, as `(view, value)` pairs. -/
  heard : Finset (Nat × Nat)
  /-- Time at which `viewTimeout` becomes enabled. -/
  timeoutAt : Time
  /-- Time at which `resend` becomes enabled. -/
  resendAt : Time
  deriving DecidableEq

/-- Vote once per view; re-broadcast on `resend`; abandon the view on
    `viewTimeout`. Both timer reactions push their own deadline forward. -/
def reaction (p : Node) (r : Time) (_view : View Node Msg) (s : St) :
    Event Node Msg Ev → NodeStepResult St Msg :=
  fun e =>
    match e with
    | .tick =>
        if s.voted = none then
          { state := { s with voted := some p.val, resendAt := r + 2 },
            send := {Msg.vote s.view p.val} }
        else
          { state := s, send := ∅ }
    | .wake =>
        -- A real joining protocol would start here; this toy has none.
        { state := s, send := ∅ }
    | .recv m =>
        match m.msg with
        | .vote v k => { state := { s with heard := insert (v, k) s.heard }, send := ∅ }
        | .complain _ => { state := s, send := ∅ }
    | .custom .viewTimeout =>
        { state := { s with view := s.view + 1, voted := none,
                            timeoutAt := r + 4, resendAt := r + 2 },
          send := {Msg.complain s.view} }
    | .custom .resend =>
        match s.voted with
        | some k => { state := { s with resendAt := r + 2 }, send := {Msg.vote s.view k} }
        | none => { state := s, send := ∅ }
/-- The protocol, lifting the deterministic `reaction` into the relational
    `Protocol.step`. -/
def proto : Protocol Node Msg St Ev where
  init _ := { view := 0, voted := none, heard := ∅, timeoutAt := 4, resendAt := 2 }
  step p r view s e res := res = reaction p r view s e
  total _ _ _ _ _ := ⟨_, rfl⟩
  enabled r s ev :=
    match ev with
    | .viewTimeout => s.timeoutAt ≤ r
    | .resend => s.resendAt ≤ r ∧ s.voted ≠ none

/-- A state in which the validator has voted, its resend timer is due, and its
    view timer is not. -/
def voted1 : St :=
  { view := 0, voted := some 1, heard := ∅, timeoutAt := 10, resendAt := 4 }

/-! ## The two events have independent conditions -/

/-- The view timer is not due at round 5… -/
example : ¬ proto.enabled 5 voted1 .viewTimeout := by simp [proto, voted1]

/-- …while the resend timer is, so only one of the two may fire here. -/
example : proto.enabled 5 voted1 .resend := by simp [proto, voted1]

/-- `resend` also requires having voted — a condition on state, not just on the
    round, which is why `enabled` takes the state. -/
example : ¬ proto.enabled 5 { voted1 with voted := none } .resend := by
  simp [proto, voted1]

/-! ## The two reactions differ, and both reschedule -/

/-- `viewTimeout` abandons the view and complains about the one it left. -/
example :
    (reaction 1 4 ∅ (proto.init 1) (.custom .viewTimeout)).send
      = {Msg.complain 0} := by decide

/-- …moving to the next view and pushing its own deadline out, so it is no longer
    enabled at the round it just fired in. -/
example :
    ((reaction 1 4 ∅ (proto.init 1) (.custom .viewTimeout)).state.view,
      (reaction 1 4 ∅ (proto.init 1) (.custom .viewTimeout)).state.timeoutAt)
      = (1, 8) := by decide

/-- `resend` re-broadcasts the existing vote rather than casting a new one. -/
example : (reaction 1 5 ∅ voted1 (.custom .resend)).send = {Msg.vote 0 1} := by
  decide

/-- And it too pushes its deadline forward; had it not, it would remain enabled
    and could fire again in the same round. -/
example : (reaction 1 5 ∅ voted1 (.custom .resend)).state.resendAt = 7 := by
  decide

end Framework.Sts2C.CustomEvents
