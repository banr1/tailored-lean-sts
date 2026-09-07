import StsMultisetLog.Spec.AtomicExecution
import StsMultisetLog.Analysis.Lemmas

/-!
# What the atomic model gives for free

The two facts the fine-grained model can only assume — and, per-configuration, cannot
even satisfiably assume (see the header of `Spec/AtomicExecution.lean`) — are theorems
here: time is stepwise, and **every awake validator's clock reads real time at every
configuration**. There is no configuration between the time increment and the catch-up,
because there is no separate catch-up.

Proof note: the statements read `x[i]`, the goals are moved to the underlying `x.cfg i`
spelling by a `show` (the two are definitionally equal, and the step facts come out of
`x.step` in `cfg` spelling, which is what `rw` needs).
-/

set_option autoImplicit false

namespace Framework.StsMultisetLog

variable {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
variable {Pr : Protocol Node Msg NodeState Ev} {S : Schedule Node}

/-- Time is stepwise by construction: the `tickAllAwake` transition is enabled exactly
    one instant ahead, and no other action moves time. -/
theorem atomic_time_stepwise (x : AtomicExec Pr S) (i : Nat) :
    x[i + 1].time = x[i].time ∨ x[i + 1].time = x[i].time + 1 := by
  show (x.cfg (i + 1)).time = (x.cfg i).time ∨
    (x.cfg (i + 1)).time = (x.cfg i).time + 1
  have hs := x.step i
  cases hl : x.lbl i with
  | tickAllAwake t =>
      rw [hl] at hs
      obtain ⟨hen, w, tk, -, -, hc⟩ := hs
      right
      rw [hc]
      exact hen.symm
  | deliver q m =>
      rw [hl] at hs
      obtain ⟨-, -, hc⟩ := hs
      left; rw [hc]; rfl
  | custom q ev =>
      rw [hl] at hs
      obtain ⟨-, -, hc⟩ := hs
      left; rw [hc]; rfl
  | adversarial q m =>
      rw [hl] at hs
      left; rw [hs.2]

/-- **Synchronized clocks are a theorem of the atomic model**: at every configuration,
    every awake validator's clock reads real time. The fine model must assume this
    (`SynchronizedClocks`) and, read per-configuration, cannot — the configurations
    between its `advance` and the catch-up ticks refute it. Here those configurations do
    not exist: the `tickAllAwake` transition that moves time writes every awake clock in the same step. -/
theorem atomic_awake_clock_eq_time (x : AtomicExec Pr S) (i : Nat) (p : Node)
    (haw : p ∈ S.awake (x[i].time : Int)) : x[i][p].clock = x[i].time := by
  induction i with
  | zero =>
      obtain ⟨ht0, hn, -⟩ := x.init
      show ((x.cfg 0)[p]).clock = (x.cfg 0).time
      rw [hn p, ht0]
  | succ i ih =>
      replace haw : p ∈ S.awake (((x.cfg (i + 1)).time : Int)) := haw
      show ((x.cfg (i + 1))[p]).clock = (x.cfg (i + 1)).time
      have hs := x.step i
      cases hl : x.lbl i with
      | tickAllAwake t =>
          rw [hl] at hs
          obtain ⟨-, w, tk, -, -, hc⟩ := hs
          have ht : (x.cfg (i + 1)).time = t := by rw [hc]; rfl
          rw [ht] at haw ⊢
          rw [hc]
          show ((tickAllAwakeUpdate S t (x.cfg i) w tk)[p]).clock = t
          unfold tickAllAwakeUpdate
          show (if p ∈ S.awake (t : Int) then
              ({ clock := t, st := (tk p).state, view := (x.cfg i)[p].view } :
                Local Node Msg NodeState)
            else (x.cfg i)[p]).clock = t
          rw [if_pos haw]
      | deliver q m =>
          rw [hl] at hs
          obtain ⟨-, hns⟩ := hs
          have ht : (x.cfg (i + 1)).time = (x.cfg i).time := hns.time
          rw [ht] at haw ⊢
          rw [hns.2]
          simp only [applyNodeStepResult_clock, receive_clock]
          exact ih haw
      | custom q ev =>
          rw [hl] at hs
          obtain ⟨-, hns⟩ := hs
          have ht : (x.cfg (i + 1)).time = (x.cfg i).time := hns.time
          rw [ht] at haw ⊢
          rw [hns.2]
          simp only [applyNodeStepResult_clock]
          exact ih haw
      | adversarial q m =>
          rw [hl] at hs
          have ht : (x.cfg (i + 1)).time = (x.cfg i).time := by rw [hs.2]
          rw [ht] at haw ⊢
          rw [hs.2]
          exact ih haw

/-- Any two awake validators' clocks agree, at every configuration — in particular,
    with every honest validator always awake, all honest clocks are equal
    everywhere. -/
theorem atomic_awake_clocks_agree (x : AtomicExec Pr S) (i : Nat) (p q : Node)
    (hp : p ∈ S.awake (x[i].time : Int)) (hq : q ∈ S.awake (x[i].time : Int)) :
    x[i][p].clock = x[i][q].clock := by
  rw [atomic_awake_clock_eq_time x i p hp, atomic_awake_clock_eq_time x i q hq]

end Framework.StsMultisetLog
