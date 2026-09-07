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


/-! ### Reading the `tickAllAwake` successor, and case analysis on an atomic step -/

omit [DecidableEq Msg] in
/-- An awake validator's record after the `tickAllAwake` transition: its tick result,
    its clock at `t`, its view untouched. -/
theorem tickAllAwakeUpdate_getElem_awake {t : Time} {c : Config Node Msg NodeState}
    {w tk : Node → NodeStepResult NodeState Msg} {q : Node}
    (hq : q ∈ S.awake (t : Int)) :
    (tickAllAwakeUpdate S t c w tk)[q]
      = { clock := t, st := (tk q).state, view := c[q].view } := by
  show (if q ∈ S.awake (t : Int) then _ else _) = _
  rw [if_pos hq]

omit [DecidableEq Msg] in
/-- A sleeping validator's record is untouched by the `tickAllAwake` transition. -/
theorem tickAllAwakeUpdate_getElem_asleep {t : Time} {c : Config Node Msg NodeState}
    {w tk : Node → NodeStepResult NodeState Msg} {q : Node}
    (hq : q ∉ S.awake (t : Int)) :
    (tickAllAwakeUpdate S t c w tk)[q] = c[q] := by
  show (if q ∈ S.awake (t : Int) then _ else _) = _
  rw [if_neg hq]

omit [DecidableEq Msg] in
@[simp] theorem tickAllAwakeUpdate_time {t : Time} {c : Config Node Msg NodeState}
    {w tk : Node → NodeStepResult NodeState Msg} :
    (tickAllAwakeUpdate S t c w tk).time = t := rfl

/-- Case analysis on an atomic step, binding each case's witnesses and a **concrete**
    successor — the atomic counterpart of `Step.elim`. -/
theorem AtomicStep.elim
    {motive : AtomicAction Node Msg Ev → Config Node Msg NodeState →
      Config Node Msg NodeState → Prop}
    {a : AtomicAction Node Msg Ev} {c c' : Config Node Msg NodeState}
    (h : AtomicStep Pr S a c c')
    (tickAllAwake : ∀ (d : Config Node Msg NodeState) (t : Time)
        (w tk : Node → NodeStepResult NodeState Msg),
      d.time + 1 = t →
      (∀ p, TickAllAwakeWake Pr S t d p (w p)) →
      (∀ p ∈ S.awake (t : Int), Pr.step p t d[p].view (w p).state .tick (tk p)) →
      motive (.tickAllAwake t) d (tickAllAwakeUpdate S t d w tk))
    (deliver : ∀ (d : Config Node Msg NodeState) (p : Node) (m : SignedMsg Node Msg)
        (res : NodeStepResult NodeState Msg),
      (atomicSpec Pr S (.deliver p m)).Enabled d →
      Pr.step p (receive p m d)[p].clock (receive p m d)[p].view (receive p m d)[p].st
        (.recv m) res →
      motive (.deliver p m) d (applyNodeStepResult p res (receive p m d)))
    (custom : ∀ (d : Config Node Msg NodeState) (p : Node) (ev : Ev)
        (res : NodeStepResult NodeState Msg),
      (atomicSpec Pr S (.custom p ev)).Enabled d →
      Pr.step p d[p].clock d[p].view d[p].st (.custom ev) res →
      motive (.custom p ev) d (applyNodeStepResult p res d))
    (adversarial : ∀ (d : Config Node Msg NodeState) (p : Node) (m : Msg),
      (atomicSpec Pr S (.adversarial p m)).Enabled d →
      motive (.adversarial p m) d { d with sent := ⟨p, m⟩ ::ₘ d.sent }) :
    motive a c c' := by
  cases a with
  | tickAllAwake t =>
      obtain ⟨hen, w, tk, hw, htk, rfl⟩ := h
      exact tickAllAwake c t w tk hen hw htk
  | deliver p m =>
      obtain ⟨he, hr⟩ := h
      obtain ⟨res, hp, rfl⟩ := (nodeStep_iff_exists Pr p (.recv m) _ _).1 hr
      exact deliver c p m res he hp
  | custom p ev =>
      obtain ⟨he, hr⟩ := h
      obtain ⟨res, hp, rfl⟩ := (nodeStep_iff_exists Pr p (.custom ev) _ _).1 hr
      exact custom c p ev res he hp
  | adversarial p m =>
      obtain ⟨he, rfl⟩ := h
      exact adversarial c p m he

/-- Reaching an instant means its `tickAllAwake` transition happened: at the step where
    time became `t`, the label was `tickAllAwake t` — no other action moves time. The
    atomic counterpart of the fine model's `duty_fires` machinery, with no fairness
    assumption to pay. -/
theorem tickAllAwake_of_time (x : AtomicExec Pr S) (k : Nat) {t : Time}
    (ht : x[k].time = t) (h0 : t ≠ 0) :
    ∃ j, j < k ∧ x.lbl j = .tickAllAwake t ∧ x[j + 1].time = t ∧ x[j].time + 1 = t := by
  induction k with
  | zero =>
      obtain ⟨ht0, -, -⟩ := x.init
      exact absurd (ht.symm.trans ht0) h0
  | succ k ih =>
      by_cases hsame : x[k + 1].time = x[k].time
      · obtain ⟨j, hj, hrest⟩ := ih ((hsame.symm.trans ht : x[k].time = t))
        exact ⟨j, Nat.lt_succ_of_lt hj, hrest⟩
      · have hs := x.step k
        cases hl : x.lbl k with
        | tickAllAwake t' =>
            rw [hl] at hs
            obtain ⟨hen, w, tk, -, -, hc⟩ := hs
            have ht' : x[k + 1].time = t' := by
              show (x.cfg (k + 1)).time = t'
              rw [hc]; rfl
            have htt : t' = t := ht'.symm.trans ht
            subst htt
            refine ⟨k, Nat.lt_succ_self k, hl, ht' , ?_⟩
            exact hen
        | deliver q m =>
            rw [hl] at hs
            obtain ⟨-, hns⟩ := hs
            exact absurd hns.time hsame
        | custom q ev =>
            rw [hl] at hs
            obtain ⟨-, hns⟩ := hs
            exact absurd hns.time hsame
        | adversarial q m =>
            rw [hl] at hs
            exact absurd
              (show (x.cfg (k + 1)).time = (x.cfg k).time by rw [hs.2]) hsame

end Framework.StsMultisetLog
