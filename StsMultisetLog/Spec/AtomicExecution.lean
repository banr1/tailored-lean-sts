import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import StsMultisetLog.Spec.Execution

/-!
# The atomic-round semantics — a second execution model over the same protocols

The fine-grained model (`Protocol.lean`) deliberately separates time passing
(`Action.advance`) from validators acting (`Action.tick`), which is what lets it express
clock desynchronization: a validator may tick to any reading above its clock, so skewed
and lagging clocks are real executions there. The price is that *synchronized* clocks are
not expressible as a per-configuration fact: between the `advance` and a validator's
catch-up tick there is a configuration whose awake clocks lag real time, so
`Execution.SynchronizedClocks` — awake ⇒ clock = time, at every configuration — excludes
every execution in which time moves past an awake validator, and excludes every tick
outright (its strict enabling `c[p].clock < t` contradicts the equality at the
pre-configuration). Both refutations are machine-checked in the consumer project that
found them.

This file is the other model: **one transition per instant**. `tickAllAwake t` moves time
to `t` and runs every awake validator's tick duty — preceded, for validators entering the
awake set at `t`, by their wake reaction — all against the pre-round snapshot, with the
sends summed into the log. Deliveries and adversarial sends remain ordinary interleaved
steps between rounds. Because no configuration exists in which some awake clocks have
moved and some have not, "every awake validator's clock reads real time" is a **theorem**
of this model (`Analysis/AtomicLemmas.lean`), not an assumption; so are the wake-report
and catch-up-order disciplines the fine model must assume
(`Diligent`, `WakePrecedesTick`, and the reading currency of ticks).

Everything node-level is shared with the fine model — `Protocol`, `Schedule`, `Config`,
`NodeStep`, `receive`, `applyNodeStepResult`, `Event` — so one `Protocol` value binds both
semantics and a protocol's own code cannot tell which model is running it. Only the
action type, the per-action spec, and the execution abbreviation are new.

Two conventions the atomic transition fixes, on purpose:

* **Same-instant sends are invisible at that instant.** Every round-`t` duty reads the
  snapshot; the round's sends enter `sent` in the successor. A message sent at `t` can be
  delivered from `t + 1` on. (Duties a protocol schedules `Δ` apart are separate rounds
  here — a round is one value of `Time`, not a protocol phase.)
* **A wake is reported before the first post-wake duty.** An entrant's `.wake` reaction
  runs first and its `.tick` reaction runs on the wake reaction's state, in the same
  transition — so a protocol that stamps its joining instant at the first trusted reading
  (the reason the fine model needs `WakePrecedesTick`) gets the true instant by
  construction.

Nondeterminism note: the round effect existentially picks one reaction per validator
(`Protocol.step` is a relation). No order among validators is needed or observable —
duties write only their own node's record, and the shared log is a commutative sum.
-/

set_option autoImplicit false

namespace Framework.StsMultisetLog

variable {Node Msg NodeState Ev : Type}

/-- Transition labels of the atomic-round model. The fine model's `advance`, `tick` and
    `wake` are all subsumed by `tickAllAwake`. -/
inductive AtomicAction (Node Msg Ev : Type) where
  /-- Real time becomes `t`, and every validator awake at `t` reacts at reading `t` —
      entrants to the awake set react to `.wake` first. -/
  | tickAllAwake (t : Time)
  /-- `m` is delivered to `p`, which reacts to it. -/
  | deliver (p : Node) (m : SignedMsg Node Msg)
  /-- A protocol-specific event fires at `p`. -/
  | custom (p : Node) (ev : Ev)
  /-- An adversarial validator signs an arbitrary message. -/
  | adversarial (p : Node) (m : Msg)

variable [DecidableEq Node] [DecidableEq Msg]
variable (Pr : Protocol Node Msg NodeState Ev) (S : Schedule Node)
    (a : AtomicAction Node Msg Ev) (t : Time)

/-- The validators entering the awake set at `t`: awake at `t`, asleep the instant
    before. These are the ones whose `.wake` reaction the round at `t` runs first. -/
def entrants : Finset Node :=
  S.awake (t : Int) \ S.awake ((t : Int) - 1)

variable (c c' : Config Node Msg NodeState)

/-- The effect of the round at `t`, read off the pre-round snapshot `c`:

    `w p` is the wake stage — a `.wake` reaction of `p`'s snapshot state for an entrant,
    and the inert result (same state, no sends) for everyone else, so that the tick stage
    and the send sum can be written uniformly over the awake set. `tk p` is `p`'s `.tick`
    reaction at reading `t`, from the wake stage's state. The successor holds, for each
    awake validator, its tick result and the clock at `t`, with view untouched (delivery
    is a separate action); sleepers are untouched; the log gains every stage's sends,
    each signed by its sender.

    In plain words: at instant `t`, every awake validator — freshly woken ones first
    informed of their waking — runs its tick duty against what it held when the instant
    began, and everything sent lands on the network together. -/
def RoundEffect : Prop :=
  ∃ w tk : Node → NodeStepResult NodeState Msg,
    (∀ p ∈ entrants S t, Pr.step p c[p].clock c[p].view c[p].st .wake (w p)) ∧
    (∀ p, p ∉ entrants S t → w p = { state := c[p].st, send := 0 }) ∧
    (∀ p ∈ S.awake (t : Int), Pr.step p t c[p].view (w p).state .tick (tk p)) ∧
    c' = { time := t,
           nodes := fun q => if q ∈ S.awake (t : Int) then
               { clock := t, st := (tk q).state, view := c[q].view }
             else c[q],
           sent := c.sent
             + (S.awake (t : Int)).sum
                 (fun q => ((w q).send + (tk q).send).map (SignedMsg.mk q)) }

omit [DecidableEq Msg] in
/-- The round is always possible: choose a reaction per validator from
    `Protocol.total`. -/
theorem roundEffect_total : ∃ c', RoundEffect Pr S t c c' := by
  classical
  choose wf hwf using fun p => Pr.total p c[p].clock c[p].view c[p].st .wake
  refine ?_
  set w : Node → NodeStepResult NodeState Msg := fun p =>
    if p ∈ entrants S t then wf p else { state := c[p].st, send := 0 } with hwdef
  choose tk htk using fun p => Pr.total p t c[p].view (w p).state .tick
  refine ⟨_, w, tk, ?_, ?_, fun p _ => htk p, rfl⟩
  · intro p hp
    simpa [hwdef, if_pos hp] using hwf p
  · intro p hp
    simp [hwdef, if_neg hp]

/-- Each atomic action's enabling condition and effect. Deliveries, protocol events and
    adversarial sends are verbatim the fine model's; only the round is new, and it is
    enabled exactly one instant ahead of the current time, so time is stepwise by
    construction. -/
def atomicSpec : AtomicAction Node Msg Ev → ActionSpec Node Msg NodeState
  | .tickAllAwake t => {
      Enabled c := c.time + 1 = t
      Effect c c' := RoundEffect Pr S t c c'
      feasible c _ := roundEffect_total Pr S t c }
  | .deliver p m => {
      Enabled c := m ∈ c.sent ∧ p ∈ S.awake (c.time : Int)
      Effect c c' := NodeStep Pr p (.recv m) (receive p m c) c'
      feasible _ _ := nodeStep_total Pr p (.recv m) _ }
  | .custom p ev => {
      Enabled c := p ∈ S.awake (c.time : Int) ∧ Pr.enabled c[p].clock c[p].st ev
      Effect c c' := NodeStep Pr p (.custom ev) c c'
      feasible _ _ := nodeStep_total Pr p (.custom ev) _ }
  | .adversarial p m => {
      Enabled c := p ∈ S.adv (c.time : Int)
      Effect c c' := c' = { c with sent := ⟨p, m⟩ ::ₘ c.sent }
      feasible _ _ := ⟨_, rfl⟩ }

/-- The atomic step relation: enabled, and then the effect. -/
def AtomicStep : Prop :=
  (atomicSpec Pr S a).Enabled c ∧ (atomicSpec Pr S a).Effect c c'

/-- The protocol as a transition system under the atomic-round semantics. Initial
    configurations are the fine model's own. -/
def atomicSystem (Node Msg NodeState Ev : Type) [DecidableEq Node] [DecidableEq Msg]
    (Pr : Protocol Node Msg NodeState Ev) (S : Schedule Node) :
    System (Config Node Msg NodeState) (AtomicAction Node Msg Ev) where
  Init := Init Pr
  Step := AtomicStep Pr S

/-- Executions under the atomic-round semantics. -/
abbrev AtomicExec (Pr : Protocol Node Msg NodeState Ev) (S : Schedule Node) :=
  Execution (atomicSystem Node Msg NodeState Ev Pr S)

variable {Pr} {S} in
/-- Is `p` awake after `i` steps? The atomic model's spelling of
    `Execution.Awake`. -/
def AtomicAwake (x : AtomicExec Pr S) (i : Nat) (p : Node) : Prop :=
  p ∈ S.awake (x[i].time : Int)

variable {Pr} {S} in
/-- Is `p` still honest after `i` steps? -/
def AtomicHonest (x : AtomicExec Pr S) (i : Nat) (p : Node) : Prop :=
  p ∉ S.adv (x[i].time : Int)

end Framework.StsMultisetLog
