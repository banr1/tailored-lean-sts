import Framework.Sts2MX.Spec.Protocol

/-!
# What the definitions do

Everything proved about `Framework.Sts2MX.Protocol`, kept out of it so that the
specification reads as a specification. Nothing here is needed to *state* the model; it is
needed to work with it.

Four groups, in dependency order:

* **Field lemmas.** A read-back lemma per helper saying what `c[p]` is afterwards, then the
  per-field consequences that invariant proofs actually cite.
* **`applyNodeStepResult_surjective`.** Every `p`-signed extension of the log is some
  reaction's doing, so the model has no unreachable successors.
* **The two eliminators.** `Step.elim` binds a reaction and gives a concrete successor;
  `Step.elimR` leaves the successor abstract and gives a `NodeStep`. Which to use depends on
  whether the goal wants to name the successor.
* **The frame lemmas.** What a `NodeStep` may and may not touch, with `nodeStep_of_frame`
  proving that characterisation complete.
-/

set_option autoImplicit false

namespace Framework.Sts2MX

variable {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]

/-! Every repeated binder below comes from here. Declared in the order that reproduces each
signature as it was written out, so no call site moves; the `Frame` section further down
redeclares `p`, `pre` and `c'` implicitly, which simply replaces them from there on. -/

variable {Pr : Protocol Node Msg NodeState Ev} {S : Schedule Node}
    (q : Node) (res : NodeStepResult NodeState Msg) (m : SignedMsg Node Msg) (t : Time)
    (d : Config Node Msg NodeState) (p : Node) (pre c' : Config Node Msg NodeState)

/-! ### What the helpers do to each field

Two layers. First a read-back lemma per definition, saying what `c[p]` is after it — these
are what make brackets work as the normal form, since `simp` cannot otherwise reduce a
bracket applied to a literal record. Then the per-field consequences, which are what
invariant proofs actually cite.

`Config.setNode_apply` sits above both: since every setter goes through `setNode`, it is
the one lemma that turns a write into an `if`, and the read-back lemmas below are `rfl`
on top of it.

Only the second layer is `@[simp]`. The read-back lemmas are cited explicitly, because as
`simp` lemmas they fire first and expand a bracket into nested `if`s, after which the field
lemmas no longer match — the same shadowing that once made `applyNodeStepResult_clock` unusable, in the
opposite direction. -/

omit [DecidableEq Msg] in
theorem applyNodeStepResult_getElem :
    (applyNodeStepResult q res d)[p] = if q = p then { d[q] with st := res.state } else d[p] :=
  rfl

theorem receive_getElem :
    (receive q m d)[p] = if q = p then { d[q] with view := insert m d[q].view } else d[p] :=
  rfl

omit [DecidableEq Msg] in
theorem setClock_getElem :
    (setClock q t d)[p] = if q = p then { d[q] with clock := t } else d[p] := rfl

omit [DecidableEq Msg] in
@[simp] theorem applyNodeStepResult_clock :
    (applyNodeStepResult q res d)[p].clock = d[p].clock := by
  by_cases hpq : q = p <;> simp [applyNodeStepResult_getElem, hpq]

omit [DecidableEq Msg] in
@[simp] theorem applyNodeStepResult_view :
    (applyNodeStepResult q res d)[p].view = d[p].view := by
  by_cases hpq : q = p <;> simp [applyNodeStepResult_getElem, hpq]

omit [DecidableEq Msg] in
@[simp] theorem applyNodeStepResult_sent :
    (applyNodeStepResult q res d).sent = d.sent + res.send.map (SignedMsg.mk q) := rfl

@[simp] theorem receive_clock :
    (receive q m d)[p].clock = d[p].clock := by
  by_cases hpq : q = p <;> simp [receive_getElem, hpq]

@[simp] theorem receive_view_self :
    (receive q m d)[q].view = insert m d[q].view := by simp [receive_getElem]

@[simp] theorem receive_view_other (h : p ≠ q) :
    (receive q m d)[p].view = d[p].view := by simp [receive_getElem, Ne.symm h]

/-- What a reaction added to the log, as a multiset difference. Not `simp`: it is the
    inverse direction of `applyNodeStepResult_sent` and would loop with it. -/
theorem applyNodeStepResult_sent_sub :
    (applyNodeStepResult q res d).sent - d.sent = res.send.map (SignedMsg.mk q) := by
  ext a; simp [applyNodeStepResult]

@[simp] theorem receive_sent :
    (receive q m d).sent = d.sent := rfl

omit [DecidableEq Msg] in
@[simp] theorem setClock_view :
    (setClock q t d)[p].view = d[p].view := by
  by_cases hpq : q = p <;> simp [setClock_getElem, hpq]

omit [DecidableEq Msg] in
@[simp] theorem setClock_sent :
    (setClock q t d).sent = d.sent := rfl

/-! `clock_mono` used to live here, proved from `tick` incrementing by one. It is gone:
a tick may now set any reading, so clock monotonicity is an *assumption*
(`Execution.ClocksMonotone`) rather than a fact of the step relation. That is the point
of weakening the spec — the old version made a scheduling decision look like a theorem. -/

/-- …and every extension of the log by messages `p` signed is produced by some reaction, so
    `applyNodeStepResult p · pre` is onto those, not merely injective. Together with the round
    trip, reactions and reachable successors correspond exactly.

    This is what fails when `send` is a `Finset`: a delta holding one message twice is then
    unreachable, and any characterisation of the successors has to say so. -/
theorem applyNodeStepResult_surjective
    (hle : pre.sent ≤ c'.sent) (hp : ∀ m ∈ c'.sent - pre.sent, m.sender = p) :
    c'.sent = (applyNodeStepResult p (extract p pre c') pre).sent := by
  have hid : (c'.sent - pre.sent).map (fun m => SignedMsg.mk p m.msg) = c'.sent - pre.sent := by
    refine Multiset.map_congr rfl ?_ |>.trans (Multiset.map_id _)
    intro m hm
    have : m.sender = p := hp m hm
    cases m; simp_all
  -- the read-back lemmas live further down the file, so go through the definition
  show c'.sent = pre.sent + ((c'.sent - pre.sent).map SignedMsg.msg).map (SignedMsg.mk p)
  rw [Multiset.map_map, Function.comp_def, hid]
  exact (add_tsub_cancel_of_le hle).symm

/-- Case analysis on a step, one case per action, with the successor already computed.

    `Step` is a `def` — a conjunction — so `cases` cannot split it by action; every proof
    would otherwise open with `obtain ⟨-, res, -, h⟩; subst h` in each case. This does
    that once. Each case receives the action's enabling condition, the effect the
    protocol permitted, and a goal whose successor is the concrete configuration rather
    than an unknown constrained by an equation.

    It is the non-inductive equivalent of `cases` on an inductive step relation, and it
    is derived from `spec`, so it cannot drift from the step relation. -/
theorem Step.elim
    {motive : Action Node Msg Ev → Config Node Msg NodeState → Config Node Msg NodeState → Prop}
    {a : Action Node Msg Ev} {c c' : Config Node Msg NodeState} (h : Step Pr S a c c')
    (advance : ∀ (d : Config Node Msg NodeState) (t : Time),
      motive (.advance t) d { d with time := t })
    (tick : ∀ (d : Config Node Msg NodeState) (p : Node) (t : Time)
        (res : NodeStepResult NodeState Msg),
      (spec Pr S (.tick p t)).Enabled d →
      Pr.step p (setClock p t d)[p].clock (setClock p t d)[p].view (setClock p t d)[p].st
        .tick res →
      motive (.tick p t) d (applyNodeStepResult p res (setClock p t d)))
    (deliver : ∀ (d : Config Node Msg NodeState) (p : Node) (m : SignedMsg Node Msg)
        (res : NodeStepResult NodeState Msg),
      (spec Pr S (.deliver p m)).Enabled d →
      Pr.step p (receive p m d)[p].clock (receive p m d)[p].view (receive p m d)[p].st
        (.recv m) res →
      motive (.deliver p m) d (applyNodeStepResult p res (receive p m d)))
    (wake : ∀ (d : Config Node Msg NodeState) (p : Node) (res : NodeStepResult NodeState Msg),
      (spec Pr S (.wake p)).Enabled d →
      Pr.step p d[p].clock d[p].view d[p].st .wake res →
      motive (.wake p) d (applyNodeStepResult p res d))
    (custom : ∀ (d : Config Node Msg NodeState) (p : Node) (ev : Ev) (res : NodeStepResult NodeState Msg),
      (spec Pr S (.custom p ev)).Enabled d →
      Pr.step p d[p].clock d[p].view d[p].st (.custom ev) res →
      motive (.custom p ev) d (applyNodeStepResult p res d))
    (adversarial : ∀ (d : Config Node Msg NodeState) (p : Node) (m : Msg),
      (spec Pr S (.adversarial p m)).Enabled d →
      motive (.adversarial p m) d { d with sent := ⟨p, m⟩ ::ₘ d.sent }) :
    motive a c c' := by
  cases a with
  | advance t => obtain ⟨-, rfl⟩ := h; exact advance c t
  | tick p t =>
      obtain ⟨he, hr⟩ := h
      obtain ⟨res, hp, rfl⟩ := (nodeStep_iff_exists Pr p .tick _ _).1 hr
      exact tick c p t res he hp
  | deliver p m =>
      obtain ⟨he, hr⟩ := h
      obtain ⟨res, hp, rfl⟩ := (nodeStep_iff_exists Pr p (.recv m) _ _).1 hr
      exact deliver c p m res he hp
  | wake p =>
      obtain ⟨he, hr⟩ := h
      obtain ⟨res, hp, rfl⟩ := (nodeStep_iff_exists Pr p .wake _ _).1 hr
      exact wake c p res he hp
  | custom p ev =>
      obtain ⟨he, hr⟩ := h
      obtain ⟨res, hp, rfl⟩ := (nodeStep_iff_exists Pr p (.custom ev) _ _).1 hr
      exact custom c p ev res he hp
  | adversarial p m => obtain ⟨he, rfl⟩ := h; exact adversarial c p m he

/-- Case analysis on a step, leaving the successor **abstract** and handing each reacting
    case the `NodeStep` that constrains it.

    The companion to `Step.elim`, and the reason both exist. This attempt has two equivalent
    ways to say a reaction happened — `NodeStep` as defined, and the existential
    `nodeStep_iff_exists` proves it equal to — and they suit different proofs:

    * `Step.elim` binds a reaction and gives a **concrete** successor. Use it when the goal
      is about that term: `sent_mono` needs `d.sent ≤ (applyNodeStepResult …).sent`, and a
      concrete successor is exactly what makes that immediate.
    * `Step.elimR` leaves the successor as it is and gives a `NodeStep` about it. Use it when
      the goal is about an arbitrary `c'` and the frame lemmas are what the proof needs —
      `Justified` is the example, where replacing `c'` by a term buys nothing.

    Four of the six cases are one `exact` with no destructuring, because `Step` already *is*
    `Enabled ∧ NodeStep`. Going through the wrong eliminator costs a `nodeStep_iff_exists`
    conversion in every reacting case; that is the whole of the difference. -/
theorem Step.elimR
    {motive : Action Node Msg Ev → Config Node Msg NodeState →
      Config Node Msg NodeState → Prop}
    {a : Action Node Msg Ev} {c c' : Config Node Msg NodeState} (h : Step Pr S a c c')
    (advance : ∀ (d : Config Node Msg NodeState) (t : Time),
      motive (.advance t) d { d with time := t })
    (tick : ∀ (d d' : Config Node Msg NodeState) (p : Node) (t : Time),
      (spec Pr S (.tick p t)).Enabled d → NodeStep Pr p .tick (setClock p t d) d' →
      motive (.tick p t) d d')
    (deliver : ∀ (d d' : Config Node Msg NodeState) (p : Node) (m : SignedMsg Node Msg),
      (spec Pr S (.deliver p m)).Enabled d → NodeStep Pr p (.recv m) (receive p m d) d' →
      motive (.deliver p m) d d')
    (wake : ∀ (d d' : Config Node Msg NodeState) (p : Node),
      (spec Pr S (.wake p)).Enabled d → NodeStep Pr p .wake d d' → motive (.wake p) d d')
    (custom : ∀ (d d' : Config Node Msg NodeState) (p : Node) (ev : Ev),
      (spec Pr S (.custom p ev)).Enabled d → NodeStep Pr p (.custom ev) d d' →
      motive (.custom p ev) d d')
    (adversarial : ∀ (d : Config Node Msg NodeState) (p : Node) (m : Msg),
      (spec Pr S (.adversarial p m)).Enabled d →
      motive (.adversarial p m) d { d with sent := ⟨p, m⟩ ::ₘ d.sent }) :
    motive a c c' := by
  cases a with
  | advance t => obtain ⟨-, rfl⟩ := h; exact advance c t
  | tick p t => exact tick c c' p t h.1 h.2
  | deliver p m => exact deliver c c' p m h.1 h.2
  | wake p => exact wake c c' p h.1 h.2
  | custom p ev => exact custom c c' p ev h.1 h.2
  | adversarial p m => obtain ⟨he, rfl⟩ := h; exact adversarial c p m he

/-! ### One invariant, through the eliminator

Not needed by the framework, but it is what `Step.elim` is for: each case arrives with its
successor already concrete, so the proof is one line per action with no destructuring.
(`clock_mono` used to sit beside it — see the note above for why it is gone.) -/

/-- The network never forgets. -/
theorem sent_mono {a : Action Node Msg Ev} {c c' : Config Node Msg NodeState}
    (h : Step Pr S a c c') : c.sent ≤ c'.sent := by
  refine h.elim (motive := fun _ d d' => d.sent ≤ d'.sent) ?_ ?_ ?_ ?_ ?_ ?_ <;> intros <;>
    first
      | exact le_rfl
      | exact Multiset.le_iff_exists_add.mpr ⟨_, rfl⟩
      | exact Multiset.le_cons_self _ _

/-! ### What a reaction may and may not touch

The frame conditions, as *theorems* about `applyNodeStepResult` rather than as its
definition. Stating them this way keeps the frame problem away: a field added to `Config` or
`Local` is left alone because the function does not mention it, and these lemmas would simply
not mention it either — whereas a frame *relation* would let the new field change arbitrarily
until someone remembered a conjunct for it.

`nodeStep_of_frame` closes the loop: the six are not merely necessary but sufficient. That is
what `NodeStepResult.send` being a multiset buys — with a `Finset` there, a successor whose
log gained one message twice satisfies all six and is still unreachable, so a seventh
condition (`Nodup` on the delta) would be needed. -/

section Frame

variable {p : Node} {e : Event Node Msg Ev} {pre c' : Config Node Msg NodeState}

/-- Two configurations agreeing on every field are equal. -/
theorem Config.ext' {c d : Config Node Msg NodeState} (ht : c.time = d.time)
    (hn : ∀ q, c.nodes q = d.nodes q) (hs : c.sent = d.sent) : c = d := by
  obtain ⟨t₁, n₁, s₁⟩ := c
  obtain ⟨t₂, n₂, s₂⟩ := d
  simp only [Config.mk.injEq]
  exact ⟨ht, funext hn, hs⟩

/-- Real time is the environment's, not a reacting validator's. -/
theorem NodeStep.time (h : NodeStep Pr p e pre c') : c'.time = pre.time := by
  conv_lhs => rw [h.2]
  rfl

/-- No other validator is touched. -/
theorem NodeStep.other (h : NodeStep Pr p e pre c') (q : Node) (hq : q ≠ p) : c'[q] = pre[q] := by
  conv_lhs => rw [h.2]
  simp [applyNodeStepResult_getElem, Ne.symm hq]

/-- `p`'s own clock is not touched: only a `tick` moves it, and it does so before the
    reaction runs. -/
theorem NodeStep.clock (h : NodeStep Pr p e pre c') : c'[p].clock = pre[p].clock := by
  conv_lhs => rw [h.2]
  simp

/-- Nor is `p`'s view: only a delivery adds to it, again before the reaction runs. -/
theorem NodeStep.view (h : NodeStep Pr p e pre c') : c'[p].view = pre[p].view := by
  conv_lhs => rw [h.2]
  simp

/-- The log only grows. -/
theorem NodeStep.sent_le (h : NodeStep Pr p e pre c') : pre.sent ≤ c'.sent := by
  conv_rhs => rw [h.2]
  exact Multiset.le_iff_exists_add.mpr ⟨_, rfl⟩

/-- And it grows only by messages `p` signed. -/
theorem NodeStep.sent_signed (h : NodeStep Pr p e pre c') (m : SignedMsg Node Msg)
    (hm : m ∈ c'.sent - pre.sent) : m.sender = p := by
  have hdelta : c'.sent - pre.sent = (extract p pre c').send.map (SignedMsg.mk p) := by
    conv_lhs => rw [h.2]
    exact applyNodeStepResult_sent_sub _ _ _
  rw [hdelta] at hm
  obtain ⟨x, -, rfl⟩ := Multiset.mem_map.1 hm
  rfl

/-- The converse: the six conditions characterise a reaction completely. -/
theorem nodeStep_of_frame
    (hstep : Pr.step p pre[p].clock pre[p].view pre[p].st e (extract p pre c'))
    (htime : c'.time = pre.time) (hother : ∀ q, q ≠ p → c'[q] = pre[q])
    (hclock : c'[p].clock = pre[p].clock) (hview : c'[p].view = pre[p].view)
    (hle : pre.sent ≤ c'.sent) (hsigned : ∀ m ∈ c'.sent - pre.sent, m.sender = p) :
    NodeStep Pr p e pre c' := by
  refine ⟨hstep, Config.ext' htime (fun q => ?_) ?_⟩
  -- both sides in bracket form, so the read-back lemmas match
  · show c'[q] = (applyNodeStepResult p (extract p pre c') pre)[q]
    by_cases hq : q = p
    · subst hq
      simp only [applyNodeStepResult_getElem, Config.setNode_apply, if_pos rfl]
      rw [← hclock, ← hview]
      -- what is left is `c'[q]` written out field by field
      simp [extract]
    · rw [hother q hq]
      simp [applyNodeStepResult_getElem, Ne.symm hq]
  · exact applyNodeStepResult_surjective p pre c' hle hsigned

end Frame

end Framework.Sts2MX
