import Examples.StsMultisetLog.majorum.Analysis.Proofs.Provenance2

/-!
# The Algorithm 5 → Algorithm 2 simulation (Lemma 10, stage B)

Given any execution of Algorithm 5, `simulate` builds an execution of Algorithm 2 over
the **same schedule and the same label stream**: ticks, wakes and time advances carry
over unchanged, adversarial injections are routed through the correspondence table —
verbatim until the injected message collides with an honest tick's send, whose
counterpart then stands in for it, else the simulated log would hold a message its
deliveries never carry and `Synchrony` would fail on the simulated run — and
deliveries are routed through the same step-indexed correspondence
table `τ` — the framework's `deliver p m` demands `m ∈ sent`, so the simulated
execution delivers *its own* counterpart of each Algorithm-5 message. That table is the
paper's adversary decision (iv) made concrete: whenever a validator's tick sends a
message in both executions, `τ` pairs them.

Algorithm 2's nondeterministic blank is pinned to `⟨[], 0⟩` at every tick, making the
whole construction deterministic; each step's configuration is *defined* as the
framework's effect term, so the step proofs are shape-only.

This file is deliberately **analysis-free**: it establishes the execution and the cheap
structural invariants (time, clocks, `activeAt`, the send-correspondence and the
`τ`-image of the log). Definition 9's MFC-equivalence — Lemma 10's content — is a slot
induction over the completed execution, in stage C.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 400

namespace Majorum

open the framework's flat multiset-log flavour Classical

variable {Node Tx : Type} [DecidableEq Node] [DecidableEq Tx] [Fintype Node]
  {Q : Params} {S : Schedule Node} {n kappa : Nat} {pool : Nat → Tx}
  {proposer : Nat → Node}

local notation "Pr5" => protocol (components n kappa pool proposer) Q
local notation "Pr2" => protocol2 Q n kappa pool proposer

/-- Algorithm 2's messages and Algorithm 5's share one type. -/
local notation "M" => Msg (Chain Tx) (QCert Node Tx)

/-- **Definition 8** (`Definition 8, arXiv:2601.03862v1 p.18`), repaired: two messages
    are *dynamically equivalent* iff they differ in at most their finality-derived
    components — votes in the fin-vote (the paper's clause, verbatim), proposes in
    everything but the proposed chain and slot.

    The paper's propose clause frees only the greatest-justified-checkpoint field, but
    that is inconsistent with its own `fastconfirm`: the GJ-branch substitutes the
    justified chain for `(chC, QC)`, so an Algorithm-5 proposal can differ from its
    Algorithm-2 counterpart in those fields whenever slot `t−1` lacked a fast-confirm
    quorum, and Lemma 10's condition 1 is false as worded (ninth finding, `CONTEXT.md`
    2026-08-05). Since `fastconfirm` is finality-coupled by construction, the whole
    `(chC, QC)` pair is finality-*derived* and this definition frees it. Nothing
    downstream loses strength — the transfers read only the proposed chain and slot,
    and the frozen-chain divergence `chC` feeds is handled by bounding, not equality.
    The tighter substitution-aware alternative (free the pair only when
    `QC = none ∧ chC` equals the message's own GJ chain) is recorded here should the
    full-strength condition 1 ever be wanted. -/
def DynEq : M → M → Prop
  | .propose chp _ _ _ t, .propose chp' _ _ _ t' => chp = chp' ∧ t = t'
  | .vote e _ _ t, .vote e' _ _ t' => e = e' ∧ t = t'
  | _, _ => False

/-- The blank Algorithm 2's `·` is pinned to throughout the simulation. -/
def simBlank : Checkpoint (Chain Tx) := ⟨[], 0⟩

/-- The message a reaction sends, if any — the handlers send at most one. -/
noncomputable def sendOf (res : NodeStepResult (NodeState2 Node Tx) M) : Option M :=
  res.send.toList.head?

/-- What `sendOf` returns was sent. -/
theorem sendOf_mem {res : NodeStepResult (NodeState2 Node Tx) M} {m : M}
    (h : sendOf res = some m) : m ∈ res.send := by
  unfold sendOf at h
  refine Multiset.mem_toList.mp ?_
  cases hl : res.send.toList with
  | nil => rw [hl] at h; cases h
  | cons b l' =>
      rw [hl] at h
      simp only [List.head?_cons, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self

/-- An Algorithm-5 tick step, inverted: some admissible pick ran the deterministic
    core. The relational vote choice (tenth finding) makes this an existential where it
    used to be an equation. -/
theorem exec5_tick {x5 : Exec Pr5 S} {k : Nat} {p : Node} {t : Time}
    (h : x5.lbl k = .tick p t) :
    ∃ pk ∈ (components n kappa pool proposer).votePicks Q
        (setClock p t (x5.cfg k))[p].view t (setClock p t (x5.cfg k))[p].st,
      x5.cfg (k + 1) = applyNodeStepResult p
        (handlerCore (components n kappa pool proposer) Q pk p t
          (setClock p t (x5.cfg k))[p].view (setClock p t (x5.cfg k))[p].st)
        (setClock p t (x5.cfg k)) := by
  have hstep := x5.step k
  rw [h] at hstep
  obtain ⟨-, heff⟩ := hstep
  simp only [spec] at heff
  rw [nodeStep_iff_exists] at heff
  obtain ⟨res, hres, hpost⟩ := heff
  rw [protocol_step_tick] at hres
  obtain ⟨pk, hpk, rfl⟩ := mem_handler_iff.mp hres
  refine ⟨pk, ?_, ?_⟩
  · simpa [setClock_getElem] using hpk
  · rw [hpost]
    simp [setClock_getElem]

/-- The pick the original tick at step `k` actually used — by choice from `exec5_tick`;
    a placeholder off the tick labels. -/
noncomputable def pick5 (x5 : Exec Pr5 S) (k : Nat) (p : Node) (t : Time) : Chain Tx :=
  @dite _ (x5.lbl k = .tick p t) (Classical.propDecidable _)
    (fun h => (exec5_tick (x5 := x5) h).choose) (fun _ => [])

theorem pick5_mem {x5 : Exec Pr5 S} {k : Nat} {p : Node} {t : Time}
    (h : x5.lbl k = .tick p t) :
    pick5 x5 k p t ∈ (components n kappa pool proposer).votePicks Q
      (setClock p t (x5.cfg k))[p].view t (setClock p t (x5.cfg k))[p].st := by
  unfold pick5
  rw [dif_pos h]
  exact (exec5_tick h).choose_spec.1

theorem exec5_succ_tick {x5 : Exec Pr5 S} {k : Nat} {p : Node} {t : Time}
    (h : x5.lbl k = .tick p t) :
    x5.cfg (k + 1) = applyNodeStepResult p
      (handlerCore (components n kappa pool proposer) Q (pick5 x5 k p t) p t
        (setClock p t (x5.cfg k))[p].view (setClock p t (x5.cfg k))[p].st)
      (setClock p t (x5.cfg k)) := by
  unfold pick5
  rw [dif_pos h]
  exact (exec5_tick h).choose_spec.2

/-- The simulated tick's pick: the original's, when admissible in the simulated view —
    that it *is* admissible at every honest tick is stage C's content, not the
    construction's — and any admissible pick otherwise, keeping the construction total
    and every step legal. -/
noncomputable def simPick (x5 : Exec Pr5 S) (k : Nat) (p : Node) (t : Time)
    (V2 : View Node M) (s2 : NodeState2 Node Tx) : Chain Tx :=
  @ite _ (pick5 x5 k p t ∈ votePicks2 Q n proposer V2 t s2) (Classical.propDecidable _)
    (pick5 x5 k p t) (votePicks2_nonempty Q n proposer V2 t s2).choose

theorem simPick_mem (x5 : Exec Pr5 S) (k : Nat) (p : Node) (t : Time)
    (V2 : View Node M) (s2 : NodeState2 Node Tx) :
    simPick x5 k p t V2 s2 ∈ votePicks2 Q n proposer V2 t s2 := by
  unfold simPick
  split_ifs with h
  · exact h
  · exact (votePicks2_nonempty Q n proposer V2 t s2).choose_spec

/-- One step of the simulation: the Algorithm-2 configuration, and the correspondence
    table pairing each Algorithm-5 message with the simulated execution's counterpart.
    Every branch is the framework's effect term for the (translated) action, verbatim,
    so `simulate`'s step obligations hold by shape. -/
noncomputable def simStep (x5 : Exec Pr5 S) (k : Nat) :
    Config Node M (NodeState2 Node Tx) × (SignedMsg Node M → SignedMsg Node M) →
    Config Node M (NodeState2 Node Tx) × (SignedMsg Node M → SignedMsg Node M) :=
  fun (c2, τ) =>
    match x5.lbl k with
    | .advance t => ({ c2 with time := t }, τ)
    | .tick p t =>
        let pre2 := setClock p t c2
        let res2 := handler2Core Q n kappa pool proposer simBlank
          (simPick x5 k p t pre2[p].view pre2[p].st) p t
          pre2[p].view pre2[p].st
        let pre5 := setClock p t (x5.cfg k)
        let res5 := handlerCore (components n kappa pool proposer) Q (pick5 x5 k p t) p t
          pre5[p].view pre5[p].st
        (applyNodeStepResult p res2 pre2,
         fun sm =>
           if sm.sender = p ∧ sm.msg ∈ res5.send then
             match sendOf res2 with
             | some m2 => ⟨p, m2⟩
             | none => τ sm
           else τ sm)
    | .deliver p m =>
        let pre2 := receive p (τ m) c2
        (applyNodeStepResult p { state := pre2[p].st, send := 0 } pre2, τ)
    | .wake p =>
        (applyNodeStepResult p
          { state := { c2[p].st with activeAt := activationRound Q c2[p].clock },
            send := 0 } c2, τ)
    | .custom _ ev => ev.elim
    | .adversarial p m => ({ c2 with sent := ⟨p, (τ ⟨p, m⟩).msg⟩ ::ₘ c2.sent }, τ)

/-- The initial Algorithm-2 configuration. -/
noncomputable def simInit : Config Node M (NodeState2 Node Tx) where
  time := 0
  nodes := fun _ =>
    { clock := 0
      st := { chi := [], vFrozen := ∅, chFrozen := [], activeAt := 0 }
      view := ∅ }
  sent := 0

/-- The simulated run: configuration and correspondence table after `k` steps. -/
noncomputable def simState (x5 : Exec Pr5 S) : Nat →
    Config Node M (NodeState2 Node Tx) × (SignedMsg Node M → SignedMsg Node M)
  | 0 => (simInit, id)
  | k + 1 => simStep x5 k (simState x5 k)

/-- The simulated labels: deliveries are translated through the table, everything else
    carries over. -/
noncomputable def simLbl (x5 : Exec Pr5 S) (k : Nat) : Action Node M Empty :=
  match x5.lbl k with
  | .deliver p m => .deliver p ((simState x5 k).2 m)
  | .advance t => .advance t
  | .tick p t => .tick p t
  | .wake p => .wake p
  | .custom p ev => .custom p ev
  | .adversarial p m => .adversarial p (((simState x5 k).2 ⟨p, m⟩).msg)

/-! ### The cheap invariants

Everything the step obligations need: the simulated clock face matches the original —
time, per-validator clocks, `activeAt` — and the table maps the original log into the
simulated one. None of this says anything about *content*; that is stage C. -/

/-- Algorithm 5's every step, resolved: deterministic except at ticks, whose reaction
    is the core at the pick `exec5_tick` extracted. -/
theorem exec5_succ {x5 : Exec Pr5 S} (k : Nat) :
    x5.cfg (k + 1) =
      match x5.lbl k with
      | .advance t => { x5.cfg k with time := t }
      | .tick p t =>
          applyNodeStepResult p
            (handlerCore (components n kappa pool proposer) Q (pick5 x5 k p t) p t
              (setClock p t (x5.cfg k))[p].view (setClock p t (x5.cfg k))[p].st)
            (setClock p t (x5.cfg k))
      | .deliver p m =>
          applyNodeStepResult p { state := (receive p m (x5.cfg k))[p].st, send := 0 }
            (receive p m (x5.cfg k))
      | .wake p =>
          applyNodeStepResult p
            { state := { (x5.cfg k)[p].st with
                activeAt := activationRound Q (x5.cfg k)[p].clock }, send := 0 }
            (x5.cfg k)
      | .custom _ ev => ev.elim
      | .adversarial p m => { x5.cfg k with sent := ⟨p, m⟩ ::ₘ (x5.cfg k).sent } := by
  have hstep := x5.step k
  cases h : x5.lbl k with
  | advance t =>
      rw [h] at hstep
      exact hstep.2
  | tick p t => exact exec5_succ_tick h
  | deliver p m =>
      rw [h] at hstep
      obtain ⟨-, heff⟩ := hstep
      simp only [spec] at heff
      rw [nodeStep_iff_exists] at heff
      obtain ⟨res, hres, hpost⟩ := heff
      rw [protocol_step_recv] at hres
      rw [hpost, hres]
  | wake p =>
      rw [h] at hstep
      obtain ⟨-, heff⟩ := hstep
      simp only [spec] at heff
      rw [nodeStep_iff_exists] at heff
      obtain ⟨res, hres, hpost⟩ := heff
      rw [protocol_step_wake] at hres
      rw [hpost, hres]
  | custom p ev => exact ev.elim
  | adversarial p m =>
      rw [h] at hstep
      exact hstep.2

/-- The simulated real time tracks the original's. -/
theorem sim_time {x5 : Exec Pr5 S} (k : Nat) :
    (simState x5 k).1.time = (x5.cfg k).time := by
  induction k with
  | zero =>
      have h0 := x5.init.1
      simp [simState, simInit, h0]
  | succ k ih =>
      have h5 := exec5_succ (x5 := x5) k
      show (simStep x5 k (simState x5 k)).1.time = _
      rw [h5]
      cases h : x5.lbl k with
      | advance t => simp [simStep, h]
      | tick p t =>
          simp only [simStep, h]
          simp [applyNodeStepResult, setClock, Config.setNode, ih]
      | deliver p m =>
          simp only [simStep, h]
          simp [applyNodeStepResult, receive, Config.setNode, ih]
      | wake p =>
          simp only [simStep, h]
          simp [applyNodeStepResult, Config.setNode, ih]
      | custom p ev => exact ev.elim
      | adversarial p m =>
          simp only [simStep, h]
          simp [ih]

/-- The simulated clocks track the original's, validator by validator. -/
theorem sim_clock {x5 : Exec Pr5 S} (k : Nat) (q : Node) :
    (simState x5 k).1[q].clock = (x5.cfg k)[q].clock := by
  induction k with
  | zero =>
      have h0 := x5.init.2.1 q
      show (simState x5 0).1[q].clock = _
      rw [h0]
      rfl
  | succ k ih =>
      have h5 := exec5_succ (x5 := x5) k
      show (simStep x5 k (simState x5 k)).1[q].clock = _
      rw [h5]
      cases h : x5.lbl k with
      | advance t =>
          simp only [simStep, h]
          exact ih
      | tick p t =>
          simp only [simStep, h]
          by_cases hpq : q = p
          · subst hpq
            simp [applyNodeStepResult_getElem, setClock_getElem]
          · simp [applyNodeStepResult_getElem, setClock_getElem, Ne.symm hpq, ih]
      | deliver p m =>
          simp only [simStep, h]
          by_cases hpq : q = p
          · subst hpq
            simp [applyNodeStepResult_getElem, receive_getElem, ih]
          · simp [applyNodeStepResult_getElem, receive_getElem, Ne.symm hpq, ih]
      | wake p =>
          simp only [simStep, h]
          by_cases hpq : q = p
          · subst hpq
            simp [applyNodeStepResult_getElem, ih]
          · simp [applyNodeStepResult_getElem, Ne.symm hpq, ih]
      | custom p ev => exact ev.elim
      | adversarial p m =>
          simp only [simStep, h]
          exact ih

/-- The simulated joining state tracks the original's: both executions wake and
    activate identically. -/
theorem sim_activeAt {x5 : Exec Pr5 S} (k : Nat) (q : Node) :
    (simState x5 k).1[q].st.activeAt = (x5.cfg k)[q].st.activeAt := by
  induction k with
  | zero =>
      have h0 := x5.init.2.1 q
      show (simState x5 0).1[q].st.activeAt = _
      rw [h0]
      rfl
  | succ k ih =>
      have h5 := exec5_succ (x5 := x5) k
      show (simStep x5 k (simState x5 k)).1[q].st.activeAt = _
      rw [h5]
      cases h : x5.lbl k with
      | advance t =>
          simp only [simStep, h]
          exact ih
      | tick p t =>
          simp only [simStep, h]
          by_cases hpq : q = p
          · subst hpq
            simp [applyNodeStepResult_getElem, setClock_getElem, handler2_activeAt,
              handler_activeAt, ih]
          · simp [applyNodeStepResult_getElem, setClock_getElem, Ne.symm hpq, ih]
      | deliver p m =>
          simp only [simStep, h]
          by_cases hpq : q = p
          · subst hpq
            simp [applyNodeStepResult_getElem, receive_getElem, ih]
          · simp [applyNodeStepResult_getElem, receive_getElem, Ne.symm hpq, ih]
      | wake p =>
          simp only [simStep, h]
          by_cases hpq : q = p
          · subst hpq
            simp [applyNodeStepResult_getElem, ih, sim_clock (x5 := x5) k]
          · simp [applyNodeStepResult_getElem, Ne.symm hpq, ih]
      | custom p ev => exact ev.elim
      | adversarial p m =>
          simp only [simStep, h]
          exact ih

/-- The two handlers send together or not at all: the branch conditions read only the
    phase, the proposer, and `activeAt` — equal across the simulation. -/
theorem sends_align {view5 : View Node M} {st5 : NodeState Node (Chain Tx) (QCert Node Tx)}
    {view2 : View Node M} {st2 : NodeState2 Node Tx} {pk5 pk2 : Chain Tx}
    (p : Node) (t : Time)
    (hact : st2.activeAt = st5.activeAt) :
    ((handlerCore (components n kappa pool proposer) Q pk5 p t view5 st5).send = 0 ∧
      (handler2Core Q n kappa pool proposer simBlank pk2 p t view2 st2).send = 0) ∨
    ((handlerCore (components n kappa pool proposer) Q pk5 p t view5 st5).send ≠ 0 ∧
      (handler2Core Q n kappa pool proposer simBlank pk2 p t view2 st2).send ≠ 0) := by
  simp only [handlerCore, handler2Core, components, apply_ite NodeStepResult.send, hact]
  split_ifs <;>
    first
      | exact Or.inl ⟨rfl, rfl⟩
      | exact Or.inr ⟨by simp, by simp⟩
      | (left; constructor <;> rfl)
      | (right; constructor <;> simp)

/-- The table preserves the signer: a key's image carries the key's own sender. -/
theorem sim_table_sender {x5 : Exec Pr5 S} (k : Nat) (sm : SignedMsg Node M) :
    ((simState x5 k).2 sm).sender = sm.sender := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show ((simStep x5 k (simState x5 k)).2 sm).sender = sm.sender
      cases h : x5.lbl k with
      | advance t => simp only [simStep, h]; exact ih
      | tick p t =>
          simp only [simStep, h]
          by_cases hcond : sm.sender = p ∧ sm.msg ∈
              (handlerCore (components n kappa pool proposer) Q (pick5 x5 k p t) p t
                (setClock p t (x5.cfg k))[p].view (setClock p t (x5.cfg k))[p].st).send
          · rw [if_pos hcond]
            cases hso : sendOf (handler2Core Q n kappa pool proposer simBlank
                (simPick x5 k p t (setClock p t (simState x5 k).1)[p].view
                  (setClock p t (simState x5 k).1)[p].st) p t
                (setClock p t (simState x5 k).1)[p].view
                (setClock p t (simState x5 k).1)[p].st) with
            | none => exact ih
            | some m2 => exact hcond.1.symm
          · rw [if_neg hcond]
            exact ih
      | deliver p m => simp only [simStep, h]; exact ih
      | wake p => simp only [simStep, h]; exact ih
      | custom p ev => exact ev.elim
      | adversarial p m => simp only [simStep, h]; exact ih

/-- The table maps into the simulated log (or is the identity): every entry ever
    written points at a message the simulation has signed. -/
theorem sim_table {x5 : Exec Pr5 S} (k : Nat) (sm : SignedMsg Node M) :
    (simState x5 k).2 sm = sm ∨ (simState x5 k).2 sm ∈ (simState x5 k).1.sent := by
  induction k with
  | zero => exact Or.inl rfl
  | succ k ih =>
      show (simStep x5 k (simState x5 k)).2 sm = sm ∨
        (simStep x5 k (simState x5 k)).2 sm ∈ (simStep x5 k (simState x5 k)).1.sent
      cases h : x5.lbl k with
      | advance t =>
          simp only [simStep, h]
          exact ih
      | tick p t =>
          simp only [simStep, h]
          by_cases hcond : sm.sender = p ∧ sm.msg ∈
              (handlerCore (components n kappa pool proposer) Q (pick5 x5 k p t) p t
                (setClock p t (x5.cfg k))[p].view (setClock p t (x5.cfg k))[p].st).send
          · rw [if_pos hcond]
            cases hso : sendOf (handler2Core Q n kappa pool proposer simBlank
                (simPick x5 k p t (setClock p t (simState x5 k).1)[p].view
                  (setClock p t (simState x5 k).1)[p].st) p t
                (setClock p t (simState x5 k).1)[p].view
                (setClock p t (simState x5 k).1)[p].st) with
            | none =>
                rcases ih with h1 | h1
                · exact Or.inl h1
                · refine Or.inr ?_
                  simp only [applyNodeStepResult_sent, setClock]
                  exact Multiset.mem_add.mpr (Or.inl h1)
            | some m2 =>
                refine Or.inr ?_
                have hm2 : m2 ∈ (handler2Core Q n kappa pool proposer simBlank
                    (simPick x5 k p t (setClock p t (simState x5 k).1)[p].view
                      (setClock p t (simState x5 k).1)[p].st) p t
                    (setClock p t (simState x5 k).1)[p].view
                    (setClock p t (simState x5 k).1)[p].st).send := sendOf_mem hso
                simp only [applyNodeStepResult_sent]
                exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_map.mpr ⟨m2, hm2, rfl⟩))
          · rw [if_neg hcond]
            rcases ih with h1 | h1
            · exact Or.inl h1
            · refine Or.inr ?_
              simp only [applyNodeStepResult_sent, setClock]
              exact Multiset.mem_add.mpr (Or.inl h1)
      | deliver p m =>
          simp only [simStep, h]
          rcases ih with h1 | h1
          · exact Or.inl h1
          · refine Or.inr ?_
            simp only [applyNodeStepResult_sent, receive]
            exact Multiset.mem_add.mpr (Or.inl h1)
      | wake p =>
          simp only [simStep, h]
          rcases ih with h1 | h1
          · exact Or.inl h1
          · refine Or.inr ?_
            simp only [applyNodeStepResult_sent]
            exact Multiset.mem_add.mpr (Or.inl h1)
      | custom p ev => exact ev.elim
      | adversarial p m =>
          simp only [simStep, h]
          rcases ih with h1 | h1
          · exact Or.inl h1
          · exact Or.inr (Multiset.mem_cons_of_mem h1)

/-- The table maps the original log into the simulated one: every message ever signed
    in the Algorithm-5 run has its counterpart signed in the simulation. -/
theorem sim_sent {x5 : Exec Pr5 S} (k : Nat) :
    ∀ sm ∈ (x5.cfg k).sent, (simState x5 k).2 sm ∈ (simState x5 k).1.sent := by
  induction k with
  | zero =>
      have h0 := x5.init.2.2
      rw [h0]
      intro sm hsm
      cases hsm
  | succ k ih =>
      have h5 := exec5_succ (x5 := x5) k
      intro sm hsm
      rw [h5] at hsm
      show (simStep x5 k (simState x5 k)).2 sm ∈ (simStep x5 k (simState x5 k)).1.sent
      cases h : x5.lbl k with
      | advance t =>
          rw [h] at hsm
          simp only [simStep, h]
          exact ih sm hsm
      | tick p t =>
          rw [h] at hsm
          simp only [simStep, h]
          simp only [applyNodeStepResult_sent] at hsm ⊢
          by_cases hcond : sm.sender = p ∧ sm.msg ∈
              (handlerCore (components n kappa pool proposer) Q (pick5 x5 k p t) p t
                (setClock p t (x5.cfg k))[p].view (setClock p t (x5.cfg k))[p].st).send
          · rw [if_pos hcond]
            -- the original handler sent something, so the simulated one did too
            have halign := sends_align (Q := Q) (n := n) (kappa := kappa) (pool := pool)
              (proposer := proposer) (pk5 := pick5 x5 k p t)
              (pk2 := simPick x5 k p t (setClock p t (simState x5 k).1)[p].view
                (setClock p t (simState x5 k).1)[p].st)
              (view5 := (setClock p t (x5.cfg k))[p].view)
              (st5 := (setClock p t (x5.cfg k))[p].st)
              (view2 := (setClock p t (simState x5 k).1)[p].view)
              (st2 := (setClock p t (simState x5 k).1)[p].st) p t
              (by simp only [setClock_getElem, if_pos rfl]
                  exact sim_activeAt (x5 := x5) k p)
            rcases halign with ⟨h50, -⟩ | ⟨-, h2ne⟩
            · rw [h50] at hcond
              cases hcond.2
            · have hne : (handler2Core Q n kappa pool proposer simBlank
                  (simPick x5 k p t (setClock p t (simState x5 k).1)[p].view
                    (setClock p t (simState x5 k).1)[p].st) p t
                  (setClock p t (simState x5 k).1)[p].view
                  (setClock p t (simState x5 k).1)[p].st).send.toList ≠ [] := by
                intro h0
                exact h2ne (by
                  have := congrArg Multiset.ofList h0
                  simpa [Multiset.coe_toList] using this)
              obtain ⟨m2, hm2⟩ := List.exists_mem_of_ne_nil _ hne
              cases hso : sendOf (handler2Core Q n kappa pool proposer simBlank
                  (simPick x5 k p t (setClock p t (simState x5 k).1)[p].view
                    (setClock p t (simState x5 k).1)[p].st) p t
                  (setClock p t (simState x5 k).1)[p].view
                  (setClock p t (simState x5 k).1)[p].st) with
              | none =>
                  exfalso
                  unfold sendOf at hso
                  rcases List.head?_eq_none_iff.mp hso with h0
                  exact hne h0
              | some m2' =>
                  have hm2' : m2' ∈ (handler2Core Q n kappa pool proposer simBlank
                      (simPick x5 k p t (setClock p t (simState x5 k).1)[p].view
                        (setClock p t (simState x5 k).1)[p].st) p t
                      (setClock p t (simState x5 k).1)[p].view
                      (setClock p t (simState x5 k).1)[p].st).send := sendOf_mem hso
                  exact Multiset.mem_add.mpr
                    (Or.inr (Multiset.mem_map.mpr ⟨m2', hm2', rfl⟩))
          · rw [if_neg hcond]
            rcases Multiset.mem_add.mp hsm with hold | hnew
            · -- an old message keeps its old image
              have hs : (setClock p t (x5.cfg k)).sent = (x5.cfg k).sent := rfl
              rw [hs] at hold
              exact Multiset.mem_add.mpr (Or.inl (ih sm hold))
            · -- a fresh message contradicts the failed condition
              exfalso
              obtain ⟨m5, hm5, rfl⟩ := Multiset.mem_map.mp hnew
              exact hcond ⟨rfl, hm5⟩
      | deliver p m =>
          rw [h] at hsm
          simp only [simStep, h]
          simp only [applyNodeStepResult_sent] at hsm ⊢
          rcases Multiset.mem_add.mp hsm with hold | hnew
          · have hs : (receive p m (x5.cfg k)).sent = (x5.cfg k).sent := rfl
            rw [hs] at hold
            exact Multiset.mem_add.mpr (Or.inl (ih sm hold))
          · simp at hnew
      | wake p =>
          rw [h] at hsm
          simp only [simStep, h]
          simp only [applyNodeStepResult_sent] at hsm ⊢
          rcases Multiset.mem_add.mp hsm with hold | hnew
          · exact Multiset.mem_add.mpr (Or.inl (ih sm hold))
          · simp at hnew
      | custom p ev => exact ev.elim
      | adversarial p m =>
          rw [h] at hsm
          simp only [simStep, h]
          rcases Multiset.mem_cons.mp hsm with rfl | hold
          · have hs := sim_table_sender (x5 := x5) k (⟨p, m⟩ : SignedMsg Node M)
            have himg : (⟨p, ((simState x5 k).2 ⟨p, m⟩).msg⟩ : SignedMsg Node M)
                = (simState x5 k).2 ⟨p, m⟩ := by
              cases htau : (simState x5 k).2 ⟨p, m⟩ with
              | mk sd mg =>
                  rw [htau] at hs
                  simp only at hs ⊢
                  rw [hs]
            rw [himg]
            exact Multiset.mem_cons_self _ _
          · exact Multiset.mem_cons_of_mem (ih sm hold)

/-- **The simulated execution** — Lemma 10's constructed Algorithm-2 run: same
    schedule, same labels up to the delivery table, every step valid. The MFC
    equivalence with the original is stage C's slot induction. -/
noncomputable def simulate (x5 : Exec Pr5 S) : Exec Pr2 S where
  cfg k := (simState x5 k).1
  lbl := simLbl x5
  init := ⟨rfl, fun _ => rfl, rfl⟩
  step k := by
    show Step Pr2 S (simLbl x5 k) (simState x5 k).1 (simState x5 (k + 1)).1
    have hstep5 := x5.step k
    cases h : x5.lbl k with
    | advance t =>
        rw [h] at hstep5
        simp only [simLbl, h]
        refine ⟨trivial, ?_⟩
        show (simStep x5 k (simState x5 k)).1 = _
        simp [simStep, h]
    | tick p t =>
        rw [h] at hstep5
        obtain ⟨hen, -⟩ := hstep5
        simp only [simLbl, h]
        refine ⟨?_, ?_⟩
        · show p ∈ S.awake (((simState x5 k).1.time : Int))
          rw [sim_time]
          exact hen
        · show NodeStep Pr2 p .tick (setClock p t (simState x5 k).1)
            (simState x5 (k + 1)).1
          rw [nodeStep_iff_exists]
          refine ⟨handler2Core Q n kappa pool proposer simBlank
            (simPick x5 k p t (setClock p t (simState x5 k).1)[p].view
              (setClock p t (simState x5 k).1)[p].st) p
            (setClock p t (simState x5 k).1)[p].clock
            (setClock p t (simState x5 k).1)[p].view
            (setClock p t (simState x5 k).1)[p].st, ?_, ?_⟩
          · rw [protocol2_step_tick, mem_handler2_iff]
            refine ⟨simBlank, _, ?_, rfl⟩
            simpa [setClock_getElem] using simPick_mem x5 k p t
              (setClock p t (simState x5 k).1)[p].view
              (setClock p t (simState x5 k).1)[p].st
          · show (simStep x5 k (simState x5 k)).1 = _
            simp only [simStep, h]
            simp [setClock_getElem]
    | deliver p m =>
        rw [h] at hstep5
        obtain ⟨hen, -⟩ := hstep5
        simp only [simLbl, h]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · exact sim_sent k m hen.1
        · show p ∈ S.awake (((simState x5 k).1.time : Int))
          rw [sim_time]
          exact hen.2
        · show NodeStep Pr2 p (.recv ((simState x5 k).2 m))
            (receive p ((simState x5 k).2 m) (simState x5 k).1) (simState x5 (k + 1)).1
          rw [nodeStep_iff_exists]
          refine ⟨⟨(receive p ((simState x5 k).2 m) (simState x5 k).1)[p].st, 0⟩,
            ?_, ?_⟩
          · rw [protocol2_step_recv]
          · show (simStep x5 k (simState x5 k)).1 = _
            simp [simStep, h]
    | wake p =>
        rw [h] at hstep5
        obtain ⟨hen, -⟩ := hstep5
        simp only [simLbl, h]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · show p ∈ S.awake (((simState x5 k).1.time : Int))
          rw [sim_time]
          exact hen.1
        · show p ∉ S.awake ((((simState x5 k).1.time : Time) : Int) - 1)
          rw [sim_time]
          exact hen.2
        · show NodeStep Pr2 p .wake (simState x5 k).1 (simState x5 (k + 1)).1
          rw [nodeStep_iff_exists]
          refine ⟨⟨{ (simState x5 k).1[p].st with
              activeAt := activationRound Q (simState x5 k).1[p].clock }, 0⟩, ?_, ?_⟩
          · rw [protocol2_step_wake]
          · show (simStep x5 k (simState x5 k)).1 = _
            simp [simStep, h]
    | custom p ev => exact ev.elim
    | adversarial p m =>
        rw [h] at hstep5
        simp only [simLbl, h]
        refine ⟨?_, ?_⟩
        · show p ∈ S.adv (((simState x5 k).1.time : Int))
          rw [sim_time]
          exact hstep5.1
        · show (simStep x5 k (simState x5 k)).1 = _
          simp [simStep, h]

end Majorum
