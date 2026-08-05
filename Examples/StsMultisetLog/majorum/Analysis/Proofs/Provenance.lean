import Mathlib.Data.Finset.Max
import Examples.StsMultisetLog.majorum.Analysis.Proofs.Mfc

/-!
# The execution layer: provenance, and the activation machinery

Helper theorems about executions of `protocol C Q` — again no paper-numbered lemma, per
the convention described in `Lemmas.lean`. The view-local half of the same material lives
in `Mfc.lean`; this file connects it to what happens in an execution. The spine is **provenance**: everything in the
log entered it at some step (`emitted_of_mem_sent`), each step's contribution is either the
sender's own tick or an adversarial injection (`emitted_step`), and the handler's sends
have a rigid shape (`mem_handler_send`). Composed, an honest vote for slot `s` pins down
its own history: it was sent by its sender's tick at reading `voting(s)`, at real time
`voting(s)`, with the joining gate open (`vote_provenance`) — from which the slot-time
bound (`voting_le_of_vote_mem`) and per-slot uniqueness of honest votes
(`honest_vote_unique`, the one consumer of `OneTickPerReading`) follow.

On top of provenance sits the containment: `activeAt` is trustworthy (`wake_sets_activeAt`
writes the true activation round, `activeAt_lb_step` shows no step lowers it below the
current round's), and `mem_active_of_honest_vote` closes the paper's silent step from
"voted in slot `t`" to membership in `H_{vote(t)}` — either the sender was awake through
the whole window, or its latest transition is inside the window and the wake machinery
(`TimeStepwise`, `Diligent`, `WakePrecedesTick`) makes its stored activation round
trustworthy, which a wake that recent puts *after* `voting(t)`, against the open gate the
vote itself certifies.

Everything here is generic in the `Components`: the handler's send discipline does not
depend on the fork-choice.
-/

set_option autoImplicit false

attribute [local instance] Set.monad

namespace Majorum

open the framework's flat multiset-log flavour

variable {Node Tx QC : Type} [DecidableEq Node] [DecidableEq Tx] [DecidableEq QC]
  {C : Components Node (Chain Tx) QC} {Q : Params} {S : Schedule Node}

local notation "Pr" => protocol C Q

/-! ### Navigation -/

/-- `TimeMonotone`, chained along indices. Generic over the protocol: this and the two
    generic lemmas below serve Algorithm 5's and Algorithm 2's layers alike. -/
theorem time_le_of_le {NS : Type} {Pr' : Protocol Node (Msg (Chain Tx) QC) NS Empty}
    {x : Exec Pr' S} (hmono : TimeMonotone x) {i j : Nat} (hij : i ≤ j) :
    x[i].time ≤ x[j].time := by
  induction j, hij using Nat.le_induction with
  | base => exact le_refl _
  | succ n _ ih => exact le_trans ih (hmono n)

/-! ### Provenance -/

/-- **Views only grow**: no action removes from a view — reactions keep it, deliveries
    insert into it. Protocol-generic; the `Majority` congruences' snapshot discipline
    rests on this. -/
theorem view_mono {NS : Type} {Pr' : Protocol Node (Msg (Chain Tx) QC) NS Empty}
    {x : Exec Pr' S} (k : Nat) (p : Node) :
    x[k][p].view ⊆ x[k + 1][p].view := by
  have hstep : Step Pr' S (x.lbl k) x[k] x[k + 1] := x.step k
  refine hstep.elimR (motive := fun _ c c' => c[p].view ⊆ c'[p].view) ?_ ?_ ?_ ?_ ?_ ?_
  · intro d t _
    exact fun ha => ha
  · intro d d' q t hen hns
    rw [nodeStep_iff_exists] at hns
    obtain ⟨res, -, rfl⟩ := hns
    by_cases hq : q = p
    · subst hq
      simp [applyNodeStepResult_getElem, setClock_getElem]
    · simp [applyNodeStepResult_getElem, setClock_getElem, hq]
  · intro d d' q m hen hns
    rw [nodeStep_iff_exists] at hns
    obtain ⟨res, -, rfl⟩ := hns
    by_cases hq : q = p
    · subst hq
      simp only [applyNodeStepResult_getElem, receive_getElem, if_pos rfl]
      exact Finset.subset_insert _ _
    · simp [applyNodeStepResult_getElem, receive_getElem, hq]
  · intro d d' q hen hns
    rw [nodeStep_iff_exists] at hns
    obtain ⟨res, -, rfl⟩ := hns
    by_cases hq : q = p
    · subst hq
      simp [applyNodeStepResult_getElem]
    · simp [applyNodeStepResult_getElem, hq]
  · intro d d' q ev hen hns
    exact ev.elim
  · intro d q m hen
    exact fun _ ha => ha

/-- Views only grow, across any span. -/
theorem view_mono_le {NS : Type} {Pr' : Protocol Node (Msg (Chain Tx) QC) NS Empty}
    {x : Exec Pr' S} {j k : Nat} (h : j ≤ k) (p : Node) :
    x[j][p].view ⊆ x[k][p].view := by
  induction k with
  | zero =>
      have hj : j = 0 := by omega
      subst hj
      exact Finset.Subset.refl _
  | succ k ih =>
      rcases Nat.eq_or_lt_of_le h with heq | hlt
      · subst heq
        exact Finset.Subset.refl _
      · exact (ih (by omega)).trans (view_mono k p)

/-- Everything in the log entered it at some step: the log is a multiset that starts empty
    and only grows, so a member has a positive count somewhere first. -/
theorem emitted_of_mem_sent {NS : Type} {Pr' : Protocol Node (Msg (Chain Tx) QC) NS Empty}
    {x : Exec Pr' S} {i : Nat}
    {sm : SignedMsg Node (Msg (Chain Tx) QC)} (h : sm ∈ x[i].sent) :
    ∃ k, k < i ∧ sm ∈ x[k + 1].sent - x[k].sent := by
  induction i with
  | zero =>
      obtain ⟨-, -, h0⟩ := x.init
      have h0' : x[0].sent = 0 := h0
      rw [h0'] at h
      simp at h
  | succ n ih =>
      by_cases hn : sm ∈ x[n].sent
      · obtain ⟨k, hk, hem⟩ := ih hn
        exact ⟨k, Nat.lt_succ_of_lt hk, hem⟩
      · refine ⟨n, Nat.lt_succ_self n, ?_⟩
        rw [← Multiset.count_pos, Multiset.count_sub]
        have h1 : 0 < Multiset.count sm x[n + 1].sent := Multiset.count_pos.mpr h
        have h2 : Multiset.count sm x[n].sent = 0 := Multiset.count_eq_zero.mpr hn
        omega

/-! ### The deterministic core, and the inversion through it -/

/-- The deterministic core of `handler`: Algorithm 5's four phase actions with the vote
    phase's proposal choice given — meaningful only under `pick ∈ C.votePicks …`, which
    is how `mem_handler_iff` hands it over (the tenth finding's nondeterminism, resolved
    into a parameter here, exactly as `handler2Core`'s). -/
noncomputable def handlerCore (C : Components Node (Chain Tx) QC) (Q : Params)
    (pick : Chain Tx) (p : Node) (r : Time) (V : View Node (Msg (Chain Tx) QC))
    (s : NodeState Node (Chain Tx) QC) :
    NodeStepResult (NodeState Node (Chain Tx) QC) (Msg (Chain Tx) QC) :=
  let slot : Nat := r / Q.slotLength
  let phase : Nat := r % Q.slotLength
  if phase = 0 then
    if p = C.proposer slot ∧ s.activeAt ≤ r then
      let cq := C.fastConfirm V (slot - 1)
      let chMFC := C.mfc V V cq.1 slot
      let chp := C.extend chMFC slot
      { state := s, send := {.propose chp cq.1 cq.2 (C.gj V) slot} }
    else { state := s, send := 0 }
  else if phase = Q.delta then
    let s' := processProposals C V slot s
    let chMFC := C.mfc s'.vFrozen V s'.chFrozen slot
    let chAva :=
      [s'.chAva, C.kappaPrefix slot chMFC, s'.gjFrozen.ch].foldl
        (fun acc ch => if C.prefixLe ch chMFC then C.maxCh acc ch else acc) s'.chAva
    let chFin := C.commonPrefix chAva (C.gf V).ch
    let target : Checkpoint (Chain Tx) :=
      if s'.gjFrozen.c = slot - 1 then ⟨chAva, slot⟩ else ⟨s'.gjFrozen.ch, slot⟩
    { state := if s.activeAt ≤ r then { s' with chAva := chAva, chFin := chFin } else s',
      send := if s.activeAt ≤ r then {.vote pick s'.gjFrozen target slot} else 0 }
  else if phase = 2 * Q.delta then
    let fastcand := (C.fastConfirm V slot).1
    let chAva := if C.prefixLe fastcand s.chAva then s.chAva else fastcand
    { state := { s with chAva := chAva, chFin := (C.gf V).ch }, send := 0 }
  else if phase = 3 * Q.delta then
    { state := { s with vFrozen := V, chFrozen := (C.fastConfirm V slot).1,
                        gjFrozen := C.gj V },
      send := 0 }
  else
    { state := s, send := 0 }

/-- The vote phase's choice set is never empty. -/
theorem votePicks_nonempty (C : Components Node (Chain Tx) QC) (Q : Params)
    (V : View Node (Msg (Chain Tx) QC)) (r : Time) (s : NodeState Node (Chain Tx) QC) :
    (C.votePicks Q V r s).Nonempty :=
  pickSet_nonempty _ _

/-- Membership in the vote branch's nondeterministic assignment followed by a
    deterministic continuation. -/
theorem mem_pick {γ β : Type} {F : Finset γ} {f : γ → β} {res : β} :
    (res ∈ do { let c ← (↑F : Set γ); pure (f c) }) ↔ ∃ c ∈ F, res = f c := by
  rw [Set.bind_def]
  simp only [Set.pure_def, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop,
    Finset.mem_coe]

/-- Membership in a deterministic branch, phrased with the vacuous choice the
    deterministic core still binds. -/
theorem mem_pure_pick {γ β : Type} {F : Finset γ} (hF : F.Nonempty) {b res : β} :
    (res ∈ (pure b : Set β)) ↔ ∃ c ∈ F, res = b := by
  obtain ⟨c, hc⟩ := hF
  simp only [Set.pure_def, Set.mem_singleton_iff]
  exact ⟨fun h => ⟨c, hc, h⟩, fun ⟨_, _, h⟩ => h⟩

/-- **The inversion lemma**: membership in Algorithm 5's handler is exactly "the
    deterministic core, for some admissible pick". -/
theorem mem_handler_iff {p : Node} {r : Time} {V : View Node (Msg (Chain Tx) QC)}
    {s : NodeState Node (Chain Tx) QC}
    {res : NodeStepResult (NodeState Node (Chain Tx) QC) (Msg (Chain Tx) QC)} :
    res ∈ handler C Q p r V s ↔
      ∃ pick ∈ C.votePicks Q V r s, res = handlerCore C Q pick p r V s := by
  have hpk := votePicks_nonempty C Q V r s
  simp only [handler, handlerCore]
  split_ifs <;>
    first
      | exact mem_pick
      | exact mem_pure_pick hpk

/-! `simp only [protocol]` is the wrong tool for reducing `(protocol C Q).step …`: as a
simp rewrite it also unfolds `protocol C Q` inside the *type arguments* of every term in
the hypothesis, and a later `subst` splices those into the goal, leaving terms that are
defeq to the clean spelling but never again syntactically equal to it. These three
definitional lemmas rewrite exactly the proposition and nothing else. -/

theorem protocol_step_tick {p : Node} {r : Time} {V : View Node (Msg (Chain Tx) QC)}
    {s : NodeState Node (Chain Tx) QC} {res} :
    (protocol C Q).step p r V s .tick res ↔ res ∈ handler C Q p r V s := Iff.rfl

theorem protocol_step_recv {p : Node} {r : Time} {V : View Node (Msg (Chain Tx) QC)}
    {s : NodeState Node (Chain Tx) QC} {m : SignedMsg Node (Msg (Chain Tx) QC)} {res} :
    (protocol C Q).step p r V s (.recv m) res ↔ res = { state := s, send := 0 } := Iff.rfl

theorem protocol_step_wake {p : Node} {r : Time} {V : View Node (Msg (Chain Tx) QC)}
    {s : NodeState Node (Chain Tx) QC} {res} :
    (protocol C Q).step p r V s .wake res ↔
      res = { state := { s with activeAt := activationRound Q r }, send := 0 } := Iff.rfl

/-! ### What the handler can send -/

/-- The handler's sends have a rigid shape: only once active, and only a propose message at
    the propose reading or a vote at the vote reading, each carrying the reading's own
    slot. Every other phase sends nothing. -/
theorem mem_handler_send {pick : Chain Tx} {p : Node} {r : Time}
    {V : View Node (Msg (Chain Tx) QC)}
    {s : NodeState Node (Chain Tx) QC} {m : Msg (Chain Tx) QC}
    (h : m ∈ (handlerCore C Q pick p r V s).send) :
    s.activeAt ≤ r ∧
      ((∃ chp chC qc gj, m = .propose chp chC qc gj (r / Q.slotLength) ∧
          r % Q.slotLength = 0) ∨
        (∃ ch src tgt, m = .vote ch src tgt (r / Q.slotLength) ∧
          r % Q.slotLength = Q.delta)) := by
  simp only [handlerCore, apply_ite NodeStepResult.send] at h
  -- the sends-nothing leaves close on `m ∈ 0`; the two sending leaves survive with
  -- `h : m = …` and their guards in context, retrieved anonymously so the proof does not
  -- depend on how `split_ifs` numbers the leaf tree
  split_ifs at h <;> simp at h <;> subst h <;>
    first
      | exact ⟨‹p = C.proposer (r / Q.slotLength) ∧ s.activeAt ≤ r›.2,
          Or.inl ⟨_, _, _, _, rfl, ‹r % Q.slotLength = 0›⟩⟩
      | exact ⟨‹s.activeAt ≤ r›, Or.inr ⟨_, _, _, rfl, ‹r % Q.slotLength = Q.delta›⟩⟩

/-- The handler sends at most one message per step: every branch is a singleton or empty. -/
theorem handler_send_subsingleton {pick : Chain Tx} {p : Node} {r : Time}
    {V : View Node (Msg (Chain Tx) QC)}
    {s : NodeState Node (Chain Tx) QC} {m m' : Msg (Chain Tx) QC}
    (h : m ∈ (handlerCore C Q pick p r V s).send)
    (h' : m' ∈ (handlerCore C Q pick p r V s).send) :
    m = m' := by
  simp only [handlerCore, apply_ite NodeStepResult.send] at h h'
  split_ifs at h h' <;> simp_all

/-! ### What one step can contribute -/

/-- Each step's contribution to the log is either its sender's own tick — with the message
    among that tick's handler sends — or an adversarial injection while the sender is
    corrupt. The tick disjunct also reports what the surrounding configurations know: the
    sender was awake, time did not move, and its clock came to read the tick's reading. -/
theorem emitted_step {x : Exec Pr S} {k : Nat} {sm : SignedMsg Node (Msg (Chain Tx) QC)}
    (hem : sm ∈ x[k + 1].sent - x[k].sent) :
    (∃ t : Time, x.lbl k = .tick sm.sender t ∧
        sm.sender ∈ S.awake ((x[k].time : Int)) ∧
        x[k + 1].time = x[k].time ∧ x[k + 1][sm.sender].clock = t ∧
        ∃ pick ∈ C.votePicks Q x[k][sm.sender].view t x[k][sm.sender].st,
          sm.msg ∈ (handlerCore C Q pick sm.sender t
            x[k][sm.sender].view x[k][sm.sender].st).send) ∨
      sm.sender ∈ S.adv ((x[k].time : Int)) := by
  have hstep := x.step k
  refine hstep.elimR (motive := fun a c c' => sm ∈ c'.sent - c.sent →
      (∃ t : Time, a = Action.tick sm.sender t ∧
          sm.sender ∈ S.awake ((c.time : Int)) ∧ c'.time = c.time ∧
          c'[sm.sender].clock = t ∧
          ∃ pick ∈ C.votePicks Q c[sm.sender].view t c[sm.sender].st,
            sm.msg ∈ (handlerCore C Q pick sm.sender t
              c[sm.sender].view c[sm.sender].st).send) ∨
        sm.sender ∈ S.adv ((c.time : Int)))
    ?_ ?_ ?_ ?_ ?_ ?_ hem
  · -- advance: the log does not move
    intro d t hem'
    have hz : ({ d with time := t } : Config Node (Msg (Chain Tx) QC)
        (NodeState Node (Chain Tx) QC)).sent - d.sent = 0 := by
      show d.sent - d.sent = 0
      ext a
      simp [Multiset.count_sub]
    rw [hz] at hem'
    simp at hem'
  · -- tick: some admissible reaction of the handler, so the delta is its send
    intro d d' q t hen hns hem'
    rw [nodeStep_iff_exists] at hns
    obtain ⟨res, hstep', rfl⟩ := hns
    rw [protocol_step_tick] at hstep'
    obtain ⟨pk, hpk, rfl⟩ := mem_handler_iff.mp hstep'
    rw [← setClock_sent q t d, applyNodeStepResult_sent_sub] at hem'
    obtain ⟨mm, hmm, hsm⟩ := Multiset.mem_map.mp hem'
    subst hsm
    simp only [spec] at hen
    refine Or.inl ⟨t, rfl, hen, rfl, ?_, pk, ?_, ?_⟩
    · simp [setClock_getElem]
    · simpa [setClock_getElem] using hpk
    · simpa [setClock_getElem] using hmm
  · -- deliver: the recv reaction sends nothing
    intro d d' q m hen hns hem'
    rw [nodeStep_iff_exists] at hns
    obtain ⟨res, hstep', rfl⟩ := hns
    rw [protocol_step_recv] at hstep'
    subst hstep'
    rw [← receive_sent q m d, applyNodeStepResult_sent_sub] at hem'
    simp at hem'
  · -- wake: sets the activation round, sends nothing
    intro d d' q hen hns hem'
    rw [nodeStep_iff_exists] at hns
    obtain ⟨res, hstep', rfl⟩ := hns
    rw [protocol_step_wake] at hstep'
    subst hstep'
    rw [applyNodeStepResult_sent_sub] at hem'
    simp at hem'
  · -- custom: there are no custom events
    intro d d' q ev hen hns
    exact ev.elim
  · -- adversarial: the injection is the delta, and the signer is corrupt
    intro d q m hen hem'
    simp only [spec] at hen
    have hd : (⟨q, m⟩ ::ₘ d.sent) - d.sent = {(⟨q, m⟩ : SignedMsg Node (Msg (Chain Tx) QC))} := by
      rw [← Multiset.singleton_add, Multiset.add_sub_cancel_right]
    rw [show ({ d with sent := ⟨q, m⟩ ::ₘ d.sent } : Config Node (Msg (Chain Tx) QC)
        (NodeState Node (Chain Tx) QC)).sent = ⟨q, m⟩ ::ₘ d.sent from rfl, hd] at hem'
    rw [Multiset.mem_singleton] at hem'
    subst hem'
    exact Or.inr hen

/-! ### Provenance of an honest vote -/

/-- **An honest vote pins down its own history.** A vote for slot `s` in the log, whose
    sender is still honest, was sent by that sender's tick at reading `voting(s)` — at real
    time `voting(s)`, with the joining gate open, and with the message among that one
    tick's handler sends.

    This is where the paper's "vote messages sent by validators in `H_{vote(t)}`" acquires
    a location in the execution: slot determines reading (`vote(s) = 4Δs + Δ` is the only
    reading whose phase is `Δ` and whose slot is `s`), reading determines real time
    (`SynchronizedClocks`), and honesty rules the adversarial injection out
    (`MonotoneCorruption`, since the injection would have had to happen no later). -/
theorem vote_provenance {x : Exec Pr S} (hsync : SynchronizedClocks x)
    (hmc : S.MonotoneCorruption) (hmono : TimeMonotone x) {i : Nat}
    {sm : SignedMsg Node (Msg (Chain Tx) QC)} {e : Chain Tx}
    {src tgt : Checkpoint (Chain Tx)} {s : Nat}
    (hmem : sm ∈ x[i].sent) (hhon : sm.sender ∉ S.adv ((x[i].time : Int)))
    (hmsg : sm.msg = .vote e src tgt s) :
    ∃ k, k < i ∧ x.lbl k = .tick sm.sender (Q.slotLength * s + Q.delta) ∧
      x[k].time = Q.slotLength * s + Q.delta ∧
      x[k][sm.sender].st.activeAt ≤ Q.slotLength * s + Q.delta ∧
      sm ∈ x[k + 1].sent - x[k].sent ∧
      ∃ pick ∈ C.votePicks Q x[k][sm.sender].view (Q.slotLength * s + Q.delta)
        x[k][sm.sender].st,
        sm.msg ∈ (handlerCore C Q pick sm.sender (Q.slotLength * s + Q.delta)
          x[k][sm.sender].view x[k][sm.sender].st).send := by
  obtain ⟨k, hki, hem⟩ := emitted_of_mem_sent hmem
  have hhonk : sm.sender ∉ S.adv ((x[k].time : Int)) := fun hadv =>
    hhon (hmc _ _ (by exact_mod_cast time_le_of_le hmono (Nat.le_of_lt hki)) hadv)
  rcases emitted_step hem with ⟨t, hlbl, hawake, htime, hclock, pk, hpk, hsend⟩ | hadv
  · obtain ⟨hactive, hshape⟩ := mem_handler_send hsend
    -- the vote's slot pins the reading: `t = 4Δs + Δ`
    have ht : t = Q.slotLength * s + Q.delta := by
      rcases hshape with ⟨chp, chC, qc, gj, heq, -⟩ | ⟨ch, src', tgt', heq, hmod⟩
      · rw [hmsg] at heq
        cases heq
      · rw [hmsg] at heq
        injection heq with _ _ _ hs
        rw [hs, ← hmod]
        exact (Nat.div_add_mod t Q.slotLength).symm
    subst ht
    -- the reading pins real time, through the synchronized clock at the next config
    have hawake' : x.Awake (k + 1) sm.sender := by
      show sm.sender ∈ S.awake ((x[k + 1].time : Int))
      rw [htime]
      exact hawake
    have htimek : x[k].time = Q.slotLength * s + Q.delta := by
      have := hsync (k + 1) sm.sender hawake'
      rw [hclock] at this
      omega
    exact ⟨k, hki, hlbl, htimek, hactive, hem, pk, hpk, hsend⟩
  · exact absurd hadv hhonk

/-- An honest vote for slot `s` cannot be in the log before `voting(s)`. -/
theorem voting_le_of_vote_mem {x : Exec Pr S} (hsync : SynchronizedClocks x)
    (hmc : S.MonotoneCorruption) (hmono : TimeMonotone x) {i : Nat}
    {sm : SignedMsg Node (Msg (Chain Tx) QC)} {e : Chain Tx}
    {src tgt : Checkpoint (Chain Tx)} {s : Nat}
    (hmem : sm ∈ x[i].sent) (hhon : sm.sender ∉ S.adv ((x[i].time : Int)))
    (hmsg : sm.msg = .vote e src tgt s) :
    Q.slotLength * s + Q.delta ≤ x[i].time := by
  obtain ⟨k, hki, -, htimek, -, -, -⟩ := vote_provenance hsync hmc hmono hmem hhon hmsg
  rw [← htimek]
  exact time_le_of_le hmono (Nat.le_of_lt hki)

/-- Two messages emitted by one tick are equal: the step's log delta is one reaction's
    send, and every reaction the handler admits sends at most one message — whatever the
    pick. -/
theorem tick_sends_subsingleton5 {x : Exec Pr S} {k : Nat} {p : Node} {t : Time}
    (hlbl : x.lbl k = .tick p t)
    {sm sm' : SignedMsg Node (Msg (Chain Tx) QC)}
    (h : sm ∈ x[k + 1].sent - x[k].sent) (h' : sm' ∈ x[k + 1].sent - x[k].sent) :
    sm = sm' := by
  have hstep : Step Pr S (x.lbl k) x[k] x[k + 1] := x.step k
  rw [hlbl] at hstep
  obtain ⟨-, heff⟩ := hstep
  simp only [spec] at heff
  rw [nodeStep_iff_exists] at heff
  obtain ⟨res, hres, hpost⟩ := heff
  rw [protocol_step_tick] at hres
  obtain ⟨pk, -, rfl⟩ := mem_handler_iff.mp hres
  rw [hpost, ← setClock_sent p t x[k], applyNodeStepResult_sent_sub] at h h'
  obtain ⟨mm, hmm, hsm⟩ := Multiset.mem_map.mp h
  obtain ⟨mm', hmm', hsm'⟩ := Multiset.mem_map.mp h'
  rw [← hsm, ← hsm']
  rw [show mm = mm' from handler_send_subsingleton
    (by simpa [setClock_getElem] using hmm) (by simpa [setClock_getElem] using hmm')]

/-- **One honest validator, one slot, one vote.** Two votes in the log by the same honest
    sender for the same slot are the same message. This is `OneTickPerReading`'s one job:
    both votes come from ticks at the same reading, so from the *same* tick, whose every
    admissible reaction sends at most one message. -/
theorem honest_vote_unique {x : Exec Pr S} (hsync : SynchronizedClocks x)
    (hone : OneTickPerReading x) (hmc : S.MonotoneCorruption) (hmono : TimeMonotone x)
    {i j : Nat} {sm sm' : SignedMsg Node (Msg (Chain Tx) QC)}
    {e e' : Chain Tx} {src tgt src' tgt' : Checkpoint (Chain Tx)} {s : Nat}
    (hm : sm ∈ x[i].sent) (hm' : sm' ∈ x[j].sent)
    (hh : sm.sender ∉ S.adv ((x[i].time : Int)))
    (hh' : sm'.sender ∉ S.adv ((x[j].time : Int)))
    (hs : sm'.sender = sm.sender)
    (hmsg : sm.msg = .vote e src tgt s) (hmsg' : sm'.msg = .vote e' src' tgt' s) :
    sm' = sm := by
  obtain ⟨k, -, hlbl, -, -, hem, -⟩ := vote_provenance hsync hmc hmono hm hh hmsg
  obtain ⟨k', -, hlbl', -, -, hem', -⟩ := vote_provenance hsync hmc hmono hm' hh' hmsg'
  rw [hs] at hlbl'
  have hk : k' = k := hone k' k sm.sender _ hlbl' hlbl
  subst hk
  exact tick_sends_subsingleton5 hlbl hem' hem

/-! ### The activation round is trustworthy

The pieces that turn `activeAt ≤ voting(t)` at the vote tick into schedule-level activity:
nothing but a wake event writes `activeAt`, a wake event writes the activation round of its
own (real-time) round, and the wake event for every transition actually fires
(`TimeStepwise` supplies the round, `Diligent` a tick in it, `WakePrecedesTick` the
ordering). -/

/-- `processProposals` writes only `gjFrozen` and `chFrozen`; the frozen view rides
    through. -/
theorem processProposals_vFrozen (C : Components Node (Chain Tx) QC)
    (V : View Node (Msg (Chain Tx) QC)) (t : Nat) (s : NodeState Node (Chain Tx) QC) :
    (processProposals C V t s).vFrozen = s.vFrozen := by
  unfold processProposals
  generalize V.toList = l
  induction l generalizing s with
  | nil => rfl
  | cons a l ih =>
      rw [List.foldl_cons, ih]
      cases hm : a.msg with
      | vote ch src tgt t' => rfl
      | propose chp chC qc gj t' =>
          dsimp only
          split_ifs <;> rfl

/-- Every branch of the handler keeps the frozen view or freezes the current one. -/
theorem handler_vFrozen (C : Components Node (Chain Tx) QC) (Q : Params)
    (pick : Chain Tx) (p : Node)
    (r : Time) (V : View Node (Msg (Chain Tx) QC)) (s : NodeState Node (Chain Tx) QC) :
    (handlerCore C Q pick p r V s).state.vFrozen = s.vFrozen ∨
      (handlerCore C Q pick p r V s).state.vFrozen = V := by
  simp only [handlerCore, apply_ite NodeStepResult.state]
  split_ifs <;>
    first
      | exact Or.inl rfl
      | exact Or.inl (processProposals_vFrozen C V _ s)
      | exact Or.inr rfl

/-- Ticks do not touch views: the reaction rewrites state and log only. -/
theorem tick_view {NS : Type} {Pr' : Protocol Node (Msg (Chain Tx) QC) NS Empty}
    {x : Exec Pr' S} {k : Nat} {p : Node} {t : Time} (h : x.lbl k = .tick p t)
    (q : Node) : x[k + 1][q].view = x[k][q].view := by
  have hstep : Step Pr' S (x.lbl k) x[k] x[k + 1] := x.step k
  rw [h] at hstep
  obtain ⟨-, heff⟩ := hstep
  simp only [spec] at heff
  rw [nodeStep_iff_exists] at heff
  obtain ⟨res, -, hpost⟩ := heff
  rw [hpost]
  by_cases hq : q = p
  · subst hq
    simp [applyNodeStepResult_getElem, setClock_getElem]
  · simp [applyNodeStepResult_getElem, setClock_getElem, Ne.symm hq]

/-- `processProposals` never writes `activeAt`. -/
theorem processProposals_activeAt (C : Components Node (Chain Tx) QC)
    (V : View Node (Msg (Chain Tx) QC)) (t : Nat) (s : NodeState Node (Chain Tx) QC) :
    (processProposals C V t s).activeAt = s.activeAt := by
  unfold processProposals
  generalize V.toList = l
  induction l generalizing s with
  | nil => rfl
  | cons a l ih =>
      rw [List.foldl_cons, ih]
      cases hm : a.msg with
      | vote ch src tgt t' => rfl
      | propose chp chC qc gj t' =>
          dsimp only
          split_ifs <;> rfl

/-- Neither does any branch of the handler: activation is written by wake events alone. -/
theorem handler_activeAt (pick : Chain Tx) (p : Node) (r : Time)
    (V : View Node (Msg (Chain Tx) QC))
    (s : NodeState Node (Chain Tx) QC) :
    (handlerCore C Q pick p r V s).state.activeAt = s.activeAt := by
  simp only [handlerCore, apply_ite NodeStepResult.state]
  split_ifs <;> simp [processProposals_activeAt]

/-- `activationRound` is monotone in the wake round. -/
theorem activationRound_mono (Q : Params) {r r' : Time} (h : r ≤ r') :
    activationRound Q r ≤ activationRound Q r' := by
  unfold activationRound
  have h1 : (r + 2 * Q.delta + (Q.slotLength - 1)) / Q.slotLength ≤
      (r' + 2 * Q.delta + (Q.slotLength - 1)) / Q.slotLength :=
    Nat.div_le_div_right (by omega)
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ h1) _

/-- A wake round inside slot `t`'s activity window activates only *after* `voting(t)` —
    the arithmetic behind "a validator that woke too recently cannot have the gate open". -/
theorem voting_lt_activationRound (Q : Params) {t n : Time}
    (h : Q.slotLength * t < n + 2 * Q.delta) :
    Q.slotLength * t + Q.delta < activationRound Q n := by
  unfold activationRound
  have hsl : 0 < Q.slotLength := by
    have := Q.deltaPos
    unfold Params.slotLength
    omega
  have hd : Q.delta < Q.slotLength := by
    have := Q.deltaPos
    unfold Params.slotLength
    omega
  have hle : t + 1 ≤ (n + 2 * Q.delta + (Q.slotLength - 1)) / Q.slotLength := by
    rw [Nat.le_div_iff_mul_le hsl, Nat.succ_mul, Nat.mul_comm t Q.slotLength]
    omega
  have := Nat.mul_le_mul_left Q.slotLength hle
  have hexp : Q.slotLength * (t + 1) = Q.slotLength * t + Q.slotLength := Nat.mul_succ ..
  omega

/-- Under `TimeStepwise`, every value below the current time was some configuration's
    time — the intermediate-value property of stepwise sequences. -/
theorem exists_time_eq {NS : Type} {Pr' : Protocol Node (Msg (Chain Tx) QC) NS Empty}
    {x : Exec Pr' S} (hstep : TimeStepwise x) {j : Nat} {w : Time}
    (hw : w ≤ x[j].time) : ∃ i, i ≤ j ∧ x[i].time = w := by
  induction j with
  | zero =>
      have h0 : x[0].time = 0 := x.init.1
      exact ⟨0, le_refl _, by omega⟩
  | succ n ih =>
      rcases hstep n with heq | heq
      · obtain ⟨i, hi, hti⟩ := ih (by omega)
        exact ⟨i, Nat.le_succ_of_le hi, hti⟩
      · by_cases hw' : w ≤ x[n].time
        · obtain ⟨i, hi, hti⟩ := ih hw'
          exact ⟨i, Nat.le_succ_of_le hi, hti⟩
        · exact ⟨n + 1, le_refl _, by omega⟩

/-- Membership in `awakeThroughout`, unfolded to a per-round statement. -/
theorem mem_awakeThroughout [Fintype Node] {p : Node} {a b : Int} :
    p ∈ S.awakeThroughout a b ↔ ∀ r, a ≤ r → r ≤ b → p ∈ S.awake r := by
  unfold Schedule.awakeThroughout
  rw [← Finset.singleton_subset_iff]
  constructor
  · intro h r har hrb
    exact Finset.singleton_subset_iff.mp
      (h.trans (Finset.inf_le (Finset.mem_Icc.mpr ⟨har, hrb⟩)))
  · intro h
    refine Finset.le_inf fun r hr => ?_
    obtain ⟨har, hrb⟩ := Finset.mem_Icc.mp hr
    exact Finset.singleton_subset_iff.mpr (h r har hrb)

/-- A wake event writes the activation round of its own round: the wake handler computes
    it from the clock, and the clock of a (necessarily awake) waking validator reads real
    time. -/
theorem wake_sets_activeAt {x : Exec Pr S} (hsync : SynchronizedClocks x) {k : Nat}
    {p : Node} (hlbl : x.lbl k = .wake p) :
    x[k + 1][p].st.activeAt = activationRound Q x[k].time := by
  have hstep : Step Pr S (x.lbl k) x[k] x[k + 1] := x.step k
  rw [hlbl] at hstep
  obtain ⟨hen, heff⟩ := hstep
  simp only [spec] at hen heff
  have hclock : x[k][p].clock = x[k].time := hsync k p hen.1
  rw [nodeStep_iff_exists] at heff
  obtain ⟨res, hres, hpost⟩ := heff
  rw [protocol_step_wake] at hres
  subst hres
  rw [hpost, applyNodeStepResult_getElem, if_pos rfl]
  dsimp only
  rw [hclock]

/-- One step cannot lower `activeAt` below a bound that also lies below the activation
    round of the current time: every branch of the handler preserves `activeAt`, other
    validators' steps do not touch it, and a wake resets it to the activation round of the
    current round — no earlier.

    The per-configuration clock fact is threaded through the motive rather than taken from
    `SynchronizedClocks` inside the case analysis, because `Step.elimR` keeps the
    configurations abstract. -/
theorem activeAt_lb_step {x : Exec Pr S} (hsync : SynchronizedClocks x) {m : Nat}
    {p : Node} {A : Time} (hA : A ≤ x[m][p].st.activeAt)
    (hAm : A ≤ activationRound Q x[m].time) : A ≤ x[m + 1][p].st.activeAt := by
  have hstep : Step Pr S (x.lbl m) x[m] x[m + 1] := x.step m
  refine hstep.elimR (motive := fun _ c c' =>
      A ≤ c[p].st.activeAt → A ≤ activationRound Q c.time →
      (∀ q : Node, q ∈ S.awake ((c.time : Int)) → c[q].clock = c.time) →
      A ≤ c'[p].st.activeAt)
    ?_ ?_ ?_ ?_ ?_ ?_ hA hAm (fun q hq => hsync m q hq)
  · -- advance: nodes untouched
    intro d t h _ _
    exact h
  · -- tick: the handler never writes `activeAt`
    intro d d' q t hen hns h _ _
    rw [nodeStep_iff_exists] at hns
    obtain ⟨res, hres, rfl⟩ := hns
    rw [protocol_step_tick] at hres
    obtain ⟨pk, -, rfl⟩ := mem_handler_iff.mp hres
    by_cases hq : q = p
    · subst hq
      simpa [applyNodeStepResult_getElem, handler_activeAt, setClock_getElem] using h
    · simpa [applyNodeStepResult_getElem, setClock_getElem, hq] using h
  · -- deliver: the recv reaction returns the state unchanged
    intro d d' q mm hen hns h _ _
    rw [nodeStep_iff_exists] at hns
    obtain ⟨res, hres, rfl⟩ := hns
    rw [protocol_step_recv] at hres
    subst hres
    by_cases hq : q = p
    · subst hq
      simpa [applyNodeStepResult_getElem, receive_getElem] using h
    · simpa [applyNodeStepResult_getElem, receive_getElem, hq] using h
  · -- wake: resets `activeAt` to the activation round of the current round
    intro d d' q hen hns h hm' hclocks
    simp only [spec] at hen
    rw [nodeStep_iff_exists] at hns
    obtain ⟨res, hres, rfl⟩ := hns
    rw [protocol_step_wake] at hres
    subst hres
    by_cases hq : q = p
    · subst hq
      simp only [applyNodeStepResult_getElem, if_pos rfl]
      simpa [hclocks q hen.1] using hm'
    · simpa [applyNodeStepResult_getElem, hq] using h
  · -- custom: there are none
    intro d d' q ev hen hns
    exact ev.elim
  · -- adversarial: nodes untouched
    intro d q mm hen h _ _
    exact h

/-- **An honest voter is active.** A vote for slot `t` in the log, whose sender is still
    honest, puts that sender in `Active(t)` — the paper's silent step from "voted in slot
    `t`" to membership in `H_{vote(t)}`, and the last piece of Lemma 2's containment.

    The dichotomy: either the sender was awake through the whole activity window, which is
    `Active(t)` directly; or it has a latest transition *inside* the window, in which case
    the wake machinery (`TimeStepwise` supplies the round, `Diligent` a tick in it,
    `WakePrecedesTick` the wake before that tick) makes its stored activation round
    trustworthy — and a wake that recent activates only after `voting(t)`, contradicting
    the open gate the vote itself certifies. -/
theorem mem_active_of_honest_vote [Fintype Node] {x : Exec Pr S}
    (hsync : SynchronizedClocks x) (hstepw : TimeStepwise x) (hdil : Diligent x)
    (hwpt : WakePrecedesTick x) (hmc : S.MonotoneCorruption)
    {i : Nat} {sm : SignedMsg Node (Msg (Chain Tx) QC)} {e : Chain Tx}
    {src tgt : Checkpoint (Chain Tx)} {t : Nat} (ht : 1 ≤ t)
    (hmem : sm ∈ x[i].sent) (hhon : sm.sender ∉ S.adv ((x[i].time : Int)))
    (hmsg : sm.msg = .vote e src tgt t) :
    sm.sender ∈ Active Q S (t : Int) := by
  have hmono := hstepw.timeMonotone
  obtain ⟨j, hji, hlbl, htj, hgate, -, -⟩ :=
    vote_provenance hsync hmc hmono hmem hhon hmsg
  -- the voter is awake at `voting(t)`: the tick's own enabling condition
  have hstepj : Step Pr S (x.lbl j) x[j] x[j + 1] := x.step j
  rw [hlbl] at hstepj
  have hawk : sm.sender ∈ S.awake ((x[j].time : Int)) := by
    have := hstepj.1
    simp only [spec] at this
    exact this
  -- `voting(t)` as an integer
  have hvot : Q.voting (t : Int) = ((Q.slotLength * t + Q.delta : Nat) : Int) := by
    unfold Params.voting
    push_cast
    omega
  show sm.sender ∈ S.awakeThroughout (Q.voting (t : Int) - 3 * (Q.delta : Int))
    (Q.voting (t : Int))
  by_cases hbad : ∃ r ∈ Finset.Icc (Q.voting (t : Int) - 3 * (Q.delta : Int))
      (Q.voting (t : Int)), sm.sender ∉ S.awake r
  · -- a round in the window at which the sender was asleep: derive the contradiction
    exfalso
    obtain ⟨r₀, hr₀Icc, hr₀⟩ := hbad
    set bad : Finset Int := (Finset.Icc (Q.voting (t : Int) - 3 * (Q.delta : Int))
        (Q.voting (t : Int))).filter (fun r => sm.sender ∉ S.awake r) with hbaddef
    have hbadne : bad.Nonempty := ⟨r₀, Finset.mem_filter.mpr ⟨hr₀Icc, hr₀⟩⟩
    obtain ⟨hwIcc, hwna⟩ := Finset.mem_filter.mp (Finset.max'_mem bad hbadne)
    obtain ⟨hwlo, hwhi⟩ := Finset.mem_Icc.mp hwIcc
    -- the sender is awake at the top of the window, so the bad round is strictly below
    have hawktop : sm.sender ∈ S.awake (Q.voting (t : Int)) := by
      rw [hvot]
      rw [htj] at hawk
      exact_mod_cast hawk
    have hwlt : bad.max' hbadne < Q.voting (t : Int) :=
      lt_of_le_of_ne hwhi (fun h => hwna (by rw [h]; exact hawktop))
    -- awake everywhere strictly above the bad round, within the window
    have hawakeW : ∀ r : Int, bad.max' hbadne < r → r ≤ Q.voting (t : Int) →
        sm.sender ∈ S.awake r := by
      intro r hr1 hr2
      by_contra hna
      have hmem' : r ∈ bad :=
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hr2⟩, hna⟩
      have := Finset.le_max' bad r hmem'
      omega
    -- the transition round `wmax + 1`, as a natural number
    have hlopos : (0 : Int) < Q.voting (t : Int) - 3 * (Q.delta : Int) := by
      have hδ := Q.deltaPos
      have h4 : Q.slotLength ≤ Q.slotLength * t := by
        simpa using Nat.mul_le_mul_left Q.slotLength ht
      have hsl : Q.slotLength = 4 * Q.delta := rfl
      rw [hvot]
      push_cast
      omega
    obtain ⟨n, hn⟩ : ∃ n : Nat, (n : Int) = bad.max' hbadne + 1 :=
      ⟨(bad.max' hbadne + 1).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hnvt : n ≤ Q.slotLength * t + Q.delta := by
      have h2 : (n : Int) ≤ ((Q.slotLength * t + Q.delta : Nat) : Int) := by
        rw [hn, ← hvot]
        omega
      exact_mod_cast h2
    -- a wake event of the sender at time `n`, strictly before the vote tick
    have hwake : ∃ k, k < j ∧ x.lbl k = .wake sm.sender ∧ x[k].time = n := by
      rcases Nat.lt_or_ge n (Q.slotLength * t + Q.delta) with hnlt | hnge
      · -- the transition is strictly below the vote round: Diligent ticks it there
        obtain ⟨i₀, hi₀j, hti₀⟩ := exists_time_eq hstepw
          (show n ≤ x[j].time by rw [htj]; omega)
        have hAw : x.Awake i₀ sm.sender := by
          show sm.sender ∈ S.awake ((x[i₀].time : Int))
          rw [hti₀, hn]
          exact hawakeW _ (by omega) (by omega)
        obtain ⟨i₁, hti₁, hlbl₁⟩ := hdil n sm.sender ⟨i₀, hti₀, hAw⟩
        have hnaw : sm.sender ∉ S.awake ((x[i₁].time : Int) - 1) := by
          rw [hti₁, hn]
          simpa using hwna
        obtain ⟨k, hki₁, hwk, htk'⟩ := hwpt i₁ sm.sender n hlbl₁ hnaw
        have hij : i₁ < j := by
          rcases Nat.lt_or_ge i₁ j with h | h
          · exact h
          · exfalso
            rcases Nat.eq_or_lt_of_le h with heq | h'
            · rw [← heq] at hlbl₁
              rw [hlbl₁] at hlbl
              injection hlbl with _ hnv
              omega
            · have := time_le_of_le hmono (Nat.le_of_lt h')
              rw [htj, hti₁] at this
              omega
        exact ⟨k, lt_trans hki₁ hij, hwk, by rw [htk', hti₁]⟩
      · -- the transition round is the vote round itself: the vote tick is in it
        have hneq : n = Q.slotLength * t + Q.delta := by omega
        have hnaw : sm.sender ∉ S.awake ((x[j].time : Int) - 1) := by
          rw [htj]
          have hδ : ((Q.slotLength * t + Q.delta : Nat) : Int) - 1 = bad.max' hbadne := by
            rw [← hvot]
            omega
          rw [hδ]
          exact hwna
        obtain ⟨k, hkj, hwk, htk'⟩ := hwpt j sm.sender _ hlbl hnaw
        refine ⟨k, hkj, hwk, ?_⟩
        rw [htk', htj]
        omega
    obtain ⟨k, hkj, hwk, htk⟩ := hwake
    -- the wake wrote the true activation round, and nothing lowered it since
    have hbase : x[k + 1][sm.sender].st.activeAt = activationRound Q n := by
      have h := wake_sets_activeAt hsync hwk
      rw [htk] at h
      exact h
    have hpers : ∀ m, k + 1 ≤ m → m ≤ j →
        activationRound Q n ≤ x[m][sm.sender].st.activeAt := by
      intro m
      induction m with
      | zero => omega
      | succ m ih =>
          intro h1 h2
          rcases Nat.eq_or_lt_of_le h1 with heq | hlt
          · have hkm : k = m := by omega
            subst hkm
            exact le_of_eq hbase.symm
          · refine activeAt_lb_step hsync (ih (by omega) (by omega)) ?_
            exact activationRound_mono Q (htk ▸ time_le_of_le hmono (by omega : k ≤ m))
    have hAj := hpers j (by omega) (le_refl j)
    -- a wake this recent activates only after `voting(t)` — against the open gate
    have harith : Q.slotLength * t < n + 2 * Q.delta := by
      have h2 : ((Q.slotLength * t : Nat) : Int) < (n : Int) + 2 * (Q.delta : Int) := by
        rw [hvot] at hwlo
        push_cast at hwlo ⊢
        omega
      exact_mod_cast h2
    have hfin := voting_lt_activationRound Q harith
    omega
  · -- no such round: awake throughout the window is `Active` directly
    refine mem_awakeThroughout.mpr fun r h1 h2 => ?_
    by_contra hna
    exact hbad ⟨r, Finset.mem_Icc.mpr ⟨h1, h2⟩, hna⟩

/-! ### The propose-round half of Lemma 2 -/

/-- Inverting `votes`: a member of the vote filter really is a vote. -/
theorem exists_vote_of_mem_votes {V : View Node (Msg (Chain Tx) QC)}
    {sm : SignedMsg Node (Msg (Chain Tx) QC)} (h : sm ∈ votes V) :
    ∃ e src tgt s, sm.msg = Msg.vote e src tgt s := by
  simp only [votes, Finset.mem_filter] at h
  obtain ⟨-, hv⟩ := h
  cases hm : sm.msg with
  | propose chp chC qc gj t' =>
      rw [hm] at hv
      exact absurd hv (by simp)
  | vote e src tgt s => exact ⟨e, src, tgt, s, rfl⟩

section Lemma2Propose

variable [Fintype Node]

/-- **Lemma 2's hypothesis, over the log**: every validator active in slot `t` has, by the
    end of `voting(t)`, sent a slot-`t` vote for a chain extending `ch`. The paper says
    "all validators in `H_{vote(t)}` send vote messages for chains extending `ch`"; with
    `honest_vote_unique` the one exhibited vote is the only one, so "a vote extends" and
    "all their votes extend" coincide for the honest. -/
def ActiveVotesExtend (x : Exec Pr S) (t : Nat) (ch : Chain Tx) : Prop :=
  ∀ p ∈ Active Q S (t : Int), ∃ (i : Nat) (e : Chain Tx) (src tgt : Checkpoint (Chain Tx)),
    x[i].time = Q.slotLength * t + Q.delta ∧
    ⟪vote, e, src, tgt, t, p⟫ ∈ x[i].sent ∧
    chainLe ch e

/-- **The propose-round half of Lemma 2**: if every validator active in slot `t` voted for
    an extension of `ch`, then at `propose(t+1)` the fork-choice of any validator active in
    slot `t+1` returns an extension of `ch`, over any base `b ⪯ ch`.

    The paper's Case 1, assembled: `Synchrony` delivers the slot-`t` votes into the view;
    provenance and one-vote-per-slot push each honest vote through the three filters; every
    voter the view shows is corrupt at `voting(t+1)` or, by `mem_active_of_honest_vote`,
    active in slot `t` — the containment; and Constraint (1) at slot `t+1` turns the
    containment into `MFC`'s majority. -/
theorem le_mfc_at_propose {x : Exec Pr S}
    (hsync : SynchronizedClocks x) (hstepw : TimeStepwise x) (hdil : Diligent x)
    (hwpt : WakePrecedesTick x) (hone : OneTickPerReading x) (hmc : S.MonotoneCorruption)
    (hsyn : Synchrony 0 Q.delta x) (hslp : Sleepiness Q S) (hgst : Q.gst = 0)
    {t : Nat} (ht : 1 ≤ t) {ch : Chain Tx} (hvotes : ActiveVotesExtend x t ch)
    {ip : Nat} (hip : x[ip].time = Q.slotLength * (t + 1))
    {v : Node} (hv : v ∈ Active Q S ((t : Int) + 1))
    {b : Chain Tx} (hb : chainLe b ch) :
    chainLe ch (mfc (x[ip][v].view) (x[ip][v].view) b (t + 1)) := by
  have hmono := hstepw.timeMonotone
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  have hexp : Q.slotLength * (t + 1) = Q.slotLength * t + Q.slotLength := Nat.mul_succ ..
  have hvot1 : Q.voting ((t : Int) + 1) = ((Q.slotLength * (t + 1) + Q.delta : Nat) : Int) := by
    unfold Params.voting
    push_cast
    omega
  -- `v` is awake at `propose(t+1)`: it sits inside slot `t+1`'s activity window
  have hvAw : x.Awake ip v := by
    show v ∈ S.awake ((x[ip].time : Int))
    rw [hip]
    refine mem_awakeThroughout.mp hv _ ?_ ?_ <;> rw [hvot1] <;> push_cast <;> omega
  -- each still-honest active of slot `t` pushes its vote through the filters at `t+1`
  have hmemFor : ∀ p ∈ Active Q S (t : Int) \ S.adv (Q.voting ((t : Int) + 1)),
      ∃ smp ∈ votesFor (x[ip][v].view) ch (t + 1), smp.sender = p := by
    intro p hp
    obtain ⟨hpA, hpH⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨iv, e, src, tgt, htiv, hsent, hext⟩ := hvotes p hpA
    have hhon : ∀ r : Time, r ≤ Q.slotLength * (t + 1) + Q.delta →
        p ∉ S.adv ((r : Int)) := by
      intro r hr had
      refine hpH (hmc _ _ ?_ had)
      rw [hvot1]
      exact_mod_cast hr
    -- delivery: sent at `voting(t)`, in the view by `propose(t+1)`
    have hview : ⟪vote, e, src, tgt, t, p⟫
        ∈ x[ip][v].view := by
      refine hsyn iv ip v _ hsent ?_ hvAw
      rw [htiv, hip]
      omega
    have hsent_ip : ⟪vote, e, src, tgt, t, p⟫
        ∈ x[ip].sent := views_sound x ip v _ hview
    have hhon_ip : p ∉ S.adv ((x[ip].time : Int)) := by
      rw [hip]
      exact hhon _ (by omega)
    refine ⟨⟨p, Msg.vote e src tgt t⟩, ?_, rfl⟩
    -- build the filter membership inside out
    have hvv : ⟪vote, e, src, tgt, t, p⟫
        ∈ votes (x[ip][v].view) := by
      simp only [votes, Finset.mem_filter]
      exact ⟨hview, trivial⟩
    have hfeq : ⟪vote, e, src, tgt, t, p⟫
        ∈ filEq (x[ip][v].view) := by
      simp only [filEq, Finset.mem_filter]
      refine ⟨hvv, ?_⟩
      rintro ⟨sm', hsm', hsend', hslot', hne⟩
      have hsm'log : sm' ∈ x[ip].sent :=
        views_sound x ip v _ (by simp only [votes, Finset.mem_filter] at hsm'; exact hsm'.1)
      obtain ⟨e', src', tgt', s', hm'⟩ := exists_vote_of_mem_votes hsm'
      have e2 : msgSlot sm'.msg = s' := by rw [hm']; exact rfl
      rw [e2] at hslot'
      -- the two spellings of "our vote's slot" are definitionally `t`
      have hs' : s' = t := hslot'
      subst hs'
      have hh' : sm'.sender ∉ S.adv ((x[ip].time : Int)) := by
        rw [hsend']
        exact hhon_ip
      have heq := honest_vote_unique hsync hone hmc hmono hsent_ip hsm'log hhon_ip hh'
        hsend' rfl hm'
      exact hne (by rw [heq])
    have hfexp : ⟪vote, e, src, tgt, t, p⟫
        ∈ fil1Exp (filEq (x[ip][v].view)) (t + 1) := by
      simp only [fil1Exp, Finset.mem_filter]
      exact ⟨hfeq, rfl⟩
    have hflmd : ⟪vote, e, src, tgt, t, p⟫
        ∈ filLmd (fil1Exp (filEq (x[ip][v].view)) (t + 1)) := by
      simp only [filLmd, Finset.mem_filter]
      refine ⟨hfexp, ?_⟩
      rintro ⟨sm', hsm', hsend', hlt⟩
      -- the equality filter pins `sm'`'s slot to `t`, against the strict inequality
      have hexp' : t + 1 = msgSlot sm'.msg + 1 := (Finset.mem_filter.mp hsm').2
      have hlt' : t < msgSlot sm'.msg := hlt
      omega
    simp only [votesFor, Finset.mem_filter]
    exact ⟨hflmd, hext⟩
  -- `Active(t) \ A` injects into the supporters' senders
  have himg : Active Q S (t : Int) \ S.adv (Q.voting ((t : Int) + 1)) ⊆
      (votesFor (x[ip][v].view) ch (t + 1) ∩ votesFor (x[ip][v].view) ch (t + 1)).image
        SignedMsg.sender := by
    intro p hp
    obtain ⟨smp, hsmp, hsend⟩ := hmemFor p hp
    exact Finset.mem_image.mpr ⟨smp, Finset.mem_inter.mpr ⟨hsmp, hsmp⟩, hsend⟩
  -- the containment: every voter the view shows is active-or-corrupt
  have hsub : voters (x[ip][v].view) (t + 1) ⊆
      (Active Q S (t : Int) \ S.adv (Q.voting ((t : Int) + 1))) ∪
        S.adv (Q.voting ((t : Int) + 1)) := by
    intro q hq
    simp only [voters, Finset.mem_image] at hq
    obtain ⟨smq, hsmq, rfl⟩ := hq
    simp only [fil1Exp, Finset.mem_filter] at hsmq
    obtain ⟨hsmqv, hexp'⟩ := hsmq
    by_cases hqa : smq.sender ∈ S.adv (Q.voting ((t : Int) + 1))
    · exact Finset.mem_union_right _ hqa
    refine Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨?_, hqa⟩)
    have hqlog : smq ∈ x[ip].sent :=
      views_sound x ip v _ (by simp only [votes, Finset.mem_filter] at hsmqv; exact hsmqv.1)
    obtain ⟨e', src', tgt', s', hm'⟩ := exists_vote_of_mem_votes hsmqv
    have hh' : smq.sender ∉ S.adv ((x[ip].time : Int)) := by
      rw [hip]
      intro had
      refine hqa (hmc _ _ ?_ had)
      rw [hvot1]
      exact_mod_cast (by omega : Q.slotLength * (t + 1) ≤ Q.slotLength * (t + 1) + Q.delta)
    have e2 : msgSlot smq.msg = s' := by rw [hm']; exact rfl
    rw [e2] at hexp'
    have hs' : s' = t := by omega
    subst hs'
    exact mem_active_of_honest_vote hsync hstepw hdil hwpt hmc ht hqlog hh' hm'
  -- Constraint (1) at slot `t + 1` turns the containment into the majority
  have hgstok : (Q.gst : Int) ≤ Q.proposing ((t : Int) + 1) := by
    rw [hgst]
    unfold Params.proposing
    push_cast
    exact mul_nonneg (Int.natCast_nonneg _) (by omega)
  have hc1 : (S.adv (Q.voting ((t : Int) + 1))).card <
      (Active Q S (t : Int) \ S.adv (Q.voting ((t : Int) + 1))).card := by
    have h := hslp ((t : Int) + 1) hgstok
    simpa using h
  have hvoters := voters_lt_two_mul_honest hsub hc1
  have himgcard := Finset.card_le_card himg
  have hmaj : Majority (x[ip][v].view) (x[ip][v].view) (t + 1) ch := by
    show (voters (x[ip][v].view) (t + 1)).card < 2 * _
    omega
  exact le_mfc_of_majority _ _ b (t + 1) ch hb hmaj

end Lemma2Propose

end Majorum