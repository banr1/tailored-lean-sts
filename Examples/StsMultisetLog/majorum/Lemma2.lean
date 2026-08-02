import Examples.StsMultisetLog.majorum.Lemmas

/-!
# Lemma 2, the execution layer

The view-local half of Lemma 2 lives in `Lemmas.lean`; this file connects it to what
happens in an execution of `protocol C Q`. The spine is **provenance**: everything in the
log entered it at some step (`emitted_of_mem_sent`), each step's contribution is either the
sender's own tick or an adversarial injection (`emitted_step`), and the handler's sends
have a rigid shape (`mem_handler_send`). Composed, an honest vote for slot `s` pins down
its own history: it was sent by its sender's tick at reading `voting(s)`, at real time
`voting(s)`, with the joining gate open (`vote_provenance`) — from which the slot-time
bound (`voting_le_of_vote_mem`) and per-slot uniqueness of honest votes
(`honest_vote_unique`, the one consumer of `OneTickPerReading`) follow.

Everything here is generic in the `Components`: the handler's send discipline does not
depend on the fork-choice.
-/

set_option autoImplicit false

namespace Majorum

open the framework's flat multiset-log flavour

variable {Node Tx QC : Type} [DecidableEq Node] [DecidableEq Tx] [DecidableEq QC]
  {C : Components Node (Chain Tx) QC} {Q : Params} {S : Schedule Node}

local notation "Pr" => protocol C Q

/-! ### Navigation -/

/-- `TimeMonotone`, chained along indices. -/
theorem time_le_of_le {x : Exec Pr S} (hmono : TimeMonotone x) {i j : Nat} (hij : i ≤ j) :
    x[i].time ≤ x[j].time := by
  induction j, hij using Nat.le_induction with
  | base => exact le_refl _
  | succ n _ ih => exact le_trans ih (hmono n)

/-! ### Provenance -/

/-- Everything in the log entered it at some step: the log is a multiset that starts empty
    and only grows, so a member has a positive count somewhere first. -/
theorem emitted_of_mem_sent {x : Exec Pr S} {i : Nat}
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

/-! ### What the handler can send -/

/-- The handler's sends have a rigid shape: only once active, and only a propose message at
    the propose reading or a vote at the vote reading, each carrying the reading's own
    slot. Every other phase sends nothing. -/
theorem mem_handler_send {p : Node} {r : Time} {V : View Node (Msg (Chain Tx) QC)}
    {s : NodeState Node (Chain Tx) QC} {m : Msg (Chain Tx) QC}
    (h : m ∈ (handler C Q p r V s).send) :
    s.activeAt ≤ r ∧
      ((∃ chp chC qc gj, m = .propose chp chC qc gj (r / Q.slotLength) ∧
          r % Q.slotLength = 0) ∨
        (∃ ch src tgt, m = .vote ch src tgt (r / Q.slotLength) ∧
          r % Q.slotLength = Q.delta)) := by
  simp only [handler, apply_ite NodeStepResult.send] at h
  -- the sends-nothing leaves close on `m ∈ 0`; the two sending leaves survive with
  -- `h : m = …` and their guards in context, retrieved anonymously so the proof does not
  -- depend on how `split_ifs` numbers the leaf tree
  split_ifs at h <;> simp at h <;> subst h <;>
    first
      | exact ⟨‹p = C.proposer (r / Q.slotLength) ∧ s.activeAt ≤ r›.2,
          Or.inl ⟨_, _, _, _, rfl, ‹r % Q.slotLength = 0›⟩⟩
      | exact ⟨‹s.activeAt ≤ r›, Or.inr ⟨_, _, _, rfl, ‹r % Q.slotLength = Q.delta›⟩⟩

/-- The handler sends at most one message per step: every branch is a singleton or empty. -/
theorem handler_send_subsingleton {p : Node} {r : Time} {V : View Node (Msg (Chain Tx) QC)}
    {s : NodeState Node (Chain Tx) QC} {m m' : Msg (Chain Tx) QC}
    (h : m ∈ (handler C Q p r V s).send) (h' : m' ∈ (handler C Q p r V s).send) :
    m = m' := by
  simp only [handler, apply_ite NodeStepResult.send] at h h'
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
        sm.msg ∈ (handler C Q sm.sender t x[k][sm.sender].view x[k][sm.sender].st).send) ∨
      sm.sender ∈ S.adv ((x[k].time : Int)) := by
  have hstep := x.step k
  refine hstep.elimR (motive := fun a c c' => sm ∈ c'.sent - c.sent →
      (∃ t : Time, a = Action.tick sm.sender t ∧
          sm.sender ∈ S.awake ((c.time : Int)) ∧ c'.time = c.time ∧
          c'[sm.sender].clock = t ∧
          sm.msg ∈ (handler C Q sm.sender t c[sm.sender].view c[sm.sender].st).send) ∨
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
  · -- tick: the graph of the handler, so the delta is the handler's send
    intro d d' q t hen hns hem'
    rw [nodeStep_iff_exists] at hns
    obtain ⟨res, hstep', rfl⟩ := hns
    simp only [protocol] at hstep'
    subst hstep'
    rw [← setClock_sent q t d, applyNodeStepResult_sent_sub] at hem'
    obtain ⟨mm, hmm, hsm⟩ := Multiset.mem_map.mp hem'
    subst hsm
    simp only [spec] at hen
    refine Or.inl ⟨t, rfl, hen, rfl, ?_, ?_⟩
    · simp [setClock_getElem]
    · simpa [setClock_getElem] using hmm
  · -- deliver: the recv reaction sends nothing
    intro d d' q m hen hns hem'
    rw [nodeStep_iff_exists] at hns
    obtain ⟨res, hstep', rfl⟩ := hns
    simp only [protocol] at hstep'
    subst hstep'
    rw [← receive_sent q m d, applyNodeStepResult_sent_sub] at hem'
    simp at hem'
  · -- wake: sets the activation round, sends nothing
    intro d d' q hen hns hem'
    rw [nodeStep_iff_exists] at hns
    obtain ⟨res, hstep', rfl⟩ := hns
    simp only [protocol] at hstep'
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
      sm.msg ∈ (handler C Q sm.sender (Q.slotLength * s + Q.delta)
        x[k][sm.sender].view x[k][sm.sender].st).send := by
  obtain ⟨k, hki, hem⟩ := emitted_of_mem_sent hmem
  have hhonk : sm.sender ∉ S.adv ((x[k].time : Int)) := fun hadv =>
    hhon (hmc _ _ (by exact_mod_cast time_le_of_le hmono (Nat.le_of_lt hki)) hadv)
  rcases emitted_step hem with ⟨t, hlbl, hawake, htime, hclock, hsend⟩ | hadv
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
    exact ⟨k, hki, hlbl, htimek, hactive, hsend⟩
  · exact absurd hadv hhonk

/-- An honest vote for slot `s` cannot be in the log before `voting(s)`. -/
theorem voting_le_of_vote_mem {x : Exec Pr S} (hsync : SynchronizedClocks x)
    (hmc : S.MonotoneCorruption) (hmono : TimeMonotone x) {i : Nat}
    {sm : SignedMsg Node (Msg (Chain Tx) QC)} {e : Chain Tx}
    {src tgt : Checkpoint (Chain Tx)} {s : Nat}
    (hmem : sm ∈ x[i].sent) (hhon : sm.sender ∉ S.adv ((x[i].time : Int)))
    (hmsg : sm.msg = .vote e src tgt s) :
    Q.slotLength * s + Q.delta ≤ x[i].time := by
  obtain ⟨k, hki, -, htimek, -, -⟩ := vote_provenance hsync hmc hmono hmem hhon hmsg
  rw [← htimek]
  exact time_le_of_le hmono (Nat.le_of_lt hki)

/-- **One honest validator, one slot, one vote.** Two votes in the log by the same honest
    sender for the same slot are the same message. This is `OneTickPerReading`'s one job:
    both votes come from ticks at the same reading, so from the *same* tick, whose handler
    sends at most one message. -/
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
  obtain ⟨k, -, hlbl, -, -, hsend⟩ := vote_provenance hsync hmc hmono hm hh hmsg
  obtain ⟨k', -, hlbl', -, -, hsend'⟩ := vote_provenance hsync hmc hmono hm' hh' hmsg'
  rw [hs] at hlbl'
  have hk : k' = k := hone k' k sm.sender _ hlbl' hlbl
  subst hk
  rw [hs] at hsend'
  have hmm : sm.msg = sm'.msg := handler_send_subsingleton hsend hsend'
  cases sm
  cases sm'
  simp_all

/-! ### The activation round is trustworthy

The pieces that turn `activeAt ≤ voting(t)` at the vote tick into schedule-level activity:
nothing but a wake event writes `activeAt`, a wake event writes the activation round of its
own (real-time) round, and the wake event for every transition actually fires
(`TimeStepwise` supplies the round, `Diligent` a tick in it, `WakePrecedesTick` the
ordering). -/

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
theorem handler_activeAt (p : Node) (r : Time) (V : View Node (Msg (Chain Tx) QC))
    (s : NodeState Node (Chain Tx) QC) :
    (handler C Q p r V s).state.activeAt = s.activeAt := by
  simp only [handler, apply_ite NodeStepResult.state]
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
theorem exists_time_eq {x : Exec Pr S} (hstep : TimeStepwise x) {j : Nat} {w : Time}
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

/-! `simp only [protocol]` is the wrong tool for reducing `(protocol C Q).step …`: as a
simp rewrite it also unfolds `protocol C Q` inside the *type arguments* of every term in
the hypothesis, and a later `subst` splices those into the goal, leaving terms that are
defeq to the clean spelling but never again syntactically equal to it. These three
definitional lemmas rewrite exactly the proposition and nothing else. -/

theorem protocol_step_tick {p : Node} {r : Time} {V : View Node (Msg (Chain Tx) QC)}
    {s : NodeState Node (Chain Tx) QC} {res} :
    (protocol C Q).step p r V s .tick res ↔ res = handler C Q p r V s := Iff.rfl

theorem protocol_step_recv {p : Node} {r : Time} {V : View Node (Msg (Chain Tx) QC)}
    {s : NodeState Node (Chain Tx) QC} {m : SignedMsg Node (Msg (Chain Tx) QC)} {res} :
    (protocol C Q).step p r V s (.recv m) res ↔ res = { state := s, send := 0 } := Iff.rfl

theorem protocol_step_wake {p : Node} {r : Time} {V : View Node (Msg (Chain Tx) QC)}
    {s : NodeState Node (Chain Tx) QC} {res} :
    (protocol C Q).step p r V s .wake res ↔
      res = { state := { s with activeAt := activationRound Q r }, send := 0 } := Iff.rfl

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
    subst hres
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

end Majorum