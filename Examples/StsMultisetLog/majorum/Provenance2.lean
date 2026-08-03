import Examples.StsMultisetLog.majorum.Provenance
import Examples.StsMultisetLog.majorum.Algorithm2

/-!
# The execution layer for Algorithm 2

The same provenance spine as `Provenance.lean`, re-instantiated against `handler2` — the
subject of the paper's Lemma 2 (the course correction of 2026-08-03). The generic pieces
(`time_le_of_le`, `emitted_of_mem_sent`, `exists_time_eq`, the `activationRound`
arithmetic, `mem_awakeThroughout`, `exists_vote_of_mem_votes`) are imported from
`Provenance.lean`; everything handler-shaped is proved afresh here, by the same scripts
against a simpler handler.
-/

set_option autoImplicit false

/- Algorithm 2 pins the certificate type to `QCert Node Tx` (its validity check inspects
   the certificate), so `DecidableEq (SignedMsg Node (Msg (Chain Tx) (QCert Node Tx)))`
   is a fully concrete derivation of term size 212 — over `synthInstance.maxSize`'s
   default 128, where Algorithm 5's layer kept `QC` atomic and small. The instance is
   found and then rejected on size alone; raise the bound. -/
set_option synthInstance.maxSize 400

namespace Majorum

open the framework's flat multiset-log flavour

variable {Node Tx : Type} [DecidableEq Node] [DecidableEq Tx]
  {Q : Params} {S : Schedule Node} {n kappa : Nat} {pool : Nat → Tx} {proposer : Nat → Node}

local notation "Pr2" => protocol2 Q n kappa pool proposer

/-! ### Reducing `protocol2`'s step, projection-precisely

Same rationale as `protocol_step_tick` and friends: `simp only [protocol2]` would unfold
the definition inside implicit type arguments and poison later goals. -/

theorem protocol2_step_tick {p : Node} {r : Time}
    {V : View Node (Msg (Chain Tx) (QCert Node Tx))} {s : NodeState2 Node Tx} {res} :
    (protocol2 (Node := Node) Q n kappa pool proposer).step p r V s .tick res ↔
      res = handler2 Q n kappa pool proposer p r V s := Iff.rfl

theorem protocol2_step_recv {p : Node} {r : Time}
    {V : View Node (Msg (Chain Tx) (QCert Node Tx))} {s : NodeState2 Node Tx}
    {m : SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))} {res} :
    (protocol2 (Node := Node) Q n kappa pool proposer).step p r V s (.recv m) res ↔
      res = { state := s, send := 0 } := Iff.rfl

theorem protocol2_step_wake {p : Node} {r : Time}
    {V : View Node (Msg (Chain Tx) (QCert Node Tx))} {s : NodeState2 Node Tx} {res} :
    (protocol2 (Node := Node) Q n kappa pool proposer).step p r V s .wake res ↔
      res = { state := { s with activeAt := activationRound Q r }, send := 0 } := Iff.rfl

/-! ### What `handler2` can send -/

/-- Algorithm 2's send discipline: only once active, and only a propose at the propose
    reading or a vote — with the paper's placeholder in the finality fields — at the vote
    reading, carrying the reading's slot. -/
theorem mem_handler2_send {p : Node} {r : Time}
    {V : View Node (Msg (Chain Tx) (QCert Node Tx))} {s : NodeState2 Node Tx}
    {m : Msg (Chain Tx) (QCert Node Tx)}
    (h : m ∈ (handler2 Q n kappa pool proposer p r V s).send) :
    s.activeAt ≤ r ∧
      ((∃ chp chC qc, m = .propose chp chC qc dotCk (r / Q.slotLength) ∧
          r % Q.slotLength = 0) ∨
        (∃ ch, m = .vote ch dotCk dotCk (r / Q.slotLength) ∧
          r % Q.slotLength = Q.delta)) := by
  simp only [handler2, apply_ite NodeStepResult.send] at h
  split_ifs at h <;> simp at h <;> subst h <;>
    first
      | exact ⟨‹p = proposer (r / Q.slotLength) ∧ s.activeAt ≤ r›.2,
          Or.inl ⟨_, _, _, rfl, ‹r % Q.slotLength = 0›⟩⟩
      | exact ⟨‹s.activeAt ≤ r›, Or.inr ⟨_, rfl, ‹r % Q.slotLength = Q.delta›⟩⟩

/-- `handler2` sends at most one message per step. -/
theorem handler2_send_subsingleton {p : Node} {r : Time}
    {V : View Node (Msg (Chain Tx) (QCert Node Tx))} {s : NodeState2 Node Tx}
    {m m' : Msg (Chain Tx) (QCert Node Tx)}
    (h : m ∈ (handler2 Q n kappa pool proposer p r V s).send)
    (h' : m' ∈ (handler2 Q n kappa pool proposer p r V s).send) : m = m' := by
  simp only [handler2, apply_ite NodeStepResult.send] at h h'
  split_ifs at h h' <;> simp_all

/-! ### What one step can contribute -/

/-- Each step's contribution to the log is the sender's own tick — with the message among
    that tick's `handler2` sends — or an adversarial injection while corrupt. -/
theorem emitted_step2 {x : Exec Pr2 S} {k : Nat}
    {sm : SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))}
    (hem : sm ∈ x[k + 1].sent - x[k].sent) :
    (∃ t : Time, x.lbl k = .tick sm.sender t ∧
        sm.sender ∈ S.awake ((x[k].time : Int)) ∧
        x[k + 1].time = x[k].time ∧ x[k + 1][sm.sender].clock = t ∧
        sm.msg ∈ (handler2 Q n kappa pool proposer sm.sender t
          x[k][sm.sender].view x[k][sm.sender].st).send) ∨
      sm.sender ∈ S.adv ((x[k].time : Int)) := by
  have hstep : Step Pr2 S (x.lbl k) x[k] x[k + 1] := x.step k
  refine hstep.elimR (motive := fun a c c' => sm ∈ c'.sent - c.sent →
      (∃ t : Time, a = Action.tick sm.sender t ∧
          sm.sender ∈ S.awake ((c.time : Int)) ∧ c'.time = c.time ∧
          c'[sm.sender].clock = t ∧
          sm.msg ∈ (handler2 Q n kappa pool proposer sm.sender t
            c[sm.sender].view c[sm.sender].st).send) ∨
        sm.sender ∈ S.adv ((c.time : Int)))
    ?_ ?_ ?_ ?_ ?_ ?_ hem
  · -- advance: the log does not move
    intro d t hem'
    have hz : ({ d with time := t } : Config Node (Msg (Chain Tx) (QCert Node Tx))
        (NodeState2 Node Tx)).sent - d.sent = 0 := by
      show d.sent - d.sent = 0
      ext a
      simp [Multiset.count_sub]
    rw [hz] at hem'
    simp at hem'
  · -- tick: the graph of `handler2`
    intro d d' q t hen hns hem'
    rw [nodeStep_iff_exists] at hns
    obtain ⟨res, hres, rfl⟩ := hns
    rw [protocol2_step_tick] at hres
    subst hres
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
    obtain ⟨res, hres, rfl⟩ := hns
    rw [protocol2_step_recv] at hres
    subst hres
    rw [← receive_sent q m d, applyNodeStepResult_sent_sub] at hem'
    simp at hem'
  · -- wake: sets the activation round, sends nothing
    intro d d' q hen hns hem'
    rw [nodeStep_iff_exists] at hns
    obtain ⟨res, hres, rfl⟩ := hns
    rw [protocol2_step_wake] at hres
    subst hres
    rw [applyNodeStepResult_sent_sub] at hem'
    simp at hem'
  · -- custom: there are none
    intro d d' q ev hen hns
    exact ev.elim
  · -- adversarial: the injection is the delta, and the signer is corrupt
    intro d q m hen hem'
    simp only [spec] at hen
    have hd : (⟨q, m⟩ ::ₘ d.sent) - d.sent
        = {(⟨q, m⟩ : SignedMsg Node (Msg (Chain Tx) (QCert Node Tx)))} := by
      rw [← Multiset.singleton_add, Multiset.add_sub_cancel_right]
    rw [show ({ d with sent := ⟨q, m⟩ ::ₘ d.sent } : Config Node
        (Msg (Chain Tx) (QCert Node Tx)) (NodeState2 Node Tx)).sent
        = ⟨q, m⟩ ::ₘ d.sent from rfl, hd] at hem'
    rw [Multiset.mem_singleton] at hem'
    subst hem'
    exact Or.inr hen

/-! ### Provenance of an honest vote -/

/-- **An honest vote pins down its own history** — `vote_provenance`, against `handler2`.
    A vote for slot `s` in the log, whose sender is still honest, was sent by that
    sender's tick at reading `voting(s)`, at real time `voting(s)`, with the joining gate
    open, and with the message among that one tick's handler sends. -/
theorem vote_provenance2 {x : Exec Pr2 S} (hsync : SynchronizedClocks x)
    (hmc : S.MonotoneCorruption) (hmono : TimeMonotone x) {i : Nat}
    {sm : SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))} {e : Chain Tx}
    {src tgt : Checkpoint (Chain Tx)} {s : Nat}
    (hmem : sm ∈ x[i].sent) (hhon : sm.sender ∉ S.adv ((x[i].time : Int)))
    (hmsg : sm.msg = .vote e src tgt s) :
    ∃ k, k < i ∧ x.lbl k = .tick sm.sender (Q.slotLength * s + Q.delta) ∧
      x[k].time = Q.slotLength * s + Q.delta ∧
      x[k][sm.sender].st.activeAt ≤ Q.slotLength * s + Q.delta ∧
      sm.msg ∈ (handler2 Q n kappa pool proposer sm.sender (Q.slotLength * s + Q.delta)
        x[k][sm.sender].view x[k][sm.sender].st).send := by
  obtain ⟨k, hki, hem⟩ := emitted_of_mem_sent hmem
  have hhonk : sm.sender ∉ S.adv ((x[k].time : Int)) := fun hadv =>
    hhon (hmc _ _ (by exact_mod_cast time_le_of_le hmono (Nat.le_of_lt hki)) hadv)
  rcases emitted_step2 hem with ⟨t, hlbl, hawake, htime, hclock, hsend⟩ | hadv
  · obtain ⟨hactive, hshape⟩ := mem_handler2_send hsend
    -- the vote's slot pins the reading: `t = 4Δs + Δ`
    have ht : t = Q.slotLength * s + Q.delta := by
      rcases hshape with ⟨chp, chC, qc, heq, -⟩ | ⟨ch, heq, hmod⟩
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
theorem voting_le_of_vote_mem2 {x : Exec Pr2 S} (hsync : SynchronizedClocks x)
    (hmc : S.MonotoneCorruption) (hmono : TimeMonotone x) {i : Nat}
    {sm : SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))} {e : Chain Tx}
    {src tgt : Checkpoint (Chain Tx)} {s : Nat}
    (hmem : sm ∈ x[i].sent) (hhon : sm.sender ∉ S.adv ((x[i].time : Int)))
    (hmsg : sm.msg = .vote e src tgt s) :
    Q.slotLength * s + Q.delta ≤ x[i].time := by
  obtain ⟨k, hki, -, htimek, -, -⟩ := vote_provenance2 hsync hmc hmono hmem hhon hmsg
  rw [← htimek]
  exact time_le_of_le hmono (Nat.le_of_lt hki)

/-- **One honest validator, one slot, one vote** — for Algorithm 2. -/
theorem honest_vote_unique2 {x : Exec Pr2 S} (hsync : SynchronizedClocks x)
    (hone : OneTickPerReading x) (hmc : S.MonotoneCorruption) (hmono : TimeMonotone x)
    {i j : Nat} {sm sm' : SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))}
    {e e' : Chain Tx} {src tgt src' tgt' : Checkpoint (Chain Tx)} {s : Nat}
    (hm : sm ∈ x[i].sent) (hm' : sm' ∈ x[j].sent)
    (hh : sm.sender ∉ S.adv ((x[i].time : Int)))
    (hh' : sm'.sender ∉ S.adv ((x[j].time : Int)))
    (hs : sm'.sender = sm.sender)
    (hmsg : sm.msg = .vote e src tgt s) (hmsg' : sm'.msg = .vote e' src' tgt' s) :
    sm' = sm := by
  obtain ⟨k, -, hlbl, -, -, hsend⟩ := vote_provenance2 hsync hmc hmono hm hh hmsg
  obtain ⟨k', -, hlbl', -, -, hsend'⟩ := vote_provenance2 hsync hmc hmono hm' hh' hmsg'
  rw [hs] at hlbl'
  have hk : k' = k := hone k' k sm.sender _ hlbl' hlbl
  subst hk
  rw [hs] at hsend'
  have hmm : sm.msg = sm'.msg := handler2_send_subsingleton hsend hsend'
  cases sm
  cases sm'
  simp_all

/-! ### The activation round is trustworthy — Algorithm 2's copies -/

/-- `processProposals2` never writes `activeAt`. -/
theorem processProposals2_activeAt (V : View Node (Msg (Chain Tx) (QCert Node Tx)))
    (t : Nat) (s : NodeState2 Node Tx) :
    (processProposals2 n V t s).activeAt = s.activeAt := by
  unfold processProposals2
  generalize V.toList = l
  induction l generalizing s with
  | nil => rfl
  | cons a l ih =>
      rw [List.foldl_cons, ih]
      cases hm : a.msg with
      | vote ch src tgt t' => rfl
      | propose chp chC qc ck t' =>
          dsimp only
          split_ifs <;> rfl

/-- Neither does any branch of `handler2`: activation is written by wake events alone. -/
theorem handler2_activeAt (p : Node) (r : Time)
    (V : View Node (Msg (Chain Tx) (QCert Node Tx))) (s : NodeState2 Node Tx) :
    (handler2 Q n kappa pool proposer p r V s).state.activeAt = s.activeAt := by
  simp only [handler2, apply_ite NodeStepResult.state]
  split_ifs <;> simp [processProposals2_activeAt]

/-- A wake event writes the activation round of its own round. -/
theorem wake_sets_activeAt2 {x : Exec Pr2 S} (hsync : SynchronizedClocks x) {k : Nat}
    {p : Node} (hlbl : x.lbl k = .wake p) :
    x[k + 1][p].st.activeAt = activationRound Q x[k].time := by
  have hstep : Step Pr2 S (x.lbl k) x[k] x[k + 1] := x.step k
  rw [hlbl] at hstep
  obtain ⟨hen, heff⟩ := hstep
  simp only [spec] at hen heff
  have hclock : x[k][p].clock = x[k].time := hsync k p hen.1
  rw [nodeStep_iff_exists] at heff
  obtain ⟨res, hres, hpost⟩ := heff
  rw [protocol2_step_wake] at hres
  subst hres
  rw [hpost, applyNodeStepResult_getElem, if_pos rfl]
  dsimp only
  rw [hclock]

/-- One step cannot lower `activeAt` below a bound that also lies below the activation
    round of the current time. Same motive-threading as `activeAt_lb_step`. -/
theorem activeAt_lb_step2 {x : Exec Pr2 S} (hsync : SynchronizedClocks x) {m : Nat}
    {p : Node} {A : Time} (hA : A ≤ x[m][p].st.activeAt)
    (hAm : A ≤ activationRound Q x[m].time) : A ≤ x[m + 1][p].st.activeAt := by
  have hstep : Step Pr2 S (x.lbl m) x[m] x[m + 1] := x.step m
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
    rw [protocol2_step_tick] at hres
    subst hres
    by_cases hq : q = p
    · subst hq
      simpa [applyNodeStepResult_getElem, handler2_activeAt, setClock_getElem] using h
    · simpa [applyNodeStepResult_getElem, setClock_getElem, hq] using h
  · -- deliver: the recv reaction returns the state unchanged
    intro d d' q mm hen hns h _ _
    rw [nodeStep_iff_exists] at hns
    obtain ⟨res, hres, rfl⟩ := hns
    rw [protocol2_step_recv] at hres
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
    rw [protocol2_step_wake] at hres
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

/-- **An honest voter is active** — the containment, for Algorithm 2. Same dichotomy as
    `mem_active_of_honest_vote`: awake through the whole window, or the wake machinery
    makes the stored activation round trustworthy and a wake that recent contradicts the
    open gate the vote itself certifies. -/
theorem mem_active_of_honest_vote2 [Fintype Node] {x : Exec Pr2 S}
    (hsync : SynchronizedClocks x) (hstepw : TimeStepwise x) (hdil : Diligent x)
    (hwpt : WakePrecedesTick x) (hmc : S.MonotoneCorruption)
    {i : Nat} {sm : SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))} {e : Chain Tx}
    {src tgt : Checkpoint (Chain Tx)} {t : Nat} (ht : 1 ≤ t)
    (hmem : sm ∈ x[i].sent) (hhon : sm.sender ∉ S.adv ((x[i].time : Int)))
    (hmsg : sm.msg = .vote e src tgt t) :
    sm.sender ∈ Active Q S (t : Int) := by
  have hmono := hstepw.timeMonotone
  obtain ⟨j, hji, hlbl, htj, hgate, -⟩ := vote_provenance2 hsync hmc hmono hmem hhon hmsg
  -- the voter is awake at `voting(t)`: the tick's own enabling condition
  have hstepj : Step Pr2 S (x.lbl j) x[j] x[j + 1] := x.step j
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
    obtain ⟨w, hw⟩ : ∃ w : Nat, (w : Int) = bad.max' hbadne + 1 :=
      ⟨(bad.max' hbadne + 1).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hnvt : w ≤ Q.slotLength * t + Q.delta := by
      have h2 : (w : Int) ≤ ((Q.slotLength * t + Q.delta : Nat) : Int) := by
        rw [hw, ← hvot]
        omega
      exact_mod_cast h2
    -- a wake event of the sender at time `w`, strictly before the vote tick
    have hwake : ∃ k, k < j ∧ x.lbl k = .wake sm.sender ∧ x[k].time = w := by
      rcases Nat.lt_or_ge w (Q.slotLength * t + Q.delta) with hnlt | hnge
      · -- the transition is strictly below the vote round: Diligent ticks it there
        obtain ⟨i₀, hi₀j, hti₀⟩ := exists_time_eq hstepw
          (show w ≤ x[j].time by rw [htj]; omega)
        have hAw : x.Awake i₀ sm.sender := by
          show sm.sender ∈ S.awake ((x[i₀].time : Int))
          rw [hti₀, hw]
          exact hawakeW _ (by omega) (by omega)
        obtain ⟨i₁, hti₁, hlbl₁⟩ := hdil w sm.sender ⟨i₀, hti₀, hAw⟩
        have hnaw : sm.sender ∉ S.awake ((x[i₁].time : Int) - 1) := by
          rw [hti₁, hw]
          simpa using hwna
        obtain ⟨k, hki₁, hwk, htk'⟩ := hwpt i₁ sm.sender w hlbl₁ hnaw
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
        have hneq : w = Q.slotLength * t + Q.delta := by omega
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
    have hbase : x[k + 1][sm.sender].st.activeAt = activationRound Q w := by
      have h := wake_sets_activeAt2 hsync hwk
      rw [htk] at h
      exact h
    have hpers : ∀ m, k + 1 ≤ m → m ≤ j →
        activationRound Q w ≤ x[m][sm.sender].st.activeAt := by
      intro m
      induction m with
      | zero => omega
      | succ m ih =>
          intro h1 h2
          rcases Nat.eq_or_lt_of_le h1 with heq | hlt
          · have hkm : k = m := by omega
            subst hkm
            exact le_of_eq hbase.symm
          · refine activeAt_lb_step2 hsync (ih (by omega) (by omega)) ?_
            exact activationRound_mono Q (htk ▸ time_le_of_le hmono (by omega : k ≤ m))
    have hAj := hpers j (by omega) (le_refl j)
    -- a wake this recent activates only after `voting(t)` — against the open gate
    have harith : Q.slotLength * t < w + 2 * Q.delta := by
      have h2 : ((Q.slotLength * t : Nat) : Int) < (w : Int) + 2 * (Q.delta : Int) := by
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

/-! ### The propose-round half of Lemma 2, for Algorithm 2 -/

section Lemma2Propose

variable [Fintype Node]

/-- **Lemma 2's hypothesis, over the log**: every validator active in slot `t` has, by the
    end of `voting(t)`, sent a slot-`t` vote for a chain extending `ch`. Algorithm 2's
    honest votes carry `dotCk` in the finality fields, so the hypothesis pins them. -/
def ActiveVotesExtend2 (x : Exec Pr2 S) (t : Nat) (ch : Chain Tx) : Prop :=
  ∀ p ∈ Active Q S (t : Int), ∃ (i : Nat) (e : Chain Tx),
    x[i].time = Q.slotLength * t + Q.delta ∧
    (⟨p, Msg.vote e dotCk dotCk t⟩ : SignedMsg Node (Msg (Chain Tx) (QCert Node Tx)))
      ∈ x[i].sent ∧
    chainLe ch e

set_option maxHeartbeats 1000000 in
/-- **The propose-round half of Lemma 2, for Algorithm 2**: if every validator active in
    slot `t` voted for an extension of `ch`, then at `propose(t+1)` the fork-choice of any
    validator active in slot `t+1` returns an extension of `ch`, over any base `b ⪯ ch`.
    Same assembly as `le_mfc_at_propose`, against `handler2`.

    The heartbeat bump is the concrete certificate type again: the closing `omega` and the
    `Majority` unfolding re-check definitional equality under instances that are atomic in
    the Algorithm-5 layer but full derivation trees here. -/
theorem le_mfc_at_propose2 {x : Exec Pr2 S}
    (hsync : SynchronizedClocks x) (hstepw : TimeStepwise x) (hdil : Diligent x)
    (hwpt : WakePrecedesTick x) (hone : OneTickPerReading x) (hmc : S.MonotoneCorruption)
    (hsyn : Synchrony 0 Q.delta x) (hslp : Sleepiness Q S) (hgst : Q.gst = 0)
    {t : Nat} (ht : 1 ≤ t) {ch : Chain Tx} (hvotes : ActiveVotesExtend2 x t ch)
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
    obtain ⟨iv, e, htiv, hsent, hext⟩ := hvotes p hpA
    have hhon : ∀ r : Time, r ≤ Q.slotLength * (t + 1) + Q.delta →
        p ∉ S.adv ((r : Int)) := by
      intro r hr had
      refine hpH (hmc _ _ ?_ had)
      rw [hvot1]
      exact_mod_cast hr
    -- delivery: sent at `voting(t)`, in the view by `propose(t+1)`
    have hview : (⟨p, Msg.vote e dotCk dotCk t⟩ :
        SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ x[ip][v].view := by
      refine hsyn iv ip v _ hsent ?_ hvAw
      rw [htiv, hip]
      omega
    have hsent_ip : (⟨p, Msg.vote e dotCk dotCk t⟩ :
        SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ x[ip].sent :=
      views_sound x ip v _ hview
    have hhon_ip : p ∉ S.adv ((x[ip].time : Int)) := by
      rw [hip]
      exact hhon _ (by omega)
    refine ⟨⟨p, Msg.vote e dotCk dotCk t⟩, ?_, rfl⟩
    -- build the filter membership inside out
    have hvv : (⟨p, Msg.vote e dotCk dotCk t⟩ :
        SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ votes (x[ip][v].view) := by
      simp only [votes, Finset.mem_filter]
      exact ⟨hview, trivial⟩
    have hfeq : (⟨p, Msg.vote e dotCk dotCk t⟩ :
        SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ filEq (x[ip][v].view) := by
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
      have heq := honest_vote_unique2 hsync hone hmc hmono hsent_ip hsm'log hhon_ip hh'
        hsend' rfl hm'
      exact hne (by rw [heq])
    have hfexp : (⟨p, Msg.vote e dotCk dotCk t⟩ :
        SignedMsg Node (Msg (Chain Tx) (QCert Node Tx)))
        ∈ fil1Exp (filEq (x[ip][v].view)) (t + 1) := by
      simp only [fil1Exp, Finset.mem_filter]
      exact ⟨hfeq, rfl⟩
    have hflmd : (⟨p, Msg.vote e dotCk dotCk t⟩ :
        SignedMsg Node (Msg (Chain Tx) (QCert Node Tx)))
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
    exact mem_active_of_honest_vote2 hsync hstepw hdil hwpt hmc ht hqlog hh' hm'
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
