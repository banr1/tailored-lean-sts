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
  {dot : Checkpoint (Chain Tx)}

local notation "Pr2" => protocol2 Q n kappa pool proposer

/-! ### Reducing `protocol2`'s step, projection-precisely

Same rationale as `protocol_step_tick` and friends: `simp only [protocol2]` would unfold
the definition inside implicit type arguments and poison later goals. -/

theorem protocol2_step_tick {p : Node} {r : Time}
    {V : View Node (Msg (Chain Tx) (QCert Node Tx))} {s : NodeState2 Node Tx} {res} :
    (protocol2 (Node := Node) Q n kappa pool proposer).step p r V s .tick res ↔
      ∃ dot : Checkpoint (Chain Tx),
        res = handler2 Q n kappa pool proposer dot p r V s := Iff.rfl

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
    (h : m ∈ (handler2 Q n kappa pool proposer dot p r V s).send) :
    s.activeAt ≤ r ∧
      ((∃ chp chC qc, m = .propose chp chC qc dot (r / Q.slotLength) ∧
          r % Q.slotLength = 0) ∨
        (∃ ch, m = .vote ch dot dot (r / Q.slotLength) ∧
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
    (h : m ∈ (handler2 Q n kappa pool proposer dot p r V s).send)
    (h' : m' ∈ (handler2 Q n kappa pool proposer dot p r V s).send) : m = m' := by
  simp only [handler2, apply_ite NodeStepResult.send] at h h'
  split_ifs at h h' <;> simp_all

/-! ### What one step can contribute -/

/-- Each step's contribution to the log is the sender's own tick — with the message among
    that tick's `handler2` sends — or an adversarial injection while corrupt. -/
theorem emitted_step2 {x : Exec Pr2 S} {k : Nat}
    {sm : SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))}
    (hem : sm ∈ x[k + 1].sent - x[k].sent) :
    (∃ (t : Time) (dot : Checkpoint (Chain Tx)), x.lbl k = .tick sm.sender t ∧
        sm.sender ∈ S.awake ((x[k].time : Int)) ∧
        x[k + 1].time = x[k].time ∧ x[k + 1][sm.sender].clock = t ∧
        sm.msg ∈ (handler2 Q n kappa pool proposer dot sm.sender t
          x[k][sm.sender].view x[k][sm.sender].st).send) ∨
      sm.sender ∈ S.adv ((x[k].time : Int)) := by
  have hstep : Step Pr2 S (x.lbl k) x[k] x[k + 1] := x.step k
  refine hstep.elimR (motive := fun a c c' => sm ∈ c'.sent - c.sent →
      (∃ (t : Time) (dot : Checkpoint (Chain Tx)), a = Action.tick sm.sender t ∧
          sm.sender ∈ S.awake ((c.time : Int)) ∧ c'.time = c.time ∧
          c'[sm.sender].clock = t ∧
          sm.msg ∈ (handler2 Q n kappa pool proposer dot sm.sender t
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
  · -- tick: the graph of `handler2`, for the filler this tick chose
    intro d d' q t hen hns hem'
    rw [nodeStep_iff_exists] at hns
    obtain ⟨res, hres, rfl⟩ := hns
    rw [protocol2_step_tick] at hres
    obtain ⟨dt, rfl⟩ := hres
    rw [← setClock_sent q t d, applyNodeStepResult_sent_sub] at hem'
    obtain ⟨mm, hmm, hsm⟩ := Multiset.mem_map.mp hem'
    subst hsm
    simp only [spec] at hen
    refine Or.inl ⟨t, dt, rfl, hen, rfl, ?_, ?_⟩
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
    open — and it is among that one step's contribution to the log, which is what
    uniqueness consumes now that each tick chooses its own blank filler. -/
theorem vote_provenance2 {x : Exec Pr2 S} (hsync : SynchronizedClocks x)
    (hmc : S.MonotoneCorruption) (hmono : TimeMonotone x) {i : Nat}
    {sm : SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))} {e : Chain Tx}
    {src tgt : Checkpoint (Chain Tx)} {s : Nat}
    (hmem : sm ∈ x[i].sent) (hhon : sm.sender ∉ S.adv ((x[i].time : Int)))
    (hmsg : sm.msg = .vote e src tgt s) :
    ∃ k, k < i ∧ x.lbl k = .tick sm.sender (Q.slotLength * s + Q.delta) ∧
      x[k].time = Q.slotLength * s + Q.delta ∧
      x[k][sm.sender].st.activeAt ≤ Q.slotLength * s + Q.delta ∧
      sm ∈ x[k + 1].sent - x[k].sent := by
  obtain ⟨k, hki, hem⟩ := emitted_of_mem_sent hmem
  have hhonk : sm.sender ∉ S.adv ((x[k].time : Int)) := fun hadv =>
    hhon (hmc _ _ (by exact_mod_cast time_le_of_le hmono (Nat.le_of_lt hki)) hadv)
  rcases emitted_step2 hem with ⟨t, dt, hlbl, hawake, htime, hclock, hsend⟩ | hadv
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
    exact ⟨k, hki, hlbl, htimek, hactive, hem⟩
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

/-- One tick contributes at most one message to the log: its delta is the handler's
    sends, all signed by the ticker, and the handler sends at most one message —
    whatever filler this tick chose. -/
theorem tick_sends_subsingleton {x : Exec Pr2 S} {k : Nat} {p : Node} {t : Time}
    (hlbl : x.lbl k = .tick p t)
    {sm sm' : SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))}
    (h : sm ∈ x[k + 1].sent - x[k].sent) (h' : sm' ∈ x[k + 1].sent - x[k].sent) :
    sm = sm' := by
  have hstep : Step Pr2 S (x.lbl k) x[k] x[k + 1] := x.step k
  rw [hlbl] at hstep
  obtain ⟨hen, heff⟩ := hstep
  simp only [spec] at heff
  rw [nodeStep_iff_exists] at heff
  obtain ⟨res, hres, hpost⟩ := heff
  rw [protocol2_step_tick] at hres
  obtain ⟨dt, rfl⟩ := hres
  rw [hpost, ← setClock_sent p t x[k], applyNodeStepResult_sent_sub] at h h'
  obtain ⟨m, hm, rfl⟩ := Multiset.mem_map.mp h
  obtain ⟨m', hm', heq'⟩ := Multiset.mem_map.mp h'
  rw [← heq', handler2_send_subsingleton hm hm']

/-- **One honest validator, one slot, one vote** — for Algorithm 2. Both votes come from
    ticks at the same reading, hence from the *same* tick (`OneTickPerReading`), whose
    one log contribution they both are. -/
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
  obtain ⟨k, -, hlbl, -, -, hem⟩ := vote_provenance2 hsync hmc hmono hm hh hmsg
  obtain ⟨k', -, hlbl', -, -, hem'⟩ := vote_provenance2 hsync hmc hmono hm' hh' hmsg'
  rw [hs] at hlbl'
  have hk : k' = k := hone k' k sm.sender _ hlbl' hlbl
  subst hk
  exact tick_sends_subsingleton hlbl hem' hem

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
    (handler2 Q n kappa pool proposer dot p r V s).state.activeAt = s.activeAt := by
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
    obtain ⟨dt, rfl⟩ := hres
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

/-! ### What the vote-round half additionally needs: reading arithmetic -/

/-- `chainLe` is transitive (prefix order). -/
theorem chainLe_trans {a b c : Chain Tx} (h1 : chainLe a b) (h2 : chainLe b c) :
    chainLe a c := by
  rw [chainLe_iff_prefix] at h1 h2 ⊢
  exact h1.trans h2

/-- The vote reading of slot `t+1`, reduced. -/
theorem voting_reading_mod (Q : Params) (t : Nat) :
    (Q.slotLength * t + Q.delta) % Q.slotLength = Q.delta := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  rw [Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt (by omega)

theorem voting_reading_div (Q : Params) (t : Nat) :
    (Q.slotLength * t + Q.delta) / Q.slotLength = t := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega)]
  omega

/-- The merge reading of slot `t`, reduced. -/
theorem merge_reading_mod (Q : Params) (t : Nat) :
    (Q.slotLength * t + 3 * Q.delta) % Q.slotLength = 3 * Q.delta := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  rw [Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt (by omega)

theorem merge_reading_div (Q : Params) (t : Nat) :
    (Q.slotLength * t + 3 * Q.delta) / Q.slotLength = t := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega)]
  omega

/-- Between `merge(t)` and `voting(t+1)` inclusive, a reading with the merge phase is
    `merge(t)` itself, and one with the vote phase is `voting(t+1)` itself — the
    arithmetic behind "no other tick can write the frozen state in that window". -/
theorem phase_pins_reading (Q : Params) {t tr : Nat}
    (hlo : Q.slotLength * t + 3 * Q.delta ≤ tr)
    (hhi : tr ≤ Q.slotLength * (t + 1) + Q.delta) :
    (tr % Q.slotLength = 3 * Q.delta → tr = Q.slotLength * t + 3 * Q.delta) ∧
      (tr % Q.slotLength = Q.delta → tr = Q.slotLength * (t + 1) + Q.delta) := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  have hdm := Nat.div_add_mod tr Q.slotLength
  set k := tr / Q.slotLength with hk
  have he1 : Q.slotLength * (t + 1) = Q.slotLength * t + Q.slotLength := Nat.mul_succ ..
  have he2 : Q.slotLength * (k + 1) = Q.slotLength * k + Q.slotLength := Nat.mul_succ ..
  have he3 : Q.slotLength * (t + 2) = Q.slotLength * (t + 1) + Q.slotLength :=
    Nat.mul_succ ..
  constructor
  · intro hmod
    rw [hmod] at hdm
    have hup : ¬ (t + 1 ≤ k) := by
      intro h
      have := Nat.mul_le_mul_left Q.slotLength h
      omega
    have hdown : ¬ (k + 1 ≤ t) := by
      intro h
      have := Nat.mul_le_mul_left Q.slotLength h
      omega
    have hkt : k = t := by omega
    rw [hkt] at hdm
    omega
  · intro hmod
    rw [hmod] at hdm
    have hup : ¬ (t + 2 ≤ k) := by
      intro h
      have := Nat.mul_le_mul_left Q.slotLength h
      omega
    have hdown : ¬ (k ≤ t) := by
      intro h
      have := Nat.mul_le_mul_left Q.slotLength h
      omega
    have hkt : k = t + 1 := by omega
    rw [hkt] at hdm
    omega

/-- A wake round no later than the top of slot `t1`'s activity window activates by
    `voting(t1)`: `activationRound` is monotone and hits `voting(t1)` exactly at the
    window's bottom `voting(t1) − 3Δ`. -/
theorem activationRound_le_voting (Q : Params) {r : Time} {t1 : Nat}
    (hr : r + 3 * Q.delta ≤ Q.slotLength * t1 + Q.delta) :
    activationRound Q r ≤ Q.slotLength * t1 + Q.delta := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  unfold activationRound
  have hle : (r + 2 * Q.delta + (Q.slotLength - 1)) / Q.slotLength ≤ t1 := by
    rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
    omega
  have := Nat.mul_le_mul_left Q.slotLength hle
  omega

/-! ### What one step cannot change: the frozen snapshots -/

/-- `processProposals2` never writes `vFrozen`. -/
theorem processProposals2_vFrozen (V : View Node (Msg (Chain Tx) (QCert Node Tx)))
    (t : Nat) (s : NodeState2 Node Tx) :
    (processProposals2 n V t s).vFrozen = s.vFrozen := by
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

open Classical in
/-- What `processProposals2` can leave in `chFrozen`: the value it started from, or the
    fast-confirmed chain of a proposal that is in the view, is for this slot, and passed
    the certificate check. The lines 33–36 provenance, as a fold invariant. -/
theorem processProposals2_chFrozen (V : View Node (Msg (Chain Tx) (QCert Node Tx)))
    (t : Nat) (s : NodeState2 Node Tx) :
    (processProposals2 n V t s).chFrozen = s.chFrozen ∨
      ∃ sm ∈ V, (∃ chp qc ck, sm.msg =
          .propose chp ((processProposals2 n V t s).chFrozen) qc ck t) ∧
        ValidProposal2 n V sm := by
  unfold processProposals2
  have hgen : ∀ (l : List (SignedMsg Node (Msg (Chain Tx) (QCert Node Tx)))),
      (∀ a ∈ l, a ∈ V) → ∀ s₀ : NodeState2 Node Tx,
      (l.foldl (fun acc sm =>
        match sm.msg with
        | .propose _ chC _ _ t' =>
            if t' = t ∧ ValidProposal2 n V sm ∧ chainLe acc.chFrozen chC then
              { acc with chFrozen := chC }
            else acc
        | .vote .. => acc) s₀).chFrozen = s₀.chFrozen ∨
      ∃ sm ∈ V, (∃ chp qc ck, sm.msg = .propose chp ((l.foldl (fun acc sm =>
        match sm.msg with
        | .propose _ chC _ _ t' =>
            if t' = t ∧ ValidProposal2 n V sm ∧ chainLe acc.chFrozen chC then
              { acc with chFrozen := chC }
            else acc
        | .vote .. => acc) s₀).chFrozen) qc ck t) ∧ ValidProposal2 n V sm := by
    intro l
    induction l with
    | nil => exact fun _ s₀ => Or.inl rfl
    | cons a l ih =>
        intro hl s₀
        rw [List.foldl_cons]
        rcases ih (fun b hb => hl b (List.mem_cons_of_mem a hb)) _ with h | h
        · rw [h]
          obtain ⟨asd, amsg⟩ := a
          cases amsg with
          | vote ch src tgt t' => exact Or.inl rfl
          | propose chp chC qc ck t' =>
              dsimp only
              split_ifs with hcond
              · refine Or.inr ⟨⟨asd, .propose chp chC qc ck t'⟩,
                  hl _ List.mem_cons_self, ⟨chp, qc, ck, ?_⟩, hcond.2.1⟩
                rw [hcond.1]
              · exact Or.inl rfl
        · exact Or.inr h
  exact hgen V.toList (fun a ha => (Finset.mem_toList).mp ha) s

/-- Outside the vote and merge phases, no branch of `handler2` writes the frozen state. -/
theorem handler2_frozen {p : Node} {r : Time}
    {V : View Node (Msg (Chain Tx) (QCert Node Tx))} {s : NodeState2 Node Tx}
    (h1 : r % Q.slotLength ≠ Q.delta) (h2 : r % Q.slotLength ≠ 3 * Q.delta) :
    (handler2 Q n kappa pool proposer dot p r V s).state.vFrozen = s.vFrozen ∧
      (handler2 Q n kappa pool proposer dot p r V s).state.chFrozen = s.chFrozen := by
  simp only [handler2, apply_ite NodeStepResult.state]
  split_ifs <;>
    first
      | exact ⟨rfl, rfl⟩
      | exact absurd ‹r % Q.slotLength = Q.delta› h1
      | exact absurd ‹r % Q.slotLength = 3 * Q.delta› h2

/-- The merge phase, unfolded: freeze the view and the fast-confirmed chain. -/
theorem handler2_merge {p : Node} {r : Time}
    {V : View Node (Msg (Chain Tx) (QCert Node Tx))} {s : NodeState2 Node Tx}
    (hmod : r % Q.slotLength = 3 * Q.delta) :
    (handler2 Q n kappa pool proposer dot p r V s).state =
      { s with vFrozen := V, chFrozen := (fastConfirmSimple n V (r / Q.slotLength)).1 } := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  simp only [handler2, apply_ite NodeStepResult.state]
  split_ifs <;> first | rfl | omega

/-- The chain the vote phase settles on extends this tick's fork-choice: `proposedNow`
    filters on exactly that, and its absence falls back to the fork-choice itself. -/
theorem chainLe_getD_findSome (l : List (SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))))
    (chMFC : Chain Tx) (slot : Nat) :
    chainLe chMFC ((l.findSome? (fun sm => match sm.msg with
      | .propose chp _ _ _ t' =>
          if t' == slot && proposedAt chp == slot && chainLe chMFC chp then some chp
          else none
      | .vote .. => none)).getD chMFC) := by
  cases hfind : l.findSome? (fun sm => match sm.msg with
      | .propose chp _ _ _ t' =>
          if t' == slot && proposedAt chp == slot && chainLe chMFC chp then some chp
          else none
      | .vote .. => none) with
  | none => simp [chainLe_refl]
  | some chp =>
      obtain ⟨a, -, hfa⟩ := List.exists_of_findSome?_eq_some hfind
      simp only [Option.getD_some]
      revert hfa
      cases a.msg with
      | vote e src tgt s₁ => intro h; cases h
      | propose chp' chC' qc' ck' t' =>
          dsimp only
          split_ifs with hcond
          · intro h
            injection h with h
            subst h
            simp only [Bool.and_eq_true] at hcond
            exact hcond.2
          · intro h
            cases h

/-- The vote phase's send, with the joining check open: one vote, for a chain extending
    this tick's fork-choice over the processed state. -/
theorem handler2_vote_send {p : Node} {r : Time}
    {V : View Node (Msg (Chain Tx) (QCert Node Tx))} {s : NodeState2 Node Tx}
    (hmod : r % Q.slotLength = Q.delta) (hgate : s.activeAt ≤ r) :
    ∃ ch, (handler2 Q n kappa pool proposer dot p r V s).send
        = {Msg.vote ch dot dot (r / Q.slotLength)} ∧
      chainLe (mfc (processProposals2 n V (r / Q.slotLength) s).vFrozen V
        (processProposals2 n V (r / Q.slotLength) s).chFrozen (r / Q.slotLength)) ch := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  simp only [handler2, apply_ite NodeStepResult.send]
  split_ifs <;>
    first
      | omega
      | exact ⟨_, rfl, chainLe_getD_findSome _ _ _⟩

/-! ### One tick, precisely: state, time, reading, emission -/

/-- A tick step, described whole: for the filler this tick chose, the ticking
    validator's successor state is the handler's, and every handler send is in the next
    log. One existential, so state facts and emissions about the same tick agree on the
    filler. -/
theorem tick_effect {x : Exec Pr2 S} {k : Nat} {p : Node} {t : Time}
    (hlbl : x.lbl k = .tick p t) :
    ∃ dt : Checkpoint (Chain Tx),
      x[k + 1][p].st =
        (handler2 Q n kappa pool proposer dt p t x[k][p].view x[k][p].st).state ∧
      ∀ m ∈ (handler2 Q n kappa pool proposer dt p t x[k][p].view x[k][p].st).send,
        (⟨p, m⟩ : SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ x[k + 1].sent := by
  have hstep : Step Pr2 S (x.lbl k) x[k] x[k + 1] := x.step k
  rw [hlbl] at hstep
  obtain ⟨hen, heff⟩ := hstep
  simp only [spec] at hen heff
  rw [nodeStep_iff_exists] at heff
  obtain ⟨res, hres, hpost⟩ := heff
  rw [protocol2_step_tick] at hres
  obtain ⟨dt, rfl⟩ := hres
  refine ⟨dt, ?_, ?_⟩
  · rw [hpost, applyNodeStepResult_getElem, if_pos rfl]
    dsimp only
    simp [setClock_getElem]
  · intro m hm
    rw [hpost, applyNodeStepResult_sent, setClock_sent]
    refine Multiset.mem_add.mpr (Or.inr (Multiset.mem_map.mpr ⟨m, ?_, rfl⟩))
    simpa [setClock_getElem] using hm

/-- A tick does not move real time. -/
theorem tick_time {x : Exec Pr2 S} {k : Nat} {p : Node} {t : Time}
    (hlbl : x.lbl k = .tick p t) : x[k + 1].time = x[k].time := by
  have hstep : Step Pr2 S (x.lbl k) x[k] x[k + 1] := x.step k
  rw [hlbl] at hstep
  obtain ⟨hen, heff⟩ := hstep
  simp only [spec] at heff
  rw [nodeStep_iff_exists] at heff
  obtain ⟨res, hres, hpost⟩ := heff
  rw [hpost]
  rfl

/-- Under synchronized clocks, a tick's reading is the real time it happens at. -/
theorem tick_reading {x : Exec Pr2 S} (hsync : SynchronizedClocks x) {k : Nat} {p : Node}
    {t : Time} (hlbl : x.lbl k = .tick p t) : x[k].time = t := by
  have hstep : Step Pr2 S (x.lbl k) x[k] x[k + 1] := x.step k
  rw [hlbl] at hstep
  obtain ⟨hen, heff⟩ := hstep
  simp only [spec] at hen heff
  rw [nodeStep_iff_exists] at heff
  obtain ⟨res, hres, hpost⟩ := heff
  have hclock : x[k + 1][p].clock = t := by
    rw [hpost]
    simp [setClock_getElem]
  have htime : x[k + 1].time = x[k].time := by
    rw [hpost]
    rfl
  have hAw : x.Awake (k + 1) p := by
    show p ∈ S.awake ((x[k + 1].time : Int))
    rw [htime]
    exact hen
  have := hsync (k + 1) p hAw
  rw [hclock, htime] at this
  omega

/-- Outside the vote and merge phases, one step preserves a validator's frozen state —
    whoever moves. -/
theorem frozen_step2 {x : Exec Pr2 S} {m : Nat} {p : Node}
    (hcond : ∀ tr : Time, x.lbl m = .tick p tr →
      tr % Q.slotLength ≠ Q.delta ∧ tr % Q.slotLength ≠ 3 * Q.delta) :
    x[m + 1][p].st.vFrozen = x[m][p].st.vFrozen ∧
      x[m + 1][p].st.chFrozen = x[m][p].st.chFrozen := by
  have hstep : Step Pr2 S (x.lbl m) x[m] x[m + 1] := x.step m
  refine hstep.elimR (motive := fun a c c' =>
      (∀ tr : Time, a = .tick p tr →
        tr % Q.slotLength ≠ Q.delta ∧ tr % Q.slotLength ≠ 3 * Q.delta) →
      c'[p].st.vFrozen = c[p].st.vFrozen ∧ c'[p].st.chFrozen = c[p].st.chFrozen)
    ?_ ?_ ?_ ?_ ?_ ?_ hcond
  · -- advance: nodes untouched
    intro d t _
    exact ⟨rfl, rfl⟩
  · -- tick: outside the writing phases by hypothesis
    intro d d' q t hen hns hc
    rw [nodeStep_iff_exists] at hns
    obtain ⟨res, hres, rfl⟩ := hns
    rw [protocol2_step_tick] at hres
    obtain ⟨dt, rfl⟩ := hres
    by_cases hq : q = p
    · subst hq
      have hph := hc t rfl
      have hfr := handler2_frozen (Q := Q) (n := n) (kappa := kappa) (pool := pool)
        (proposer := proposer) (dot := dt) (p := q) (r := t)
        (V := (setClock q t d)[q].view) (s := (setClock q t d)[q].st) hph.1 hph.2
      constructor
      · simpa [applyNodeStepResult_getElem, setClock_getElem] using hfr.1
      · simpa [applyNodeStepResult_getElem, setClock_getElem] using hfr.2
    · constructor <;> simp [applyNodeStepResult_getElem, setClock_getElem, hq]
  · -- deliver: the recv reaction returns the state unchanged
    intro d d' q mm hen hns _
    rw [nodeStep_iff_exists] at hns
    obtain ⟨res, hres, rfl⟩ := hns
    rw [protocol2_step_recv] at hres
    subst hres
    by_cases hq : q = p
    · subst hq
      constructor <;> simp [applyNodeStepResult_getElem, receive_getElem]
    · constructor <;> simp [applyNodeStepResult_getElem, receive_getElem, hq]
  · -- wake: writes `activeAt` only
    intro d d' q hen hns _
    rw [nodeStep_iff_exists] at hns
    obtain ⟨res, hres, rfl⟩ := hns
    rw [protocol2_step_wake] at hres
    subst hres
    by_cases hq : q = p
    · subst hq
      constructor <;> simp [applyNodeStepResult_getElem]
    · constructor <;> simp [applyNodeStepResult_getElem, hq]
  · -- custom: there are none
    intro d d' q ev hen hns
    exact ev.elim
  · -- adversarial: nodes untouched
    intro d q mm hen _
    exact ⟨rfl, rfl⟩

/-! ### The joining check stays open for an active validator -/

/-- `activeAt` never exceeds `voting(t1)` for a validator awake through slot `t1`'s
    activity window, as long as time has not passed `voting(t1)`: wakes strictly inside
    the window are impossible (the framework's wake event requires having been asleep the
    round before), and a wake at or before the window's bottom activates by `voting(t1)`.
    The dual of `activeAt_lb_step`, run from the initial state's `activeAt = 0`. -/
theorem activeAt_le_voting {x : Exec Pr2 S} (hsync : SynchronizedClocks x)
    (hmono : TimeMonotone x) {p : Node} {t1 : Nat}
    (hwin : ∀ r : Int, ((Q.slotLength * t1 + Q.delta : Nat) : Int) - 3 * Q.delta ≤ r →
      r ≤ ((Q.slotLength * t1 + Q.delta : Nat) : Int) → p ∈ S.awake r)
    {j : Nat} (hj : x[j].time ≤ Q.slotLength * t1 + Q.delta) :
    x[j][p].st.activeAt ≤ Q.slotLength * t1 + Q.delta := by
  induction j with
  | zero =>
      have h0 := x.init.2.1 p
      show ((x.cfg 0)[p]).st.activeAt ≤ Q.slotLength * t1 + Q.delta
      rw [h0]
      exact Nat.zero_le _
  | succ m ih =>
      have hm' : x[m].time ≤ Q.slotLength * t1 + Q.delta :=
        le_trans (time_le_of_le hmono (Nat.le_succ m)) hj
      have hA := ih hm'
      have hstep : Step Pr2 S (x.lbl m) x[m] x[m + 1] := x.step m
      refine hstep.elimR (motive := fun _ c c' =>
          c[p].st.activeAt ≤ Q.slotLength * t1 + Q.delta →
          c.time ≤ Q.slotLength * t1 + Q.delta →
          (∀ q : Node, q ∈ S.awake ((c.time : Int)) → c[q].clock = c.time) →
          c'[p].st.activeAt ≤ Q.slotLength * t1 + Q.delta)
        ?_ ?_ ?_ ?_ ?_ ?_ hA hm' (fun q hq => hsync m q hq)
      · -- advance: nodes untouched
        intro d t h _ _
        exact h
      · -- tick: the handler never writes `activeAt`
        intro d d' q t hen hns h _ _
        rw [nodeStep_iff_exists] at hns
        obtain ⟨res, hres, rfl⟩ := hns
        rw [protocol2_step_tick] at hres
        obtain ⟨dt, rfl⟩ := hres
        by_cases hq : q = p
        · subst hq
          simpa [applyNodeStepResult_getElem, handler2_activeAt, setClock_getElem] using h
        · simpa [applyNodeStepResult_getElem, setClock_getElem, hq] using h
      · -- deliver: state unchanged
        intro d d' q mm hen hns h _ _
        rw [nodeStep_iff_exists] at hns
        obtain ⟨res, hres, rfl⟩ := hns
        rw [protocol2_step_recv] at hres
        subst hres
        by_cases hq : q = p
        · subst hq
          simpa [applyNodeStepResult_getElem, receive_getElem] using h
        · simpa [applyNodeStepResult_getElem, receive_getElem, hq] using h
      · -- wake: only possible at or below the window's bottom
        intro d d' q hen hns h hm'' hclocks
        simp only [spec] at hen
        rw [nodeStep_iff_exists] at hns
        obtain ⟨res, hres, rfl⟩ := hns
        rw [protocol2_step_wake] at hres
        subst hres
        by_cases hq : q = p
        · subst hq
          have hlow : (d.time : Int) - 1 <
              ((Q.slotLength * t1 + Q.delta : Nat) : Int) - 3 * Q.delta := by
            by_contra hge
            refine hen.2 (hwin ((d.time : Int) - 1) (by omega) ?_)
            have hdt : (d.time : Int) ≤ ((Q.slotLength * t1 + Q.delta : Nat) : Int) := by
              exact_mod_cast hm''
            omega
          have hr : d.time + 3 * Q.delta ≤ Q.slotLength * t1 + Q.delta := by
            have h2 : (d.time : Int) + 3 * Q.delta ≤
                ((Q.slotLength * t1 + Q.delta : Nat) : Int) := by omega
            exact_mod_cast h2
          simpa [applyNodeStepResult_getElem, hclocks q hen.1] using
            activationRound_le_voting Q hr
        · simpa [applyNodeStepResult_getElem, hq] using h
      · -- custom: there are none
        intro d d' q ev hen hns
        exact ev.elim
      · -- adversarial: nodes untouched
        intro d q mm hen h _ _
        exact h

/-! ### `fastconfirmsimple`'s output is empty or quorum-supported -/

/-- The longest-chain fold returns its initial value or a member of the list. -/
theorem foldl_longest_mem_or_init {l : List (Chain Tx)} {a : Chain Tx} :
    l.foldl (fun best ch => if best.length < ch.length then ch else best) a = a ∨
      l.foldl (fun best ch => if best.length < ch.length then ch else best) a ∈ l := by
  induction l generalizing a with
  | nil => exact Or.inl rfl
  | cons b l ih =>
      rw [List.foldl_cons]
      rcases ih (a := if a.length < b.length then b else a) with h | h
      · rw [h]
        split_ifs
        · exact Or.inr List.mem_cons_self
        · exact Or.inl rfl
      · exact Or.inr (List.mem_cons_of_mem b h)

/-- `fastconfirmsimple`'s chain is genesis, or carries more than `2n/3` distinct
    slot-`t` supporters in the view. -/
theorem fastConfirmSimple_fst_cases (V : View Node (Msg (Chain Tx) (QCert Node Tx)))
    (t : Nat) :
    (fastConfirmSimple n V t).1 = [] ∨
      2 * n ≤ 3 * (((votes V).filter (fun sm => msgSlot sm.msg = t ∧
        chainLe (fastConfirmSimple n V t).1 (msgChain sm.msg))).image
          SignedMsg.sender).card := by
  unfold fastConfirmSimple
  dsimp only
  split
  · exact Or.inl rfl
  · rcases foldl_longest_mem_or_init
        (l := ((candidates V []).filter (fun ch => 2 * n ≤
          3 * (((votes V).filter (fun sm => msgSlot sm.msg = t ∧
            chainLe ch (msgChain sm.msg))).image SignedMsg.sender).card)).toList)
        (a := ([] : Chain Tx)) with h | h
    · exact Or.inl h
    · right
      have hmem := Finset.mem_toList.mp h
      rw [Finset.mem_filter] at hmem
      exact hmem.2

/-! ### Counting: a quorum has an honest member -/

/-- More than `2n/3` distinct validators cannot all be corrupt when `3f < n`. -/
theorem exists_honest_sender {A : Finset Node} {r : Int} {fb : Nat}
    (hcb : S.CorruptionBounded fb) (hfn : 3 * fb < n) (hA : 2 * n ≤ 3 * A.card) :
    ∃ q ∈ A, q ∉ S.adv r := by
  by_contra hno
  have hsub : A ⊆ S.adv r := by
    intro q hq
    by_contra hq'
    exact hno ⟨q, hq, hq'⟩
  have h1 := Finset.card_le_card hsub
  have h2 := hcb r
  omega

/-! ### The propose-round half of Lemma 2, for Algorithm 2 -/

section Lemma2Propose

variable [Fintype Node]

/-- **Lemma 2's hypothesis, over the log**: every validator active in slot `t` has, by the
    end of `voting(t)`, sent a slot-`t` vote for a chain extending `ch` — with whatever
    filler that tick chose for the blank fields. -/
def ActiveVotesExtend2 (x : Exec Pr2 S) (t : Nat) (ch : Chain Tx) : Prop :=
  ∀ p ∈ Active Q S (t : Int),
    ∃ (i : Nat) (e : Chain Tx) (src tgt : Checkpoint (Chain Tx)),
    x[i].time = Q.slotLength * t + Q.delta ∧
    (⟨p, Msg.vote e src tgt t⟩ : SignedMsg Node (Msg (Chain Tx) (QCert Node Tx)))
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
    obtain ⟨iv, e, esrc, etgt, htiv, hsent, hext⟩ := hvotes p hpA
    have hhon : ∀ r : Time, r ≤ Q.slotLength * (t + 1) + Q.delta →
        p ∉ S.adv ((r : Int)) := by
      intro r hr had
      refine hpH (hmc _ _ ?_ had)
      rw [hvot1]
      exact_mod_cast hr
    -- delivery: sent at `voting(t)`, in the view by `propose(t+1)`
    have hview : (⟨p, Msg.vote e esrc etgt t⟩ :
        SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ x[ip][v].view := by
      refine hsyn iv ip v _ hsent ?_ hvAw
      rw [htiv, hip]
      omega
    have hsent_ip : (⟨p, Msg.vote e esrc etgt t⟩ :
        SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ x[ip].sent :=
      views_sound x ip v _ hview
    have hhon_ip : p ∉ S.adv ((x[ip].time : Int)) := by
      rw [hip]
      exact hhon _ (by omega)
    refine ⟨⟨p, Msg.vote e esrc etgt t⟩, ?_, rfl⟩
    -- build the filter membership inside out
    have hvv : (⟨p, Msg.vote e esrc etgt t⟩ :
        SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ votes (x[ip][v].view) := by
      simp only [votes, Finset.mem_filter]
      exact ⟨hview, trivial⟩
    have hfeq : (⟨p, Msg.vote e esrc etgt t⟩ :
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
    have hfexp : (⟨p, Msg.vote e esrc etgt t⟩ :
        SignedMsg Node (Msg (Chain Tx) (QCert Node Tx)))
        ∈ fil1Exp (filEq (x[ip][v].view)) (t + 1) := by
      simp only [fil1Exp, Finset.mem_filter]
      exact ⟨hfeq, rfl⟩
    have hflmd : (⟨p, Msg.vote e esrc etgt t⟩ :
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

/-! ### The vote-round half of Lemma 2, for Algorithm 2 -/

/-- Genesis is a prefix of everything. -/
theorem chainLe_nil (ch : Chain Tx) : chainLe [] ch := by
  rw [chainLe_iff_prefix]
  exact List.nil_prefix

/-- An honest official vote survives all three filters in whichever view it has reached:
    the equality expiry pins its slot, one-vote-per-slot kills equivocation, and nothing
    in an equality-filtered set is "later". View-parametric so the vote round can use it
    on the frozen and the live view alike. -/
theorem mem_votesFor_of_official {x : Exec Pr2 S} (hsync : SynchronizedClocks x)
    (hone : OneTickPerReading x) (hmc : S.MonotoneCorruption) (hmono : TimeMonotone x)
    {iw : Nat} {w q : Node} {e : Chain Tx} {src tgt : Checkpoint (Chain Tx)} {t : Nat}
    (hview : (⟨q, Msg.vote e src tgt t⟩ :
      SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ x[iw][w].view)
    (hhq : q ∉ S.adv ((x[iw].time : Int))) {ch : Chain Tx} (hext : chainLe ch e) :
    (⟨q, Msg.vote e src tgt t⟩ : SignedMsg Node (Msg (Chain Tx) (QCert Node Tx)))
      ∈ votesFor (x[iw][w].view) ch (t + 1) := by
  have hlog : (⟨q, Msg.vote e src tgt t⟩ :
      SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ x[iw].sent :=
    views_sound x iw w _ hview
  have hvv : (⟨q, Msg.vote e src tgt t⟩ :
      SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ votes (x[iw][w].view) := by
    simp only [votes, Finset.mem_filter]
    exact ⟨hview, trivial⟩
  have hfeq : (⟨q, Msg.vote e src tgt t⟩ :
      SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ filEq (x[iw][w].view) := by
    simp only [filEq, Finset.mem_filter]
    refine ⟨hvv, ?_⟩
    rintro ⟨sm', hsm', hsend', hslot', hne⟩
    have hsm'log : sm' ∈ x[iw].sent :=
      views_sound x iw w _ (by simp only [votes, Finset.mem_filter] at hsm'; exact hsm'.1)
    obtain ⟨e', src', tgt', s', hm'⟩ := exists_vote_of_mem_votes hsm'
    have e2 : msgSlot sm'.msg = s' := by rw [hm']; exact rfl
    rw [e2] at hslot'
    have hs' : s' = t := hslot'
    subst hs'
    have hh' : sm'.sender ∉ S.adv ((x[iw].time : Int)) := by
      rw [hsend']
      exact hhq
    have heq := honest_vote_unique2 hsync hone hmc hmono hlog hsm'log hhq hh'
      hsend' rfl hm'
    exact hne (by rw [heq])
  have hfexp : (⟨q, Msg.vote e src tgt t⟩ :
      SignedMsg Node (Msg (Chain Tx) (QCert Node Tx)))
      ∈ fil1Exp (filEq (x[iw][w].view)) (t + 1) := by
    simp only [fil1Exp, Finset.mem_filter]
    exact ⟨hfeq, rfl⟩
  have hflmd : (⟨q, Msg.vote e src tgt t⟩ :
      SignedMsg Node (Msg (Chain Tx) (QCert Node Tx)))
      ∈ filLmd (fil1Exp (filEq (x[iw][w].view)) (t + 1)) := by
    simp only [filLmd, Finset.mem_filter]
    refine ⟨hfexp, ?_⟩
    rintro ⟨sm', hsm', hsend', hlt⟩
    have hexp' : t + 1 = msgSlot sm'.msg + 1 := (Finset.mem_filter.mp hsm').2
    have hlt' : t < msgSlot sm'.msg := hlt
    omega
  simp only [votesFor, Finset.mem_filter]
  exact ⟨hflmd, hext⟩

section Lemma2Vote

variable [Fintype Node]

/-- **The containment, view-parametric**: any voter a view shows at slot `t+1` — as long
    as real time has not passed `voting(t+1)` — is corrupt by `voting(t+1)` or was active
    in slot `t`. With the equality expiry the visible slots are pinned to `t`, so this is
    delivery-schedule-independent. -/
theorem voters_containment {x : Exec Pr2 S} (hsync : SynchronizedClocks x)
    (hstepw : TimeStepwise x) (hdil : Diligent x) (hwpt : WakePrecedesTick x)
    (hmc : S.MonotoneCorruption) {iw : Nat} {w : Node} {t : Nat} (ht : 1 ≤ t)
    (hle : (x[iw].time : Int) ≤ Q.voting ((t : Int) + 1)) :
    voters (x[iw][w].view) (t + 1) ⊆
      (Active Q S (t : Int) \ S.adv (Q.voting ((t : Int) + 1))) ∪
        S.adv (Q.voting ((t : Int) + 1)) := by
  have hmono := hstepw.timeMonotone
  intro q hq
  simp only [voters, Finset.mem_image] at hq
  obtain ⟨smq, hsmq, rfl⟩ := hq
  simp only [fil1Exp, Finset.mem_filter] at hsmq
  obtain ⟨hsmqv, hexp'⟩ := hsmq
  by_cases hqa : smq.sender ∈ S.adv (Q.voting ((t : Int) + 1))
  · exact Finset.mem_union_right _ hqa
  refine Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨?_, hqa⟩)
  have hqlog : smq ∈ x[iw].sent :=
    views_sound x iw w _ (by simp only [votes, Finset.mem_filter] at hsmqv; exact hsmqv.1)
  obtain ⟨e', src', tgt', s', hm'⟩ := exists_vote_of_mem_votes hsmqv
  have hh' : smq.sender ∉ S.adv ((x[iw].time : Int)) := fun had => hqa (hmc _ _ hle had)
  have e2 : msgSlot smq.msg = s' := by rw [hm']; exact rfl
  rw [e2] at hexp'
  have hs' : s' = t := by omega
  subst hs'
  exact mem_active_of_honest_vote2 hsync hstepw hdil hwpt hmc ht hqlog hh' hm'

set_option maxHeartbeats 2000000 in
/-- **The vote-round half of Lemma 2, for Algorithm 2**: at the vote tick of a validator
    active in slot `t+1`, the fork-choice over its frozen view, live view, and processed
    frozen chain extends `ch`. The paper's `MFC^{vote(t+1)}_i ⪰ ch`.

    The assembly: the merge tick at `4Δt+3Δ` exists (`Diligent` inside the activity
    window) and froze that moment's view and fast-confirmed chain; no other reading in
    `[merge(t), voting(t+1)]` can write them (`phase_pins_reading` + `OneTickPerReading`);
    `Synchrony` puts every slot-`t` official vote in both the frozen and the live view, so
    Constraint (1) gives the majority; and the frozen chain is comparable with `ch` on
    both of its write paths — `fastconfirmsimple`'s quorum and `ValidProposal2`'s
    view-checked certificate each contain an honest slot-`t` voter whose unique vote
    extends both chains. -/
theorem le_mfc_at_vote2 {x : Exec Pr2 S}
    (hsync : SynchronizedClocks x) (hstepw : TimeStepwise x) (hdil : Diligent x)
    (hwpt : WakePrecedesTick x) (hone : OneTickPerReading x) (hmc : S.MonotoneCorruption)
    (hsyn : Synchrony 0 Q.delta x) (hslp : Sleepiness Q S)
    (hcb : S.CorruptionBounded Q.f) (hfn : 3 * Q.f < n) (hgst : Q.gst = 0)
    {t : Nat} (ht : 1 ≤ t) {ch : Chain Tx} (hvotes : ActiveVotesExtend2 x t ch)
    {p : Node} (hp : p ∈ Active Q S ((t : Int) + 1))
    {j : Nat} (hj : x.lbl j = .tick p (Q.slotLength * (t + 1) + Q.delta)) :
    chainLe ch
      (mfc (processProposals2 n (x[j][p].view) (t + 1) (x[j][p].st)).vFrozen
        (x[j][p].view)
        (processProposals2 n (x[j][p].view) (t + 1) (x[j][p].st)).chFrozen (t + 1)) := by
  have hmono := hstepw.timeMonotone
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  have htj : x[j].time = Q.slotLength * (t + 1) + Q.delta := tick_reading hsync hj
  have hexp : Q.slotLength * (t + 1) = Q.slotLength * t + Q.slotLength := Nat.mul_succ ..
  have hvot1 : Q.voting ((t : Int) + 1)
      = ((Q.slotLength * (t + 1) + Q.delta : Nat) : Int) := by
    unfold Params.voting
    push_cast
    omega
  -- awake through the whole window `[4Δt+2Δ, 4Δt+5Δ]`
  have hawake : ∀ r : Time, Q.slotLength * t + 2 * Q.delta ≤ r →
      r ≤ Q.slotLength * (t + 1) + Q.delta → p ∈ S.awake ((r : Int)) := by
    intro r h1 h2
    refine mem_awakeThroughout.mp hp _ ?_ ?_ <;> rw [hvot1] <;> omega
  -- the merge tick `im`
  have hmt : Q.slotLength * t + 3 * Q.delta ≤ x[j].time := by
    rw [htj]
    omega
  obtain ⟨i₀, hi₀j, hti₀⟩ := exists_time_eq hstepw hmt
  have hAw0 : x.Awake i₀ p := by
    show p ∈ S.awake ((x[i₀].time : Int))
    rw [hti₀]
    exact hawake _ (by omega) (by omega)
  obtain ⟨im, htim, hlblm⟩ := hdil (Q.slotLength * t + 3 * Q.delta) p ⟨i₀, hti₀, hAw0⟩
  have himj : im < j := by
    rcases Nat.lt_or_ge im j with h | h
    · exact h
    · exfalso
      have := time_le_of_le hmono h
      rw [htj, htim] at this
      omega
  -- the merge tick froze the view and the fast-confirmed chain
  have hmstate : x[im + 1][p].st = { x[im][p].st with vFrozen := x[im][p].view, chFrozen := (fastConfirmSimple n (x[im][p].view) t).1 } := by
    obtain ⟨dm, hst, -⟩ := tick_effect hlblm
    rw [hst, handler2_merge (merge_reading_mod Q t), merge_reading_div Q t]
  -- and nothing between `im+1` and `j` writes them
  have hpers : ∀ m, im + 1 ≤ m → m ≤ j →
      x[m][p].st.vFrozen = x[im + 1][p].st.vFrozen ∧
        x[m][p].st.chFrozen = x[im + 1][p].st.chFrozen := by
    intro m
    induction m with
    | zero => omega
    | succ m ih =>
        intro h1 h2
        rcases Nat.eq_or_lt_of_le h1 with heq | hlt
        · rw [← heq]
          exact ⟨rfl, rfl⟩
        · have hprev := ih (by omega) (by omega)
          have hcond : ∀ tr : Time, x.lbl m = .tick p tr →
              tr % Q.slotLength ≠ Q.delta ∧ tr % Q.slotLength ≠ 3 * Q.delta := by
            intro tr hltr
            have htr : x[m].time = tr := tick_reading hsync hltr
            have hlo2 : Q.slotLength * t + 3 * Q.delta ≤ tr := by
              rw [← htr]
              calc Q.slotLength * t + 3 * Q.delta = x[im].time := htim.symm
                _ ≤ x[m].time := time_le_of_le hmono (by omega)
            have hhi2 : tr ≤ Q.slotLength * (t + 1) + Q.delta := by
              rw [← htr, ← htj]
              exact time_le_of_le hmono (by omega)
            have hpin := phase_pins_reading Q hlo2 hhi2
            constructor
            · intro hphase
              rw [hpin.2 hphase] at hltr
              have := hone m j p _ hltr hj
              omega
            · intro hphase
              rw [hpin.1 hphase] at hltr
              have := hone m im p _ hltr hlblm
              omega
          have hstep := frozen_step2 hcond
          exact ⟨hstep.1.trans hprev.1, hstep.2.trans hprev.2⟩
  have hsj : x[j][p].st.vFrozen = x[im][p].view ∧
      x[j][p].st.chFrozen = (fastConfirmSimple n (x[im][p].view) t).1 := by
    have h := hpers j (by omega) (le_refl j)
    rw [hmstate] at h
    exact ⟨h.1, h.2⟩
  -- delivery of the official slot-`t` votes into both views
  have hAwm : x.Awake im p := by
    show p ∈ S.awake ((x[im].time : Int))
    rw [htim]
    exact hawake _ (by omega) (by omega)
  have hAwj : x.Awake j p := by
    show p ∈ S.awake ((x[j].time : Int))
    rw [htj]
    exact hawake _ (by omega) (by omega)
  have hdeliver : ∀ w ∈ Active Q S (t : Int) \ S.adv (Q.voting ((t : Int) + 1)),
      ∃ smp ∈ votesFor (x[im][p].view) ch (t + 1) ∩ votesFor (x[j][p].view) ch (t + 1),
        smp.sender = w := by
    intro w hw
    obtain ⟨hwA, hwH⟩ := Finset.mem_sdiff.mp hw
    obtain ⟨iv, e, esrc, etgt, htiv, hsent, hext⟩ := hvotes w hwA
    have hhon : ∀ i2 : Nat, (x[i2].time : Int) ≤ Q.voting ((t : Int) + 1) →
        w ∉ S.adv ((x[i2].time : Int)) :=
      fun i2 hle2 had => hwH (hmc _ _ hle2 had)
    have hviewm : (⟨w, Msg.vote e esrc etgt t⟩ :
        SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ x[im][p].view := by
      refine hsyn iv im p _ hsent ?_ hAwm
      rw [htiv, htim]
      omega
    have hviewj : (⟨w, Msg.vote e esrc etgt t⟩ :
        SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ x[j][p].view := by
      refine hsyn iv j p _ hsent ?_ hAwj
      rw [htiv, htj]
      omega
    have hhonm : w ∉ S.adv ((x[im].time : Int)) := by
      refine hhon im ?_
      rw [htim, hvot1]
      exact_mod_cast (by omega : Q.slotLength * t + 3 * Q.delta ≤
        Q.slotLength * (t + 1) + Q.delta)
    have hhonj : w ∉ S.adv ((x[j].time : Int)) := by
      refine hhon j ?_
      rw [htj, hvot1]
    have hm1 := mem_votesFor_of_official hsync hone hmc hmono hviewm hhonm hext
    have hm2 := mem_votesFor_of_official hsync hone hmc hmono hviewj hhonj hext
    exact ⟨⟨w, Msg.vote e esrc etgt t⟩, Finset.mem_inter.mpr ⟨hm1, hm2⟩, rfl⟩
  -- Constraint (1) turns the containment into the majority
  have himg : Active Q S (t : Int) \ S.adv (Q.voting ((t : Int) + 1)) ⊆
      (votesFor (x[im][p].view) ch (t + 1) ∩ votesFor (x[j][p].view) ch (t + 1)).image
        SignedMsg.sender := by
    intro w hw
    obtain ⟨smp, hsmp, hsend⟩ := hdeliver w hw
    exact Finset.mem_image.mpr ⟨smp, hsmp, hsend⟩
  have hsub := voters_containment (iw := j) (w := p) hsync hstepw hdil hwpt hmc ht
    (le_of_eq (by rw [htj, hvot1]))
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
  have hmaj : Majority (x[im][p].view) (x[j][p].view) (t + 1) ch := by
    show (voters (x[j][p].view) (t + 1)).card < 2 * _
    omega
  set s' := processProposals2 n (x[j][p].view) (t + 1) (x[j][p].st) with hs'def
  have hcomp : chainLe ch s'.chFrozen ∨ chainLe s'.chFrozen ch := by
    -- comparability of a quorum-supported chain in a view whose time is `≤ voting(t+1)`
    have hsupported : ∀ (iw : Nat) (chq : Chain Tx),
        (x[iw].time : Int) ≤ Q.voting ((t : Int) + 1) →
        2 * n ≤ 3 * (((votes (x[iw][p].view)).filter (fun sm => msgSlot sm.msg = t ∧
          chainLe chq (msgChain sm.msg))).image SignedMsg.sender).card →
        chainLe ch chq ∨ chainLe chq ch := by
      intro iw chq hlew hq
      obtain ⟨q0, hq0mem, hq0hon⟩ :=
        exists_honest_sender (r := ((x[iw].time : Int))) hcb hfn hq
      obtain ⟨smq, hsmq, hsendq⟩ := Finset.mem_image.mp hq0mem
      rw [Finset.mem_filter] at hsmq
      obtain ⟨hsmqv, hslotq, hchq⟩ := hsmq
      have hqlog : smq ∈ x[iw].sent :=
        views_sound x iw p _
          (by simp only [votes, Finset.mem_filter] at hsmqv; exact hsmqv.1)
      obtain ⟨e', src', tgt', sq, hmq⟩ := exists_vote_of_mem_votes hsmqv
      have hsq : sq = t := by
        have e2 : msgSlot smq.msg = sq := by rw [hmq]; exact rfl
        rw [e2] at hslotq
        omega
      subst hsq
      have hqhon : smq.sender ∉ S.adv ((x[iw].time : Int)) := by
        rw [hsendq]
        exact hq0hon
      have hact := mem_active_of_honest_vote2 hsync hstepw hdil hwpt hmc ht hqlog
        hqhon hmq
      obtain ⟨iv, e0, src0, tgt0, htiv, hsent0, hext0⟩ := hvotes smq.sender hact
      have hhon_iv : smq.sender ∉ S.adv ((x[iv].time : Int)) := by
        intro had
        refine hqhon (hmc _ _ ?_ had)
        have h2 : x[iv].time ≤ x[iw].time := by
          -- both bounded through `voting(t+1)`? No: directly, `voting(t) ≤ time iw` is
          -- not known; go through the vote's own provenance instead
          have hb := voting_le_of_vote_mem2 hsync hmc hmono hqlog hqhon hmq
          rw [htiv]
          exact hb
        exact_mod_cast h2
      have huniq := honest_vote_unique2 hsync hone hmc hmono hsent0 hqlog hhon_iv
        hqhon rfl rfl hmq
      have hchains : msgChain smq.msg = e0 := by
        rw [huniq]
        exact rfl
      rw [hchains] at hchq
      exact comparable_of_common_extension hext0 hchq
    rcases processProposals2_chFrozen (n := n) (x[j][p].view) (t + 1) (x[j][p].st)
      with h | h
    · -- untouched: the merge-round fast confirmation
      rw [← hs'def] at h
      rw [h, hsj.2]
      rcases fastConfirmSimple_fst_cases (n := n) (x[im][p].view) t with h0 | hq
      · rw [h0]
        exact Or.inr (chainLe_nil ch)
      · refine hsupported im _ ?_ hq
        rw [htim, hvot1]
        exact_mod_cast (by omega : Q.slotLength * t + 3 * Q.delta ≤
          Q.slotLength * (t + 1) + Q.delta)
    · -- overwritten by a certificate-checked proposal
      rw [← hs'def] at h
      obtain ⟨sm, hsmV, ⟨chp, qc, ck, hsmmsg⟩, hvp⟩ := h
      obtain ⟨sd, m0⟩ := sm
      have hm0 : m0 = Msg.propose chp s'.chFrozen qc ck (t + 1) := hsmmsg
      subst hm0
      have hvp' : proposedAt chp = (t + 1) ∧ chainLe s'.chFrozen chp ∧
          (s'.chFrozen = [] ∨ ∃ cert : QCert Node Tx, qc = some cert ∧
            2 * n ≤ 3 * (cert.image Prod.fst).card ∧
            ∀ e ∈ cert, chainLe s'.chFrozen e.2.1 ∧ e.2.2 = (t + 1) - 1 ∧
              ∃ src tgt : Checkpoint (Chain Tx),
                (⟨e.1, Msg.vote e.2.1 src tgt e.2.2⟩ :
                  SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ x[j][p].view) := hvp
      rcases hvp'.2.2 with hgen0 | ⟨cert, hqc, hcard, hcert⟩
      · rw [hgen0]
        exact Or.inr (chainLe_nil ch)
      · obtain ⟨q0, hq0mem, hq0hon⟩ :=
          exists_honest_sender (r := ((x[j].time : Int))) hcb hfn hcard
        obtain ⟨entry, hentry, hfst⟩ := Finset.mem_image.mp hq0mem
        obtain ⟨hchC, hslotE, hinV⟩ := hcert entry hentry
        have hslotE' : entry.2.2 = t := by omega
        rw [hslotE'] at hinV
        obtain ⟨esrc, etgt, hinV⟩ := hinV
        have hlogE : (⟨entry.1, Msg.vote entry.2.1 esrc etgt t⟩ :
            SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ x[j].sent :=
          views_sound x j p _ hinV
        have hhonE : entry.1 ∉ S.adv ((x[j].time : Int)) := by
          rw [hfst]
          exact hq0hon
        have hactE := mem_active_of_honest_vote2 hsync hstepw hdil hwpt hmc ht hlogE
          hhonE rfl
        obtain ⟨iv, e0, src0, tgt0, htiv, hsent0, hext0⟩ := hvotes entry.1 hactE
        have hhon_iv : entry.1 ∉ S.adv ((x[iv].time : Int)) := by
          intro had
          refine hhonE (hmc _ _ ?_ had)
          have hb := voting_le_of_vote_mem2 hsync hmc hmono hlogE hhonE rfl
          have h2 : x[iv].time ≤ x[j].time := by
            rw [htiv]
            exact hb
          exact_mod_cast h2
        have huniq := honest_vote_unique2 hsync hone hmc hmono hsent0 hlogE hhon_iv
          hhonE rfl rfl rfl
        have hE : entry.2.1 = e0 := by
          have := congrArg SignedMsg.msg huniq
          injection this with h1 h2 h3 h4
        rw [hE] at hchC
        exact comparable_of_common_extension hext0 hchC
  rcases hcomp with hle | hge
  · exact chainLe_trans hle (base_le_mfc _ _ _ _)
  · have hvf : s'.vFrozen = x[im][p].view := by
      rw [hs'def, processProposals2_vFrozen]
      exact hsj.1
    rw [hvf]
    exact le_mfc_of_majority _ _ _ _ ch hge hmaj

end Lemma2Vote

end Majorum
