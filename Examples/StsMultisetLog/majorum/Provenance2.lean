import Examples.StsMultisetLog.majorum.Provenance
import Examples.StsMultisetLog.majorum.Spec.Algorithm2

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

attribute [local instance] Set.monad

namespace Majorum

open the framework's flat multiset-log flavour

variable {Node Tx : Type} [DecidableEq Node] [DecidableEq Tx]
  {Q : Params} {S : Schedule Node} {n kappa : Nat} {pool : Nat → Tx} {proposer : Nat → Node}
  {dot : Checkpoint (Chain Tx)}

local notation "Pr2" => protocol2 Q n kappa pool proposer

/-! ### The deterministic core, and the inversion through it -/

/-- The deterministic core of `handler2`: Algorithm 2's four phase actions with the
    blank filler given. The proof layer works over this — `mem_handler2_iff` recovers it
    from the protocol's `Set`-valued handler below.

    Differences from Algorithm 5's handler, all of them the *absence* of finality: no
    `gjFrozen`, votes carry the placeholder `dot` in the fin-vote fields, the propose
    message carries it for the checkpoint, fast confirmation is `fastconfirmsimple` unwrapped (line
    28 assigns whenever a quorum exists, with no greatest-justified floor), and the one
    output chain is `chi`. The joining gates are the same. -/
noncomputable def handler2Core (Q : Params) (n kappa : Nat) (pool : Nat → Tx)
    (proposer : Nat → Node) (dot : Checkpoint (Chain Tx)) (p : Node) (r : Time)
    (V : View Node (Msg (Chain Tx) (QCert Node Tx))) (s : NodeState2 Node Tx) :
    NodeStepResult (NodeState2 Node Tx) (Msg (Chain Tx) (QCert Node Tx)) :=
  let slot : Nat := r / Q.slotLength
  let phase : Nat := r % Q.slotLength
  if phase = 0 then
    -- Propose, lines 14–19 — only once active
    if p = proposer slot ∧ s.activeAt ≤ r then
      let cq := fastConfirmSimple n V (slot - 1)
      let chMFC := mfc V V cq.1 slot
      let chp := extend pool chMFC slot
      { state := s, send := {.propose chp cq.1 cq.2 dot slot} }
    else { state := s, send := 0 }
  else if phase = Q.delta then
    -- Vote, lines 20–25, after the lines 33–36 proposal processing
    let s' := processProposals2 n proposer V slot s
    let chMFC := mfc s'.vFrozen V s'.chFrozen slot
    -- line 22: `Ch_i ← max({ch ∈ {Ch_i, (chMFC)⌈κ} : ch ⪯ chMFC})` — only once active
    let chi :=
      if s.activeAt ≤ r then
        [s'.chi, kappaPrefix kappa slot chMFC].foldl
          (fun acc c => if chainLe c chMFC then (if chainLe acc c then c else acc) else acc)
          s'.chi
      else s'.chi
    let proposedNow : Option (Chain Tx) :=
      V.toList.findSome? (fun sm => match sm.msg with
        | .propose chp _ _ _ t' =>
            if sm.sender == proposer slot && t' == slot && proposedAt chp == slot &&
                slotsIncreasing chp && chainLe chMFC chp then some chp
            else none
        | .vote .. => none)
    let ch := proposedNow.getD chMFC
    { state := { s' with chi := chi },
      -- a joining validator executes silently
      send := if s.activeAt ≤ r then {.vote ch dot dot slot} else 0 }
  else if phase = 2 * Q.delta then
    -- Fast Confirm, lines 26–29, with Algorithm 5's line-23 guard (see `handler2`)
    let fq := fastConfirmSimple n V slot
    let sF :=
      if fq.2.isSome then
        { s with chi := if chainLe fq.1 s.chi then s.chi else fq.1 }
      else s
    { state := sF, send := 0 }
  else if phase = 3 * Q.delta then
    -- Merge, lines 30–32
    { state := { s with vFrozen := V, chFrozen := (fastConfirmSimple n V slot).1 }, send := 0 }
  else
    { state := s, send := 0 }

/-- Membership in a nondeterministic assignment followed by a deterministic
    continuation — Event-B's `x :∈ S; y := f(x)`, inverted. -/
theorem mem_assign {α β : Type} {f : α → β} {res : β} :
    (res ∈ do { let x ← (Set.univ : Set α); pure (f x) }) ↔ ∃ x, res = f x := by
  rw [Set.bind_def]
  simp [Set.pure_def, eq_comm]

/-- Membership in a deterministic branch, phrased with the vacuous choice the
    deterministic core still binds. -/
theorem mem_pure_exists {α β : Type} [Nonempty α] {b res : β} :
    (res ∈ (pure b : Set β)) ↔ ∃ _ : α, res = b := by
  simp [Set.pure_def]

/-- **The inversion lemma**: membership in the handler is exactly "the deterministic
    core, for some filler". The one bridge the proof layer needs. -/
theorem mem_handler2_iff {Q : Params} {n kappa : Nat} {pool : Nat → Tx}
    {proposer : Nat → Node} {p : Node} {r : Time}
    {V : View Node (Msg (Chain Tx) (QCert Node Tx))} {s : NodeState2 Node Tx}
    {res : NodeStepResult (NodeState2 Node Tx) (Msg (Chain Tx) (QCert Node Tx))} :
    res ∈ handler2 Q n kappa pool proposer p r V s ↔
      ∃ dot, res = handler2Core Q n kappa pool proposer dot p r V s := by
  haveI hne : Nonempty (Checkpoint (Chain Tx)) := ⟨⟨[], 0⟩⟩
  simp only [handler2, handler2Core]
  split_ifs <;>
    first
      | exact mem_assign
      | exact mem_pure_exists (α := Checkpoint (Chain Tx))

/-! ### Reducing `protocol2`'s step, projection-precisely

Same rationale as `protocol_step_tick` and friends: `simp only [protocol2]` would unfold
the definition inside implicit type arguments and poison later goals. -/

theorem protocol2_step_tick {p : Node} {r : Time}
    {V : View Node (Msg (Chain Tx) (QCert Node Tx))} {s : NodeState2 Node Tx} {res} :
    (protocol2 (Node := Node) Q n kappa pool proposer).step p r V s .tick res ↔
      res ∈ handler2 Q n kappa pool proposer p r V s := Iff.rfl

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
    (h : m ∈ (handler2Core Q n kappa pool proposer dot p r V s).send) :
    s.activeAt ≤ r ∧
      ((∃ chp chC qc, m = .propose chp chC qc dot (r / Q.slotLength) ∧
          r % Q.slotLength = 0) ∨
        (∃ ch, m = .vote ch dot dot (r / Q.slotLength) ∧
          r % Q.slotLength = Q.delta)) := by
  simp only [handler2Core, apply_ite NodeStepResult.send] at h
  split_ifs at h <;> simp at h <;> subst h <;>
    first
      | exact ⟨‹p = proposer (r / Q.slotLength) ∧ s.activeAt ≤ r›.2,
          Or.inl ⟨_, _, _, rfl, ‹r % Q.slotLength = 0›⟩⟩
      | exact ⟨‹s.activeAt ≤ r›, Or.inr ⟨_, rfl, ‹r % Q.slotLength = Q.delta›⟩⟩

/-- `handler2` sends at most one message per step. -/
theorem handler2_send_subsingleton {p : Node} {r : Time}
    {V : View Node (Msg (Chain Tx) (QCert Node Tx))} {s : NodeState2 Node Tx}
    {m m' : Msg (Chain Tx) (QCert Node Tx)}
    (h : m ∈ (handler2Core Q n kappa pool proposer dot p r V s).send)
    (h' : m' ∈ (handler2Core Q n kappa pool proposer dot p r V s).send) : m = m' := by
  simp only [handler2Core, apply_ite NodeStepResult.send] at h h'
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
        sm.msg ∈ (handler2Core Q n kappa pool proposer dot sm.sender t
          x[k][sm.sender].view x[k][sm.sender].st).send) ∨
      sm.sender ∈ S.adv ((x[k].time : Int)) := by
  have hstep : Step Pr2 S (x.lbl k) x[k] x[k + 1] := x.step k
  refine hstep.elimR (motive := fun a c c' => sm ∈ c'.sent - c.sent →
      (∃ (t : Time) (dot : Checkpoint (Chain Tx)), a = Action.tick sm.sender t ∧
          sm.sender ∈ S.awake ((c.time : Int)) ∧ c'.time = c.time ∧
          c'[sm.sender].clock = t ∧
          sm.msg ∈ (handler2Core Q n kappa pool proposer dot sm.sender t
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
    rw [protocol2_step_tick, mem_handler2_iff] at hres
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

/-- The propose phase's send, in full: only the slot's proposer, once active, and the
    message's components are this tick's fork-choice over its own view. -/
theorem handler2_propose_send {p : Node} {r : Time}
    {V : View Node (Msg (Chain Tx) (QCert Node Tx))} {s : NodeState2 Node Tx}
    {m : Msg (Chain Tx) (QCert Node Tx)}
    (hmod : r % Q.slotLength = 0)
    (h : m ∈ (handler2Core Q n kappa pool proposer dot p r V s).send) :
    p = proposer (r / Q.slotLength) ∧ s.activeAt ≤ r ∧
      m = .propose
        (extend pool (mfc V V (fastConfirmSimple n V (r / Q.slotLength - 1)).1
          (r / Q.slotLength)) (r / Q.slotLength))
        (fastConfirmSimple n V (r / Q.slotLength - 1)).1
        (fastConfirmSimple n V (r / Q.slotLength - 1)).2 dot (r / Q.slotLength) := by
  have hδ := Q.deltaPos
  simp only [handler2Core, apply_ite NodeStepResult.send] at h
  split_ifs at h <;>
    first
      | omega
      | (simp only [Multiset.mem_singleton] at h
         exact ⟨‹p = proposer (r / Q.slotLength) ∧ s.activeAt ≤ r›.1,
           ‹p = proposer (r / Q.slotLength) ∧ s.activeAt ≤ r›.2, h⟩)
      | simp at h

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

/-- **An honest proposal pins down its own history**: a slot-`s` propose in the log,
    whose sender is still honest, came from the slot proposer's tick at reading
    `propose(s) = 4Δs`, at real time `4Δs`, and its chain is that tick's fork-choice over
    the proposer's own view, extended by one block. -/
theorem propose_provenance2 {x : Exec Pr2 S} (hsync : SynchronizedClocks x)
    (hmc : S.MonotoneCorruption) (hmono : TimeMonotone x) {i : Nat}
    {sm : SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))} {chp chC : Chain Tx}
    {qc : Option (QCert Node Tx)} {ck : Checkpoint (Chain Tx)} {s : Nat}
    (hmem : sm ∈ x[i].sent) (hhon : sm.sender ∉ S.adv ((x[i].time : Int)))
    (hmsg : sm.msg = .propose chp chC qc ck s) :
    sm.sender = proposer s ∧
    ∃ k, k < i ∧ x.lbl k = .tick sm.sender (Q.slotLength * s) ∧
      x[k].time = Q.slotLength * s ∧
      sm ∈ x[k + 1].sent - x[k].sent ∧
      chp = extend pool (mfc (x[k][sm.sender].view) (x[k][sm.sender].view)
        (fastConfirmSimple n (x[k][sm.sender].view) (s - 1)).1 s) s ∧
      chC = (fastConfirmSimple n (x[k][sm.sender].view) (s - 1)).1 ∧
      qc = (fastConfirmSimple n (x[k][sm.sender].view) (s - 1)).2 := by
  have hδ := Q.deltaPos
  have hsl0 : 0 < Q.slotLength := by
    have : Q.slotLength = 4 * Q.delta := rfl
    omega
  obtain ⟨k, hki, hem⟩ := emitted_of_mem_sent hmem
  have hhonk : sm.sender ∉ S.adv ((x[k].time : Int)) := fun hadv =>
    hhon (hmc _ _ (by exact_mod_cast time_le_of_le hmono (Nat.le_of_lt hki)) hadv)
  rcases emitted_step2 hem with ⟨t, dt, hlbl, hawake, htime, hclock, hsend⟩ | hadv
  · obtain ⟨hactive, hshape⟩ := mem_handler2_send hsend
    have hmods : t % Q.slotLength = 0 ∧ t / Q.slotLength = s := by
      rcases hshape with ⟨chp', chC', qc', heq, hmod0⟩ | ⟨ch', heq, -⟩
      · rw [hmsg] at heq
        injection heq with h1 h2 h3 h4 h5
        exact ⟨hmod0, h5.symm⟩
      · rw [hmsg] at heq
        cases heq
    have ht : t = Q.slotLength * s := by
      have hdm := Nat.div_add_mod t Q.slotLength
      rw [hmods.1, hmods.2] at hdm
      omega
    subst ht
    have hdiv : Q.slotLength * s / Q.slotLength = s := by
      rw [Nat.mul_div_cancel_left _ hsl0]
    obtain ⟨hprop, -, hmeq⟩ := handler2_propose_send hmods.1 hsend
    rw [hmsg, hdiv] at hmeq
    injection hmeq with h1 h2 h3 h4 h5
    rw [hdiv] at hprop
    have htimek : x[k].time = Q.slotLength * s := by
      have hawake' : x.Awake (k + 1) sm.sender := by
        show sm.sender ∈ S.awake ((x[k + 1].time : Int))
        rw [htime]
        exact hawake
      have := hsync (k + 1) sm.sender hawake'
      rw [hclock] at this
      omega
    exact ⟨hprop, k, hki, hlbl, htimek, hem, h1, h2, h3⟩
  · exact absurd hadv hhonk

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
  rw [protocol2_step_tick, mem_handler2_iff] at hres
  obtain ⟨dt, rfl⟩ := hres
  rw [hpost, ← setClock_sent p t x[k], applyNodeStepResult_sent_sub] at h h'
  obtain ⟨m, hm, rfl⟩ := Multiset.mem_map.mp h
  obtain ⟨m', hm', heq'⟩ := Multiset.mem_map.mp h'
  rw [← heq', handler2_send_subsingleton hm hm']

/-- A tick's log contribution is one of its handler sends, signed by the ticker. -/
theorem tick_delta_send {x : Exec Pr2 S} {k : Nat} {p : Node} {t : Time}
    (hlbl : x.lbl k = .tick p t)
    {sm : SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))}
    (h : sm ∈ x[k + 1].sent - x[k].sent) :
    ∃ dt : Checkpoint (Chain Tx), sm.sender = p ∧
      sm.msg ∈ (handler2Core Q n kappa pool proposer dt p t
        x[k][p].view x[k][p].st).send := by
  have hstep : Step Pr2 S (x.lbl k) x[k] x[k + 1] := x.step k
  rw [hlbl] at hstep
  obtain ⟨hen, heff⟩ := hstep
  simp only [spec] at heff
  rw [nodeStep_iff_exists] at heff
  obtain ⟨res, hres, hpost⟩ := heff
  rw [protocol2_step_tick, mem_handler2_iff] at hres
  obtain ⟨dt, rfl⟩ := hres
  rw [hpost, ← setClock_sent p t x[k], applyNodeStepResult_sent_sub] at h
  obtain ⟨m, hm, rfl⟩ := Multiset.mem_map.mp h
  exact ⟨dt, rfl, by simpa [setClock_getElem] using hm⟩

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
    (processProposals2 n proposer V t s).activeAt = s.activeAt := by
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
    (handler2Core Q n kappa pool proposer dot p r V s).state.activeAt = s.activeAt := by
  simp only [handler2Core, apply_ite NodeStepResult.state]
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
    rw [protocol2_step_tick, mem_handler2_iff] at hres
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

/-- **An open joining check at a vote tick means activity**: a validator ticking at
    `voting(t)` with `activeAt ≤ voting(t)` is in `Active t` — it is awake at the tick,
    and any sleep inside the activity window would have produced a wake event recent
    enough to push `activeAt` past `voting(t)` (`voting_lt_activationRound`). Extracted
    from `mem_active_of_honest_vote2`, which now derives the tick by provenance and
    calls this. -/
theorem active_of_open_join [Fintype Node] {x : Exec Pr2 S}
    (hsync : SynchronizedClocks x) (hstepw : TimeStepwise x) (hdil : Diligent x)
    (hwpt : WakePrecedesTick x) {p : Node} {t : Nat} (ht : 1 ≤ t)
    {j : Nat} (hlbl : x.lbl j = .tick p (Q.slotLength * t + Q.delta))
    (htj : x[j].time = Q.slotLength * t + Q.delta)
    (hgate : x[j][p].st.activeAt ≤ Q.slotLength * t + Q.delta) :
    p ∈ Active Q S (t : Int) := by
  have hmono := hstepw.timeMonotone
  have hstepj0 : Step Pr2 S (x.lbl j) x[j] x[j + 1] := x.step j
  rw [hlbl] at hstepj0
  have hawk : p ∈ S.awake ((x[j].time : Int)) := by
    have := hstepj0.1
    simp only [spec] at this
    exact this
  -- `voting(t)` as an integer
  have hvot : Q.voting (t : Int) = ((Q.slotLength * t + Q.delta : Nat) : Int) := by
    unfold Params.voting
    push_cast
    omega
  show p ∈ S.awakeThroughout (Q.voting (t : Int) - 3 * (Q.delta : Int))
    (Q.voting (t : Int))
  by_cases hbad : ∃ r ∈ Finset.Icc (Q.voting (t : Int) - 3 * (Q.delta : Int))
      (Q.voting (t : Int)), p ∉ S.awake r
  · -- a round in the window at which the sender was asleep: derive the contradiction
    exfalso
    obtain ⟨r₀, hr₀Icc, hr₀⟩ := hbad
    set bad : Finset Int := (Finset.Icc (Q.voting (t : Int) - 3 * (Q.delta : Int))
        (Q.voting (t : Int))).filter (fun r => p ∉ S.awake r) with hbaddef
    have hbadne : bad.Nonempty := ⟨r₀, Finset.mem_filter.mpr ⟨hr₀Icc, hr₀⟩⟩
    obtain ⟨hwIcc, hwna⟩ := Finset.mem_filter.mp (Finset.max'_mem bad hbadne)
    obtain ⟨hwlo, hwhi⟩ := Finset.mem_Icc.mp hwIcc
    -- the sender is awake at the top of the window, so the bad round is strictly below
    have hawktop : p ∈ S.awake (Q.voting (t : Int)) := by
      rw [hvot]
      rw [htj] at hawk
      exact_mod_cast hawk
    have hwlt : bad.max' hbadne < Q.voting (t : Int) :=
      lt_of_le_of_ne hwhi (fun h => hwna (by rw [h]; exact hawktop))
    -- awake everywhere strictly above the bad round, within the window
    have hawakeW : ∀ r : Int, bad.max' hbadne < r → r ≤ Q.voting (t : Int) →
        p ∈ S.awake r := by
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
    have hwake : ∃ k, k < j ∧ x.lbl k = .wake p ∧ x[k].time = w := by
      rcases Nat.lt_or_ge w (Q.slotLength * t + Q.delta) with hnlt | hnge
      · -- the transition is strictly below the vote round: Diligent ticks it there
        obtain ⟨i₀, hi₀j, hti₀⟩ := exists_time_eq hstepw
          (show w ≤ x[j].time by rw [htj]; omega)
        have hAw : x.Awake i₀ p := by
          show p ∈ S.awake ((x[i₀].time : Int))
          rw [hti₀, hw]
          exact hawakeW _ (by omega) (by omega)
        obtain ⟨i₁, hti₁, hlbl₁⟩ := hdil w p ⟨i₀, hti₀, hAw⟩
        have hnaw : p ∉ S.awake ((x[i₁].time : Int) - 1) := by
          rw [hti₁, hw]
          simpa using hwna
        obtain ⟨k, hki₁, hwk, htk'⟩ := hwpt i₁ p w hlbl₁ hnaw
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
        have hnaw : p ∉ S.awake ((x[j].time : Int) - 1) := by
          rw [htj]
          have hδ : ((Q.slotLength * t + Q.delta : Nat) : Int) - 1 = bad.max' hbadne := by
            rw [← hvot]
            omega
          rw [hδ]
          exact hwna
        obtain ⟨k, hkj, hwk, htk'⟩ := hwpt j p _ hlbl hnaw
        refine ⟨k, hkj, hwk, ?_⟩
        rw [htk', htj]
        omega
    obtain ⟨k, hkj, hwk, htk⟩ := hwake
    -- the wake wrote the true activation round, and nothing lowered it since
    have hbase : x[k + 1][p].st.activeAt = activationRound Q w := by
      have h := wake_sets_activeAt2 hsync hwk
      rw [htk] at h
      exact h
    have hpers : ∀ m, k + 1 ≤ m → m ≤ j →
        activationRound Q w ≤ x[m][p].st.activeAt := by
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
  exact active_of_open_join hsync hstepw hdil hwpt ht hlbl htj hgate
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

/-- The fast-confirm reading of slot `t`, reduced. -/
theorem fconf_reading_mod (Q : Params) (t : Nat) :
    (Q.slotLength * t + 2 * Q.delta) % Q.slotLength = 2 * Q.delta := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  rw [Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt (by omega)

theorem fconf_reading_div (Q : Params) (t : Nat) :
    (Q.slotLength * t + 2 * Q.delta) / Q.slotLength = t := by
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

/-- `processProposals2` writes only `chFrozen`; the confirmed chain rides through. -/
theorem processProposals2_chi (V : View Node (Msg (Chain Tx) (QCert Node Tx)))
    (t : Nat) (s : NodeState2 Node Tx) :
    (processProposals2 n proposer V t s).chi = s.chi := by
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

/-- `processProposals2` never writes `vFrozen`. -/
theorem processProposals2_vFrozen (V : View Node (Msg (Chain Tx) (QCert Node Tx)))
    (t : Nat) (s : NodeState2 Node Tx) :
    (processProposals2 n proposer V t s).vFrozen = s.vFrozen := by
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
    (processProposals2 n proposer V t s).chFrozen = s.chFrozen ∨
      ∃ sm ∈ V, (∃ chp qc ck, sm.msg =
          .propose chp ((processProposals2 n proposer V t s).chFrozen) qc ck t) ∧
        ValidProposal2 n proposer V sm := by
  unfold processProposals2
  have hgen : ∀ (l : List (SignedMsg Node (Msg (Chain Tx) (QCert Node Tx)))),
      (∀ a ∈ l, a ∈ V) → ∀ s₀ : NodeState2 Node Tx,
      (l.foldl (fun acc sm =>
        match sm.msg with
        | .propose _ chC _ _ t' =>
            if t' = t ∧ ValidProposal2 n proposer V sm ∧ chainLe acc.chFrozen chC then
              { acc with chFrozen := chC }
            else acc
        | .vote .. => acc) s₀).chFrozen = s₀.chFrozen ∨
      ∃ sm ∈ V, (∃ chp qc ck, sm.msg = .propose chp ((l.foldl (fun acc sm =>
        match sm.msg with
        | .propose _ chC _ _ t' =>
            if t' = t ∧ ValidProposal2 n proposer V sm ∧ chainLe acc.chFrozen chC then
              { acc with chFrozen := chC }
            else acc
        | .vote .. => acc) s₀).chFrozen) qc ck t) ∧ ValidProposal2 n proposer V sm := by
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

/-- `processProposals2` only ever *extends* `chFrozen`: the lines 33–36 guard requires
    the incoming fast-confirmed chain to extend the current one. -/
theorem processProposals2_chFrozen_mono (V : View Node (Msg (Chain Tx) (QCert Node Tx)))
    (t : Nat) (s : NodeState2 Node Tx) :
    chainLe s.chFrozen (processProposals2 n proposer V t s).chFrozen := by
  unfold processProposals2
  generalize V.toList = l
  induction l generalizing s with
  | nil => exact chainLe_refl _
  | cons a l ih =>
      rw [List.foldl_cons]
      obtain ⟨asd, amsg⟩ := a
      cases amsg with
      | vote ch src tgt t' => exact ih s
      | propose chp chC qc ck t' =>
          dsimp only
          split_ifs with hcond
          · exact chainLe_trans hcond.2.2 (ih { s with chFrozen := chC })
          · exact ih s

open Classical in
/-- **The fold's lower bound from a valid proposal in the view**: either the processed
    frozen chain extends the proposal's `chC₀`, or at scan time the accumulator was
    already not below `chC₀` — and then something not below `chC₀` survives into the
    result (the fold only extends). -/
theorem processProposals2_chFrozen_lb (V : View Node (Msg (Chain Tx) (QCert Node Tx)))
    (t : Nat) (s : NodeState2 Node Tx)
    {sm : SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))} (hsm : sm ∈ V)
    {chp₀ chC₀ : Chain Tx} {qc₀ : Option (QCert Node Tx)} {ck₀ : Checkpoint (Chain Tx)}
    (hmsg : sm.msg = .propose chp₀ chC₀ qc₀ ck₀ t)
    (hvalid : ValidProposal2 n proposer V sm) :
    chainLe chC₀ ((processProposals2 n proposer V t s).chFrozen) ∨
      ∃ y : Chain Tx, ¬ chainLe y chC₀ ∧
        chainLe y ((processProposals2 n proposer V t s).chFrozen) := by
  obtain ⟨sd, m0⟩ := sm
  have hm0 : m0 = Msg.propose chp₀ chC₀ qc₀ ck₀ t := hmsg
  subst hm0
  unfold processProposals2
  have hmono' : ∀ (l : List (SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))))
      (acc : NodeState2 Node Tx),
      chainLe acc.chFrozen ((l.foldl (fun acc sm =>
        match sm.msg with
        | .propose _ chC _ _ t' =>
            if t' = t ∧ ValidProposal2 n proposer V sm ∧ chainLe acc.chFrozen chC then
              { acc with chFrozen := chC }
            else acc
        | .vote .. => acc) acc).chFrozen) := by
    intro l
    induction l with
    | nil => exact fun acc => chainLe_refl _
    | cons a l ih =>
        intro acc
        rw [List.foldl_cons]
        obtain ⟨asd, amsg⟩ := a
        cases amsg with
        | vote ch src tgt t' => exact ih acc
        | propose chp chC qc ck t' =>
            dsimp only
            split_ifs with hcond
            · exact chainLe_trans hcond.2.2 (ih { acc with chFrozen := chC })
            · exact ih acc
  have hgen : ∀ (l : List (SignedMsg Node (Msg (Chain Tx) (QCert Node Tx)))),
      (⟨sd, Msg.propose chp₀ chC₀ qc₀ ck₀ t⟩ :
        SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ l →
      ∀ acc : NodeState2 Node Tx,
      chainLe chC₀ ((l.foldl (fun acc sm =>
        match sm.msg with
        | .propose _ chC _ _ t' =>
            if t' = t ∧ ValidProposal2 n proposer V sm ∧ chainLe acc.chFrozen chC then
              { acc with chFrozen := chC }
            else acc
        | .vote .. => acc) acc).chFrozen) ∨
      ∃ y : Chain Tx, ¬ chainLe y chC₀ ∧
        chainLe y ((l.foldl (fun acc sm =>
        match sm.msg with
        | .propose _ chC _ _ t' =>
            if t' = t ∧ ValidProposal2 n proposer V sm ∧ chainLe acc.chFrozen chC then
              { acc with chFrozen := chC }
            else acc
        | .vote .. => acc) acc).chFrozen) := by
    intro l
    induction l with
    | nil => intro h; cases h
    | cons a l ih =>
        intro hmem acc
        rw [List.foldl_cons]
        rcases List.mem_cons.mp hmem with rfl | hmem'
        · dsimp only
          by_cases hg : chainLe acc.chFrozen chC₀
          · rw [if_pos ⟨rfl, hvalid, hg⟩]
            exact Or.inl (hmono' l { acc with chFrozen := chC₀ })
          · rw [if_neg (fun hc => hg hc.2.2)]
            exact Or.inr ⟨acc.chFrozen, hg, hmono' l acc⟩
        · exact ih hmem' _
  exact hgen V.toList (Finset.mem_toList.mpr hsm) s

/-- Outside the vote and merge phases, no branch of `handler2` writes the frozen state. -/
theorem handler2_frozen {p : Node} {r : Time}
    {V : View Node (Msg (Chain Tx) (QCert Node Tx))} {s : NodeState2 Node Tx}
    (h1 : r % Q.slotLength ≠ Q.delta) (h2 : r % Q.slotLength ≠ 3 * Q.delta) :
    (handler2Core Q n kappa pool proposer dot p r V s).state.vFrozen = s.vFrozen ∧
      (handler2Core Q n kappa pool proposer dot p r V s).state.chFrozen = s.chFrozen := by
  simp only [handler2Core, apply_ite NodeStepResult.state]
  split_ifs <;>
    first
      | exact ⟨rfl, rfl⟩
      | exact absurd ‹r % Q.slotLength = Q.delta› h1
      | exact absurd ‹r % Q.slotLength = 3 * Q.delta› h2

/-- The merge phase, unfolded: freeze the view and the fast-confirmed chain. -/
theorem handler2_merge {p : Node} {r : Time}
    {V : View Node (Msg (Chain Tx) (QCert Node Tx))} {s : NodeState2 Node Tx}
    (hmod : r % Q.slotLength = 3 * Q.delta) :
    (handler2Core Q n kappa pool proposer dot p r V s).state =
      { s with vFrozen := V, chFrozen := (fastConfirmSimple n V (r / Q.slotLength)).1 } := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  simp only [handler2Core, apply_ite NodeStepResult.state]
  split_ifs <;> first | rfl | omega

/-- The fast-confirm phase, unfolded: adopt the fast-confirmed chain when a certificate
    exists. -/
theorem handler2_fastconfirm {p : Node} {r : Time}
    {V : View Node (Msg (Chain Tx) (QCert Node Tx))} {s : NodeState2 Node Tx}
    (hmod : r % Q.slotLength = 2 * Q.delta) :
    (handler2Core Q n kappa pool proposer dot p r V s).state =
      if (fastConfirmSimple n V (r / Q.slotLength)).2.isSome then
        { s with chi :=
            if chainLe (fastConfirmSimple n V (r / Q.slotLength)).1 s.chi then s.chi
            else (fastConfirmSimple n V (r / Q.slotLength)).1 }
      else s := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  simp only [handler2Core, apply_ite NodeStepResult.state]
  split_ifs <;> first | rfl | omega

/-- Outside the vote and fast-confirm phases, no branch of `handler2` writes the
    confirmed chain. -/
theorem handler2_chi {p : Node} {r : Time}
    {V : View Node (Msg (Chain Tx) (QCert Node Tx))} {s : NodeState2 Node Tx}
    (h1 : r % Q.slotLength ≠ Q.delta) (h2 : r % Q.slotLength ≠ 2 * Q.delta) :
    (handler2Core Q n kappa pool proposer dot p r V s).state.chi = s.chi := by
  simp only [handler2Core, apply_ite NodeStepResult.state]
  split_ifs <;>
    first
      | rfl
      | exact absurd ‹r % Q.slotLength = Q.delta› h1
      | exact absurd ‹r % Q.slotLength = 2 * Q.delta› h2

/-- The vote phase's state, unfolded: process the proposals, then run the κ-deep rule —
    only once active. -/
theorem handler2_vote_state {p : Node} {r : Time}
    {V : View Node (Msg (Chain Tx) (QCert Node Tx))} {s : NodeState2 Node Tx}
    (hmod : r % Q.slotLength = Q.delta) :
    (handler2Core Q n kappa pool proposer dot p r V s).state =
      { processProposals2 n proposer V (r / Q.slotLength) s with
        chi :=
          if s.activeAt ≤ r then
            [(processProposals2 n proposer V (r / Q.slotLength) s).chi,
              kappaPrefix kappa (r / Q.slotLength)
                (mfc (processProposals2 n proposer V (r / Q.slotLength)
                  s).vFrozen V
                (processProposals2 n proposer V (r / Q.slotLength) s).chFrozen
                (r / Q.slotLength))].foldl
              (fun acc c =>
                if chainLe c (mfc (processProposals2 n proposer V (r / Q.slotLength)
                    s).vFrozen V
                  (processProposals2 n proposer V (r / Q.slotLength) s).chFrozen
                  (r / Q.slotLength)) then
                  (if chainLe acc c then c else acc)
                else acc)
              (processProposals2 n proposer V (r / Q.slotLength) s).chi
          else (processProposals2 n proposer V (r / Q.slotLength) s).chi } := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  simp only [handler2Core, apply_ite NodeStepResult.state]
  split_ifs <;> first | rfl | omega

/-- The chain the vote phase settles on extends this tick's fork-choice: `proposedNow`
    filters on exactly that, and its absence falls back to the fork-choice itself. -/
theorem chainLe_getD_findSome (l : List (SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))))
    (chMFC : Chain Tx) (slot : Nat) (pr : Node) :
    chainLe chMFC ((l.findSome? (fun sm => match sm.msg with
      | .propose chp _ _ _ t' =>
          if sm.sender == pr && t' == slot && proposedAt chp == slot &&
              slotsIncreasing chp && chainLe chMFC chp then some chp
          else none
      | .vote .. => none)).getD chMFC) := by
  cases hfind : l.findSome? (fun sm => match sm.msg with
      | .propose chp _ _ _ t' =>
          if sm.sender == pr && t' == slot && proposedAt chp == slot &&
              slotsIncreasing chp && chainLe chMFC chp then some chp
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
    ∃ ch, (handler2Core Q n kappa pool proposer dot p r V s).send
        = {Msg.vote ch dot dot (r / Q.slotLength)} ∧
      chainLe (mfc (processProposals2 n proposer V (r / Q.slotLength) s).vFrozen V
        (processProposals2 n proposer V (r / Q.slotLength) s).chFrozen (r / Q.slotLength)) ch := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  simp only [handler2Core, apply_ite NodeStepResult.send]
  split_ifs <;>
    first
      | omega
      | exact ⟨_, rfl, chainLe_getD_findSome _ _ _ _⟩

/-- The vote phase's chain choice, named: the first slot-`slot` proposal from the slot's
    proposer extending `chMFC`, or `chMFC`. Definitionally the term inside `handler2Core`'s
    vote branch — a proof-layer name for it, so `handler2_vote_send_eq` can expose the sent
    chain exactly. -/
noncomputable def voteChoice (prop : Nat → Node)
    (V : View Node (Msg (Chain Tx) (QCert Node Tx))) (slot : Nat) (chMFC : Chain Tx) :
    Chain Tx :=
  (V.toList.findSome? (fun sm => match sm.msg with
    | .propose chp _ _ _ t' =>
        if sm.sender == prop slot && t' == slot && proposedAt chp == slot &&
            slotsIncreasing chp && chainLe chMFC chp then some chp
        else none
    | .vote .. => none)).getD chMFC

/-- The vote phase's send, exactly: one vote for `voteChoice`. -/
theorem handler2_vote_send_eq {p : Node} {r : Time}
    {V : View Node (Msg (Chain Tx) (QCert Node Tx))} {s : NodeState2 Node Tx}
    (hmod : r % Q.slotLength = Q.delta) (hgate : s.activeAt ≤ r) :
    (handler2Core Q n kappa pool proposer dot p r V s).send
      = {Msg.vote (voteChoice proposer V (r / Q.slotLength)
          (mfc (processProposals2 n proposer V (r / Q.slotLength) s).vFrozen V
            (processProposals2 n proposer V (r / Q.slotLength) s).chFrozen
            (r / Q.slotLength))) dot dot (r / Q.slotLength)} := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  simp only [handler2Core, voteChoice, apply_ite NodeStepResult.send]
  split_ifs <;> first | rfl | omega

/-- The vote phase's send content, whichever it is: the `voteChoice`. -/
theorem handler2_vote_content {p : Node} {r : Time}
    {V : View Node (Msg (Chain Tx) (QCert Node Tx))} {s : NodeState2 Node Tx}
    {m : Msg (Chain Tx) (QCert Node Tx)}
    (hmod : r % Q.slotLength = Q.delta)
    (h : m ∈ (handler2Core Q n kappa pool proposer dot p r V s).send) :
    m = Msg.vote (voteChoice proposer V (r / Q.slotLength)
      (mfc (processProposals2 n proposer V (r / Q.slotLength) s).vFrozen V
        (processProposals2 n proposer V (r / Q.slotLength) s).chFrozen
        (r / Q.slotLength))) dot dot (r / Q.slotLength) := by
  by_cases hgate : s.activeAt ≤ r
  · rw [handler2_vote_send_eq hmod hgate] at h
    exact Multiset.mem_singleton.mp h
  · exfalso
    obtain ⟨hactive, -⟩ := mem_handler2_send h
    exact hgate hactive

/-- The certificate `fastconfirmsimple` attaches, in full: the support votes' contents. -/
theorem fastConfirmSimple_snd_spec {V : View Node (Msg (Chain Tx) (QCert Node Tx))}
    {t : Nat} {ch : Chain Tx} {cert : QCert Node Tx}
    (h : fastConfirmSimple n V t = (ch, some cert)) :
    cert = ((votes V).filter (fun sm => msgSlot sm.msg = t ∧
      chainLe ch (msgChain sm.msg))).image
        (fun sm => (sm.sender, msgChain sm.msg, msgSlot sm.msg)) := by
  unfold fastConfirmSimple at h
  dsimp only at h
  split at h
  · exact absurd (congrArg Prod.snd h) (by simp)
  · have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only at h1 h2
    rw [← h1]
    exact (Option.some_injective _ h2).symm

/-! ### One tick, precisely: state, time, reading, emission -/

/-- A tick step, described whole: for the filler this tick chose, the ticking
    validator's successor state is the handler's, and every handler send is in the next
    log. One existential, so state facts and emissions about the same tick agree on the
    filler. -/
theorem tick_effect {x : Exec Pr2 S} {k : Nat} {p : Node} {t : Time}
    (hlbl : x.lbl k = .tick p t) :
    ∃ dt : Checkpoint (Chain Tx),
      x[k + 1][p].st =
        (handler2Core Q n kappa pool proposer dt p t x[k][p].view x[k][p].st).state ∧
      ∀ m ∈ (handler2Core Q n kappa pool proposer dt p t x[k][p].view x[k][p].st).send,
        (⟨p, m⟩ : SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ x[k + 1].sent := by
  have hstep : Step Pr2 S (x.lbl k) x[k] x[k + 1] := x.step k
  rw [hlbl] at hstep
  obtain ⟨hen, heff⟩ := hstep
  simp only [spec] at hen heff
  rw [nodeStep_iff_exists] at heff
  obtain ⟨res, hres, hpost⟩ := heff
  rw [protocol2_step_tick, mem_handler2_iff] at hres
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
    rw [protocol2_step_tick, mem_handler2_iff] at hres
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

/-- At a slot-`0` vote tick, the frozen chain is still the initial genesis: no reading
    before `voting(0) = Δ` has the vote or merge phase. -/
theorem chFrozen_at_slot0_tick {x : Exec Pr2 S} (hsync : SynchronizedClocks x)
    (hstepw : TimeStepwise x) (hone : OneTickPerReading x)
    {p : Node} {j : Nat} (hj : x.lbl j = .tick p (Q.slotLength * 0 + Q.delta)) :
    x[j][p].st.chFrozen = [] := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  have hmono := hstepw.timeMonotone
  have htj : x[j].time = Q.slotLength * 0 + Q.delta := tick_reading hsync hj
  have hpers : ∀ m, m ≤ j → x[m][p].st.chFrozen = x[0][p].st.chFrozen := by
    intro m
    induction m with
    | zero => exact fun _ => rfl
    | succ m ih =>
        intro h2
        have hprev := ih (by omega)
        have hcond : ∀ tr : Time, x.lbl m = .tick p tr →
            tr % Q.slotLength ≠ Q.delta ∧ tr % Q.slotLength ≠ 3 * Q.delta := by
          intro tr hltr
          have htr : x[m].time = tr := tick_reading hsync hltr
          have hhi : tr ≤ Q.slotLength * 0 + Q.delta := by
            rw [← htr, ← htj]
            exact time_le_of_le hmono (by omega)
          constructor
          · intro hphase
            have htr' : tr = Q.slotLength * 0 + Q.delta := by
              have hlt : tr % Q.slotLength = tr ∨ Q.slotLength ≤ tr := by
                rcases Nat.lt_or_ge tr Q.slotLength with h | h
                · exact Or.inl (Nat.mod_eq_of_lt h)
                · exact Or.inr h
              rcases hlt with h | h
              · omega
              · omega
            rw [htr'] at hltr
            have := hone m j p _ hltr hj
            omega
          · intro hphase
            have hmod : tr % Q.slotLength < Q.slotLength := Nat.mod_lt _ (by omega)
            have : tr % Q.slotLength ≤ tr := Nat.mod_le _ _
            omega
        exact ((frozen_step2 hcond).2).trans hprev
  have h0 : x[0][p].st.chFrozen = [] := by
    have h := x.init.2.1 p
    show ((x.cfg 0)[p]).st.chFrozen = []
    rw [h]
    rfl
  rw [hpers j (le_refl j), h0]

/-- Outside the vote and fast-confirm phases, one step preserves a validator's confirmed
    chain — whoever moves. The `chi` clone of `frozen_step2`. -/
theorem chi_step2_quiet {x : Exec Pr2 S} {m : Nat} {p : Node}
    (hcond : ∀ tr : Time, x.lbl m = .tick p tr →
      tr % Q.slotLength ≠ Q.delta ∧ tr % Q.slotLength ≠ 2 * Q.delta) :
    x[m + 1][p].st.chi = x[m][p].st.chi := by
  have hstep : Step Pr2 S (x.lbl m) x[m] x[m + 1] := x.step m
  refine hstep.elimR (motive := fun a c c' =>
      (∀ tr : Time, a = .tick p tr →
        tr % Q.slotLength ≠ Q.delta ∧ tr % Q.slotLength ≠ 2 * Q.delta) →
      c'[p].st.chi = c[p].st.chi)
    ?_ ?_ ?_ ?_ ?_ ?_ hcond
  · -- advance: nodes untouched
    intro d t _
    rfl
  · -- tick: outside the writing phases by hypothesis
    intro d d' q t hen hns hc
    rw [nodeStep_iff_exists] at hns
    obtain ⟨res, hres, rfl⟩ := hns
    rw [protocol2_step_tick, mem_handler2_iff] at hres
    obtain ⟨dt, rfl⟩ := hres
    by_cases hq : q = p
    · subst hq
      have hph := hc t rfl
      have hfr := handler2_chi (Q := Q) (n := n) (kappa := kappa) (pool := pool)
        (proposer := proposer) (dot := dt) (p := q) (r := t)
        (V := (setClock q t d)[q].view) (s := (setClock q t d)[q].st) hph.1 hph.2
      simpa [applyNodeStepResult_getElem, setClock_getElem] using hfr
    · simp [applyNodeStepResult_getElem, setClock_getElem, hq]
  · -- deliver: the recv reaction returns the state unchanged
    intro d d' q mm hen hns _
    rw [nodeStep_iff_exists] at hns
    obtain ⟨res, hres, rfl⟩ := hns
    rw [protocol2_step_recv] at hres
    subst hres
    by_cases hq : q = p
    · subst hq
      simp [applyNodeStepResult_getElem, receive_getElem]
    · simp [applyNodeStepResult_getElem, receive_getElem, hq]
  · -- wake: writes `activeAt` only
    intro d d' q hen hns _
    rw [nodeStep_iff_exists] at hns
    obtain ⟨res, hres, rfl⟩ := hns
    rw [protocol2_step_wake] at hres
    subst hres
    by_cases hq : q = p
    · subst hq
      simp [applyNodeStepResult_getElem]
    · simp [applyNodeStepResult_getElem, hq]
  · -- custom: there are none
    intro d d' q ev hen hns
    exact ev.elim
  · -- adversarial: nodes untouched
    intro d q mm hen _
    rfl

/-- **One step of the confirmed chain**: it is unchanged, or the step is its owner's
    vote tick with the joining check open and `chi` becomes the κ-deep prefix of that
    tick's fork choice, or it is the owner's fast-confirm tick with a certificate and
    `chi` becomes the confirmed chain. The case analysis Lemma 5's induction walks. -/
theorem chi_step2 {x : Exec Pr2 S} {m : Nat} {p : Node} :
    x[m + 1][p].st.chi = x[m][p].st.chi ∨
    (∃ ti : Nat, x.lbl m = .tick p (Q.slotLength * ti + Q.delta) ∧
      x[m][p].st.activeAt ≤ Q.slotLength * ti + Q.delta ∧
      x[m + 1][p].st.chi = kappaPrefix kappa ti (mfc (processProposals2 n proposer
          (x[m][p].view) ti (x[m][p].st)).vFrozen (x[m][p].view)
        (processProposals2 n proposer (x[m][p].view) ti (x[m][p].st)).chFrozen ti)) ∨
    (∃ ti : Nat, x.lbl m = .tick p (Q.slotLength * ti + 2 * Q.delta) ∧
      (fastConfirmSimple n (x[m][p].view) ti).2.isSome = true ∧
      ¬ chainLe (fastConfirmSimple n (x[m][p].view) ti).1 (x[m][p].st).chi ∧
      x[m + 1][p].st.chi = (fastConfirmSimple n (x[m][p].view) ti).1) := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  by_cases hlp : ∃ tr, x.lbl m = .tick p tr
  case neg => exact Or.inl (chi_step2_quiet (fun tr hr => absurd ⟨tr, hr⟩ hlp))
  case pos =>
  obtain ⟨tr, hr⟩ := hlp
  by_cases hph1 : tr % Q.slotLength = Q.delta
  · -- the vote phase
    obtain ⟨dt, hst, -⟩ := tick_effect hr
    have htr : tr = Q.slotLength * (tr / Q.slotLength) + Q.delta := by
      conv_lhs => rw [← Nat.div_add_mod tr Q.slotLength]
      rw [hph1]
    have hstate := handler2_vote_state (Q := Q) (n := n) (kappa := kappa) (pool := pool)
      (proposer := proposer) (dot := dt) (p := p) (r := tr)
      (V := x[m][p].view) (s := x[m][p].st) hph1
    rw [hstate] at hst
    by_cases hguard : (x[m][p].st).activeAt ≤ tr
    · rw [if_pos hguard] at hst
      have hchi : x[m + 1][p].st.chi
          = [(processProposals2 n proposer (x[m][p].view) (tr / Q.slotLength)
              (x[m][p].st)).chi,
            kappaPrefix kappa (tr / Q.slotLength)
              (mfc (processProposals2 n proposer (x[m][p].view)
                (tr / Q.slotLength) (x[m][p].st)).vFrozen (x[m][p].view)
              (processProposals2 n proposer (x[m][p].view) (tr / Q.slotLength)
                (x[m][p].st)).chFrozen (tr / Q.slotLength))].foldl
            (fun acc c =>
              if chainLe c (mfc (processProposals2 n proposer (x[m][p].view)
                  (tr / Q.slotLength) (x[m][p].st)).vFrozen (x[m][p].view)
                (processProposals2 n proposer (x[m][p].view) (tr / Q.slotLength)
                  (x[m][p].st)).chFrozen (tr / Q.slotLength)) then
                (if chainLe acc c then c else acc)
              else acc)
            (processProposals2 n proposer (x[m][p].view) (tr / Q.slotLength)
              (x[m][p].st)).chi := by
        rw [hst]
      rw [List.foldl_cons, List.foldl_cons, List.foldl_nil] at hchi
      split_ifs at hchi <;>
        first
          | exact Or.inr (Or.inl ⟨tr / Q.slotLength, htr ▸ hr, htr ▸ hguard, hchi⟩)
          | exact Or.inl (by
              rw [hchi]
              exact processProposals2_chi _ _ _)
    · rw [if_neg hguard] at hst
      refine Or.inl ?_
      rw [hst]
      exact processProposals2_chi _ _ _
  · by_cases hph2 : tr % Q.slotLength = 2 * Q.delta
    · -- the fast-confirm phase
      obtain ⟨dt, hst, -⟩ := tick_effect hr
      have htr : tr = Q.slotLength * (tr / Q.slotLength) + 2 * Q.delta := by
        conv_lhs => rw [← Nat.div_add_mod tr Q.slotLength]
        rw [hph2]
      have hstate := handler2_fastconfirm (Q := Q) (n := n) (kappa := kappa)
        (pool := pool) (proposer := proposer) (dot := dt) (p := p) (r := tr)
        (V := x[m][p].view) (s := x[m][p].st) hph2
      rw [hstate] at hst
      by_cases hq : (fastConfirmSimple n (x[m][p].view) (tr / Q.slotLength)).2.isSome
      · rw [if_pos hq] at hst
        have hchi : x[m + 1][p].st.chi
            = if chainLe (fastConfirmSimple n (x[m][p].view) (tr / Q.slotLength)).1
                (x[m][p].st).chi then (x[m][p].st).chi
              else (fastConfirmSimple n (x[m][p].view) (tr / Q.slotLength)).1 := by
          rw [hst]
        by_cases hg : chainLe (fastConfirmSimple n (x[m][p].view)
            (tr / Q.slotLength)).1 (x[m][p].st).chi
        · rw [if_pos hg] at hchi
          exact Or.inl hchi
        · rw [if_neg hg] at hchi
          exact Or.inr (Or.inr ⟨tr / Q.slotLength, htr ▸ hr, hq, hg, hchi⟩)
      · rw [if_neg hq] at hst
        refine Or.inl ?_
        rw [hst]
    · refine Or.inl (chi_step2_quiet (fun tr' hr' => ?_))
      rw [hr] at hr'
      injection hr' with h1 h2
      first
        | exact h2 ▸ ⟨hph1, hph2⟩
        | exact ⟨hph1, hph2⟩

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
        rw [protocol2_step_tick, mem_handler2_iff] at hres
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

/-- The longest-chain fold never shrinks below its initial value. -/
theorem foldl_longest_le_init {l : List (Chain Tx)} {a : Chain Tx} :
    a.length ≤ (l.foldl (fun best ch => if best.length < ch.length then ch else best) a).length := by
  induction l generalizing a with
  | nil => exact le_refl _
  | cons b l ih =>
      rw [List.foldl_cons]
      refine le_trans ?_ (ih (a := if a.length < b.length then b else a))
      split_ifs with h
      · omega
      · exact le_refl _

/-- The longest-chain fold dominates every list member. -/
theorem foldl_longest_length_ge {l : List (Chain Tx)} {b a : Chain Tx} (hb : b ∈ l) :
    b.length ≤ (l.foldl (fun best ch => if best.length < ch.length then ch else best) a).length := by
  induction l generalizing a with
  | nil => cases hb
  | cons c l ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hb with rfl | hb'
      · refine le_trans ?_ (foldl_longest_le_init (a := if a.length < b.length then b else a))
        split_ifs with h <;> omega
      · exact ih hb'

/-- A quorum-supported candidate bounds `fastconfirmsimple`'s chain from below in length:
    the fold returns the longest quorum-supported candidate. -/
theorem fastConfirmSimple_length_ge {V : View Node (Msg (Chain Tx) (QCert Node Tx))}
    {t : Nat} {ch : Chain Tx} (hch : ch ≠ [])
    (hcand : ch ∈ candidates V ([] : Chain Tx))
    (hsupp : 2 * n ≤ 3 * (((votes V).filter (fun sm => msgSlot sm.msg = t ∧
      chainLe ch (msgChain sm.msg))).image SignedMsg.sender).card) :
    ch.length ≤ (fastConfirmSimple n V t).1.length := by
  have hpos : 0 < ch.length := by
    cases ch with
    | nil => exact absurd rfl hch
    | cons _ _ => simp
  unfold fastConfirmSimple
  dsimp only
  have hmem : ch ∈ ((candidates V ([] : Chain Tx)).filter (fun c => 2 * n ≤
      3 * (((votes V).filter (fun sm => msgSlot sm.msg = t ∧
        chainLe c (msgChain sm.msg))).image SignedMsg.sender).card)).toList :=
    Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨hcand, hsupp⟩)
  have hlen := foldl_longest_length_ge (a := ([] : Chain Tx)) hmem
  split
  · rename_i hcond
    exfalso
    rw [List.isEmpty_iff] at hcond
    rw [hcond.1] at hlen
    simp only [List.length_nil] at hlen
    omega
  · exact hlen

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
    ⟪vote, e, src, tgt, t, p⟫
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
    have hview : ⟪vote, e, esrc, etgt, t, p⟫ ∈ x[ip][v].view := by
      refine hsyn iv ip v _ hsent ?_ hvAw
      rw [htiv, hip]
      omega
    have hsent_ip : ⟪vote, e, esrc, etgt, t, p⟫ ∈ x[ip].sent :=
      views_sound x ip v _ hview
    have hhon_ip : p ∉ S.adv ((x[ip].time : Int)) := by
      rw [hip]
      exact hhon _ (by omega)
    refine ⟨⟨p, Msg.vote e esrc etgt t⟩, ?_, rfl⟩
    -- build the filter membership inside out
    have hvv : ⟪vote, e, esrc, etgt, t, p⟫ ∈ votes (x[ip][v].view) := by
      simp only [votes, Finset.mem_filter]
      exact ⟨hview, trivial⟩
    have hfeq : ⟪vote, e, esrc, etgt, t, p⟫ ∈ filEq (x[ip][v].view) := by
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
    have hfexp : ⟪vote, e, esrc, etgt, t, p⟫
        ∈ fil1Exp (filEq (x[ip][v].view)) (t + 1) := by
      simp only [fil1Exp, Finset.mem_filter]
      exact ⟨hfeq, rfl⟩
    have hflmd : ⟪vote, e, esrc, etgt, t, p⟫
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
    (hview : ⟪vote, e, src, tgt, t, q⟫ ∈ x[iw][w].view)
    (hhq : q ∉ S.adv ((x[iw].time : Int))) {ch : Chain Tx} (hext : chainLe ch e) :
    ⟪vote, e, src, tgt, t, q⟫
      ∈ votesFor (x[iw][w].view) ch (t + 1) := by
  have hlog : ⟪vote, e, src, tgt, t, q⟫ ∈ x[iw].sent :=
    views_sound x iw w _ hview
  have hvv : ⟪vote, e, src, tgt, t, q⟫ ∈ votes (x[iw][w].view) := by
    simp only [votes, Finset.mem_filter]
    exact ⟨hview, trivial⟩
  have hfeq : ⟪vote, e, src, tgt, t, q⟫ ∈ filEq (x[iw][w].view) := by
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
  have hfexp : ⟪vote, e, src, tgt, t, q⟫
      ∈ fil1Exp (filEq (x[iw][w].view)) (t + 1) := by
    simp only [fil1Exp, Finset.mem_filter]
    exact ⟨hfeq, rfl⟩
  have hflmd : ⟪vote, e, src, tgt, t, q⟫
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

/-- **Two quorum-supported chains of one slot are comparable**, seen from any one view:
    the supporter sets each hold more than `2n/3` of at most `n` validators, so they
    share an honest member, whose unique slot-`t` vote extends both chains. -/
theorem supported_comparable {x : Exec Pr2 S}
    (hsync : SynchronizedClocks x) (hone : OneTickPerReading x)
    (hmc : S.MonotoneCorruption) (hmono : TimeMonotone x)
    (hcb : S.CorruptionBounded Q.f) (hfn : 3 * Q.f < n)
    (hcard : Fintype.card Node ≤ n)
    {i : Nat} {w : Node} {t : Nat} {ch1 ch2 : Chain Tx}
    (h1 : 2 * n ≤ 3 * (((votes (x[i][w].view)).filter (fun sm => msgSlot sm.msg = t ∧
      chainLe ch1 (msgChain sm.msg))).image SignedMsg.sender).card)
    (h2 : 2 * n ≤ 3 * (((votes (x[i][w].view)).filter (fun sm => msgSlot sm.msg = t ∧
      chainLe ch2 (msgChain sm.msg))).image SignedMsg.sender).card) :
    chainLe ch1 ch2 ∨ chainLe ch2 ch1 := by
  set A := ((votes (x[i][w].view)).filter (fun sm => msgSlot sm.msg = t ∧
    chainLe ch1 (msgChain sm.msg))).image SignedMsg.sender with hA
  set B := ((votes (x[i][w].view)).filter (fun sm => msgSlot sm.msg = t ∧
    chainLe ch2 (msgChain sm.msg))).image SignedMsg.sender with hB
  have hinter : Q.f < (A ∩ B).card := by
    have hu : (A ∪ B).card ≤ Fintype.card Node := Finset.card_le_univ _
    have hsum := Finset.card_union_add_card_inter A B
    omega
  obtain ⟨q, hqAB, hqhon⟩ : ∃ q ∈ A ∩ B, q ∉ S.adv ((x[i].time : Int)) := by
    by_contra hno
    have hsub : A ∩ B ⊆ S.adv ((x[i].time : Int)) := by
      intro q hq
      by_contra hq'
      exact hno ⟨q, hq, hq'⟩
    have h3 := Finset.card_le_card hsub
    have h4 := hcb ((x[i].time : Int))
    omega
  obtain ⟨hqA, hqB⟩ := Finset.mem_inter.mp hqAB
  obtain ⟨sm1, hsm1, hs1⟩ := Finset.mem_image.mp hqA
  obtain ⟨sm2, hsm2, hs2⟩ := Finset.mem_image.mp hqB
  rw [Finset.mem_filter] at hsm1 hsm2
  obtain ⟨hv1, hslot1, hle1⟩ := hsm1
  obtain ⟨hv2, hslot2, hle2⟩ := hsm2
  have hlog1 : sm1 ∈ x[i].sent :=
    views_sound x i w _ (by simp only [votes, Finset.mem_filter] at hv1; exact hv1.1)
  have hlog2 : sm2 ∈ x[i].sent :=
    views_sound x i w _ (by simp only [votes, Finset.mem_filter] at hv2; exact hv2.1)
  obtain ⟨e1, src1, tgt1, s1, hm1⟩ := exists_vote_of_mem_votes hv1
  obtain ⟨e2, src2, tgt2, s2, hm2⟩ := exists_vote_of_mem_votes hv2
  have hss1 : s1 = t := by
    have e' : msgSlot sm1.msg = s1 := by rw [hm1]; exact rfl
    rw [e'] at hslot1
    omega
  have hss2 : s2 = t := by
    have e' : msgSlot sm2.msg = s2 := by rw [hm2]; exact rfl
    rw [e'] at hslot2
    omega
  subst hss1
  subst hss2
  have hh1 : sm1.sender ∉ S.adv ((x[i].time : Int)) := by
    rw [hs1]
    exact hqhon
  have hh2 : sm2.sender ∉ S.adv ((x[i].time : Int)) := by
    rw [hs2]
    exact hqhon
  have heq := honest_vote_unique2 hsync hone hmc hmono hlog1 hlog2 hh1 hh2
    (by rw [hs1, hs2]) hm1 hm2
  rw [heq] at hle2
  exact comparable_of_common_extension hle1 hle2

/-- **The frozen state entering a vote tick**: for a validator active in slot `t+1`, the
    view and fast-confirmed chain frozen at its `merge(t)` tick are what its `voting(t+1)`
    tick reads — the merge tick exists inside the activity window, and no reading in
    between can rewrite them. Extracted from `le_mfc_at_vote2` for reuse by Lemma 3. -/
theorem frozen_at_vote_tick {x : Exec Pr2 S}
    (hsync : SynchronizedClocks x) (hstepw : TimeStepwise x) (hdil : Diligent x)
    (hone : OneTickPerReading x)
    {t : Nat} {p : Node} (hp : p ∈ Active Q S ((t : Int) + 1))
    {j : Nat} (hj : x.lbl j = .tick p (Q.slotLength * (t + 1) + Q.delta)) :
    ∃ im, im < j ∧ x[im].time = Q.slotLength * t + 3 * Q.delta ∧
      x[j][p].st.vFrozen = x[im][p].view ∧
      x[j][p].st.chFrozen = (fastConfirmSimple n (x[im][p].view) t).1 := by
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
  have hawake : ∀ r : Time, Q.slotLength * t + 2 * Q.delta ≤ r →
      r ≤ Q.slotLength * (t + 1) + Q.delta → p ∈ S.awake ((r : Int)) := by
    intro r h1 h2
    refine mem_awakeThroughout.mp hp _ ?_ ?_ <;> rw [hvot1] <;> omega
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
  have hmstate : x[im + 1][p].st = { x[im][p].st with vFrozen := x[im][p].view, chFrozen := (fastConfirmSimple n (x[im][p].view) t).1 } := by
    obtain ⟨dm, hst, -⟩ := tick_effect hlblm
    rw [hst, handler2_merge (merge_reading_mod Q t), merge_reading_div Q t]
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
  have hsj := hpers j (by omega) (le_refl j)
  rw [hmstate] at hsj
  exact ⟨im, himj, htim, hsj.1, hsj.2⟩

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
      (mfc (processProposals2 n proposer (x[j][p].view) (t + 1) (x[j][p].st)).vFrozen
        (x[j][p].view)
        (processProposals2 n proposer (x[j][p].view) (t + 1) (x[j][p].st)).chFrozen (t + 1)) := by
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
  -- the frozen state entering the vote tick
  obtain ⟨im, himj, htim, hvfj, hcfj⟩ := frozen_at_vote_tick hsync hstepw hdil hone hp hj
  have hsj : x[j][p].st.vFrozen = x[im][p].view ∧
      x[j][p].st.chFrozen = (fastConfirmSimple n (x[im][p].view) t).1 := ⟨hvfj, hcfj⟩
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
    have hviewm : ⟪vote, e, esrc, etgt, t, w⟫ ∈ x[im][p].view := by
      refine hsyn iv im p _ hsent ?_ hAwm
      rw [htiv, htim]
      omega
    have hviewj : ⟪vote, e, esrc, etgt, t, w⟫ ∈ x[j][p].view := by
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
  set s' := processProposals2 n proposer (x[j][p].view) (t + 1) (x[j][p].st) with hs'def
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
      have hvp' : sd = proposer (t + 1) ∧ proposedAt chp = (t + 1) ∧
          chainLe s'.chFrozen chp ∧
          (s'.chFrozen = [] ∨ ∃ cert : QCert Node Tx, qc = some cert ∧
            2 * n ≤ 3 * (cert.image Prod.fst).card ∧
            ∀ e ∈ cert, chainLe s'.chFrozen e.2.1 ∧ e.2.2 = (t + 1) - 1 ∧
              ∃ src tgt : Checkpoint (Chain Tx),
                ⟪vote, e.2.1, src, tgt, e.2.2, e.1⟫ ∈ x[j][p].view) := hvp
      rcases hvp'.2.2.2 with hgen0 | ⟨cert, hqc, hcard, hcert⟩
      · rw [hgen0]
        exact Or.inr (chainLe_nil ch)
      · obtain ⟨q0, hq0mem, hq0hon⟩ :=
          exists_honest_sender (r := ((x[j].time : Int))) hcb hfn hcard
        obtain ⟨entry, hentry, hfst⟩ := Finset.mem_image.mp hq0mem
        obtain ⟨hchC, hslotE, hinV⟩ := hcert entry hentry
        have hslotE' : entry.2.2 = t := by omega
        rw [hslotE'] at hinV
        obtain ⟨esrc, etgt, hinV⟩ := hinV
        have hlogE : ⟪vote, entry.2.1, esrc, etgt, t, entry.1⟫ ∈ x[j].sent :=
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

/-- **A vote-round majority transfers into the proposer's propose-round views.** The
    numerator's votes live in the voter's frozen (merge-round) view, which synchrony
    delivers to the proposer by `propose(t0+1)`; the denominator's voters reach the voter
    by synchrony the other way; and `filEq` survival transfers because `Relay` puts the
    proposer's whole view inside the voter's — a conflicting vote that kills a sender at
    the proposer would be relayed and kill it at the voter too. The paper's "Graded
    Delivery" step of Lemma 4, and the first use of `Relay`. -/
theorem majority_transfer {x : Exec Pr2 S} (hsync : SynchronizedClocks x)
    (hsyn : Synchrony 0 Q.delta x) (hrel : Relay 0 Q.delta x)
    {t0 : Nat} {j : Nat} {vi : Node}
    (hj : x.lbl j = .tick vi (Q.slotLength * (t0 + 1) + Q.delta))
    {im : Nat} (htim : x[im].time = Q.slotLength * t0 + 3 * Q.delta)
    {k : Nat} {vp : Node} (hk : x.lbl k = .tick vp (Q.slotLength * (t0 + 1)))
    (htk : x[k].time = Q.slotLength * (t0 + 1))
    {ch : Chain Tx}
    (hmaj : Majority (x[im][vi].view) (x[j][vi].view) (t0 + 1) ch) :
    Majority (x[k][vp].view) (x[k][vp].view) (t0 + 1) ch := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  have hexp : Q.slotLength * (t0 + 1) = Q.slotLength * t0 + Q.slotLength := Nat.mul_succ ..
  have htj : x[j].time = Q.slotLength * (t0 + 1) + Q.delta := tick_reading hsync hj
  have hAwk : x.Awake k vp := by
    have hstep := x.step k
    rw [hk] at hstep
    have h := hstep.1
    simp only [spec] at h
    exact h
  have hAwj : x.Awake j vi := by
    have hstep := x.step j
    rw [hj] at hstep
    have h := hstep.1
    simp only [spec] at h
    exact h
  have hVp_sub : ∀ m, m ∈ x[k][vp].view → m ∈ x[j][vi].view := by
    intro m hm
    refine hrel k j vp vi m hAwk hm ?_ hAwj
    rw [htk, htj]
    omega
  have hfz_sub : ∀ m, m ∈ x[im][vi].view → m ∈ x[k][vp].view := by
    intro m hm
    refine hsyn im k vp m (views_sound x im vi m hm) ?_ hAwk
    rw [htim, htk]
    omega
  -- peeling chains for the voter's-side filter facts
  have peel_j : votesFor (x[j][vi].view) ch (t0 + 1) ⊆ filEq (x[j][vi].view) := by
    intro sm hsm
    exact Finset.filter_subset _ _ (Finset.filter_subset _ _ (Finset.filter_subset _ _ hsm))
  have peel1_j : votesFor (x[j][vi].view) ch (t0 + 1)
      ⊆ fil1Exp (filEq (x[j][vi].view)) (t0 + 1) := by
    intro sm hsm
    exact Finset.filter_subset _ _ (Finset.filter_subset _ _ hsm)
  -- the numerator transfers
  have hnum : (votesFor (x[im][vi].view) ch (t0 + 1) ∩ votesFor (x[j][vi].view) ch (t0 + 1))
      ⊆ votesFor (x[k][vp].view) ch (t0 + 1) := by
    intro sm hsm
    obtain ⟨hsm1, hsm2⟩ := Finset.mem_inter.mp hsm
    have hv_im : sm ∈ votes (x[im][vi].view) := votesFor_subset_votes _ ch (t0 + 1) hsm1
    have hview_im : sm ∈ x[im][vi].view := by
      simp only [votes, Finset.mem_filter] at hv_im
      exact hv_im.1
    obtain ⟨e', src', tgt', s', hm'⟩ := exists_vote_of_mem_votes hv_im
    have hvv_p : sm ∈ votes (x[k][vp].view) := by
      simp only [votes, Finset.mem_filter]
      refine ⟨hfz_sub sm hview_im, ?_⟩
      rw [hm']
      trivial
    have hslot_j : t0 + 1 = msgSlot sm.msg + 1 :=
      (Finset.mem_filter.mp (peel1_j hsm2)).2
    have hfeq_p : sm ∈ filEq (x[k][vp].view) := by
      simp only [filEq, Finset.mem_filter]
      refine ⟨hvv_p, ?_⟩
      rintro ⟨sm', hsm'v, hsend', hslot', hne⟩
      have hsm'j : sm' ∈ votes (x[j][vi].view) := by
        simp only [votes, Finset.mem_filter] at hsm'v ⊢
        exact ⟨hVp_sub sm' hsm'v.1, hsm'v.2⟩
      have hfeq_j := (Finset.mem_filter.mp (peel_j hsm2)).2
      exact hfeq_j ⟨sm', hsm'j, hsend', hslot', hne⟩
    have hexp_p : sm ∈ fil1Exp (filEq (x[k][vp].view)) (t0 + 1) := by
      simp only [fil1Exp, Finset.mem_filter]
      exact ⟨hfeq_p, hslot_j⟩
    have hflmd_p : sm ∈ filLmd (fil1Exp (filEq (x[k][vp].view)) (t0 + 1)) := by
      simp only [filLmd, Finset.mem_filter]
      refine ⟨hexp_p, ?_⟩
      rintro ⟨sm'', hsm'', -, hlt⟩
      have h2 : t0 + 1 = msgSlot sm''.msg + 1 := (Finset.mem_filter.mp hsm'').2
      omega
    simp only [votesFor, Finset.mem_filter]
    exact ⟨hflmd_p, votesFor_extends hsm1⟩
  -- the denominator transfers the other way
  have hden : voters (x[k][vp].view) (t0 + 1) ⊆ voters (x[j][vi].view) (t0 + 1) := by
    intro q hq
    simp only [voters, Finset.mem_image] at hq ⊢
    obtain ⟨sm, hsm, rfl⟩ := hq
    refine ⟨sm, ?_, rfl⟩
    simp only [fil1Exp, Finset.mem_filter] at hsm ⊢
    refine ⟨?_, hsm.2⟩
    have hsv := hsm.1
    simp only [votes, Finset.mem_filter] at hsv ⊢
    exact ⟨hVp_sub sm hsv.1, hsv.2⟩
  -- counting
  show (voters (x[k][vp].view) (t0 + 1)).card < 2 * _
  have h1 := Finset.card_le_card hden
  have h2 := Finset.card_le_card (Finset.image_subset_image (f := SignedMsg.sender) hnum)
  have hm' : (voters (x[j][vi].view) (t0 + 1)).card < 2 *
      ((votesFor (x[im][vi].view) ch (t0 + 1) ∩
        votesFor (x[j][vi].view) ch (t0 + 1)).image SignedMsg.sender).card := hmaj
  rw [Finset.inter_self]
  omega

/-- **Active validators vote for whatever their fork-choice extends**: if at every vote
    tick of every slot-`t+1` active the fork-choice output extends `ch`, then every such
    validator sends a slot-`t+1` vote extending `ch`. The production machinery — the tick
    exists (`TimeDiverges` + `Diligent`), the joining check is open, the sent chain
    extends the fork-choice — shared by Lemma 2 and Lemma 3. -/
theorem activeVotesExtend_of_le_mfc {x : Exec Pr2 S}
    (hsync : SynchronizedClocks x) (hstepw : TimeStepwise x) (hdiv : TimeDiverges x)
    (hdil : Diligent x) {t : Nat} {ch : Chain Tx}
    (hmfc : ∀ p ∈ Active Q S ((t : Int) + 1), ∀ j : Nat,
      x.lbl j = .tick p (Q.slotLength * (t + 1) + Q.delta) →
      chainLe ch
        (mfc (processProposals2 n proposer (x[j][p].view) (t + 1) (x[j][p].st)).vFrozen
          (x[j][p].view)
          (processProposals2 n proposer (x[j][p].view) (t + 1) (x[j][p].st)).chFrozen (t + 1))) :
    ActiveVotesExtend2 x (t + 1) ch := by
  intro p hp0
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  have hmono := hstepw.timeMonotone
  have hvot1 : Q.voting ((t : Int) + 1)
      = ((Q.slotLength * (t + 1) + Q.delta : Nat) : Int) := by
    unfold Params.voting
    push_cast
    omega
  have hp : p ∈ Active Q S ((t : Int) + 1) := by
    have hcast : (((t + 1 : Nat)) : Int) = (t : Int) + 1 := by push_cast; omega
    rw [← hcast]
    exact hp0
  obtain ⟨i₁, hi₁⟩ := hdiv (Q.slotLength * (t + 1) + Q.delta)
  obtain ⟨i₀, hi₀, hti₀⟩ := exists_time_eq hstepw hi₁
  have hAw0 : x.Awake i₀ p := by
    show p ∈ S.awake ((x[i₀].time : Int))
    rw [hti₀]
    refine mem_awakeThroughout.mp hp _ ?_ ?_ <;> rw [hvot1] <;> omega
  obtain ⟨j, htj, hlblj⟩ := hdil (Q.slotLength * (t + 1) + Q.delta) p ⟨i₀, hti₀, hAw0⟩
  have hgate : x[j][p].st.activeAt ≤ Q.slotLength * (t + 1) + Q.delta := by
    refine activeAt_le_voting hsync hmono (t1 := t + 1) ?_ (le_of_eq htj)
    intro r h1 h2
    refine mem_awakeThroughout.mp hp _ ?_ ?_ <;> rw [hvot1] <;> omega
  obtain ⟨dotj, -, hemit⟩ := tick_effect hlblj
  obtain ⟨chS, hsend, hchS⟩ :=
    handler2_vote_send (Q := Q) (n := n) (kappa := kappa) (pool := pool)
      (proposer := proposer) (dot := dotj) (p := p) (V := x[j][p].view) (s := x[j][p].st)
      (voting_reading_mod Q (t + 1)) hgate
  rw [voting_reading_div Q (t + 1)] at hsend hchS
  have hchain : chainLe ch chS := chainLe_trans (hmfc p hp j hlblj) hchS
  have hmem : ⟪vote, chS, dotj, dotj, (t + 1), p⟫ ∈ x[j + 1].sent := by
    refine hemit _ ?_
    rw [hsend]
    exact Multiset.mem_singleton_self _
  exact ⟨j + 1, chS, dotj, dotj, by rw [tick_time hlblj, htj], hmem, hchain⟩

/-- `activeVotesExtend_of_le_mfc`, slot-generic: the production works at any slot,
    including `0`. -/
theorem activeVotesExtend_of_le_mfc' {x : Exec Pr2 S}
    (hsync : SynchronizedClocks x) (hstepw : TimeStepwise x) (hdiv : TimeDiverges x)
    (hdil : Diligent x) {u : Nat} {ch : Chain Tx}
    (hmfc : ∀ p ∈ Active Q S ((u : Nat) : Int), ∀ j : Nat,
      x.lbl j = .tick p (Q.slotLength * u + Q.delta) →
      chainLe ch
        (mfc (processProposals2 n proposer (x[j][p].view) u (x[j][p].st)).vFrozen
          (x[j][p].view)
          (processProposals2 n proposer (x[j][p].view) u (x[j][p].st)).chFrozen u)) :
    ActiveVotesExtend2 x u ch := by
  intro p hp
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  have hmono := hstepw.timeMonotone
  have hvotu : Q.voting ((u : Nat) : Int)
      = ((Q.slotLength * u + Q.delta : Nat) : Int) := by
    unfold Params.voting
    push_cast
    omega
  obtain ⟨i₁, hi₁⟩ := hdiv (Q.slotLength * u + Q.delta)
  obtain ⟨i₀, hi₀, hti₀⟩ := exists_time_eq hstepw hi₁
  have hAw0 : x.Awake i₀ p := by
    show p ∈ S.awake ((x[i₀].time : Int))
    rw [hti₀]
    refine mem_awakeThroughout.mp hp _ ?_ ?_ <;> rw [hvotu] <;> omega
  obtain ⟨j, htj, hlblj⟩ := hdil (Q.slotLength * u + Q.delta) p ⟨i₀, hti₀, hAw0⟩
  have hgate : x[j][p].st.activeAt ≤ Q.slotLength * u + Q.delta := by
    refine activeAt_le_voting hsync hmono (t1 := u) ?_ (le_of_eq htj)
    intro r h1 h2
    refine mem_awakeThroughout.mp hp _ ?_ ?_ <;> rw [hvotu] <;> omega
  obtain ⟨dotj, -, hemit⟩ := tick_effect hlblj
  obtain ⟨chS, hsend, hchS⟩ :=
    handler2_vote_send (Q := Q) (n := n) (kappa := kappa) (pool := pool)
      (proposer := proposer) (dot := dotj) (p := p) (V := x[j][p].view) (s := x[j][p].st)
      (voting_reading_mod Q u) hgate
  rw [voting_reading_div Q u] at hsend hchS
  have hchain : chainLe ch chS := chainLe_trans (hmfc p hp j hlblj) hchS
  have hmem : ⟪vote, chS, dotj, dotj, u, p⟫ ∈ x[j + 1].sent := by
    refine hemit _ ?_
    rw [hsend]
    exact Multiset.mem_singleton_self _
  exact ⟨j + 1, chS, dotj, dotj, by rw [tick_time hlblj, htj], hmem, hchain⟩

set_option maxHeartbeats 4000000 in
/-- **The honest-chain invariant**: every honest vote in the log carries a slot-sorted
    chain whose head slot is at most the vote's slot. The paper's chain model — blocks in
    slot order — recovered as an execution invariant, by strong induction on the log
    index: a vote's chain is a structurally-checked proposal or the tick's fork-choice,
    and every fork-choice output is genesis or a prefix of some *earlier* honest vote's
    chain — through the frozen fast confirmation, the certificate check, or the majority
    (whose supporters cannot all be corrupt: Constraint (1), and actives do vote). -/
theorem honest_vote_chain {x : Exec Pr2 S}
    (hsync : SynchronizedClocks x) (hstepw : TimeStepwise x) (hdiv : TimeDiverges x)
    (hdil : Diligent x) (hone : OneTickPerReading x) (hwpt : WakePrecedesTick x)
    (hmc : S.MonotoneCorruption) (hsyn : Synchrony 0 Q.delta x) (hslp : Sleepiness Q S)
    (hcb : S.CorruptionBounded Q.f) (hfn : 3 * Q.f < n) (hcard : Fintype.card Node ≤ n)
    (hgst : Q.gst = 0) :
    ∀ (k : Nat) (sm : SignedMsg Node (Msg (Chain Tx) (QCert Node Tx)))
      (e : Chain Tx) (src tgt : Checkpoint (Chain Tx)) (s : Nat),
      sm ∈ x[k].sent → sm.sender ∉ S.adv ((x[k].time : Int)) →
      sm.msg = .vote e src tgt s → slotsIncreasing e ∧ proposedAt e ≤ s := by
  have hmono := hstepw.timeMonotone
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
  intro sm e src tgt s hmem hhon hmsg
  obtain ⟨j, hjk, hlblj, htj, -, hem⟩ := vote_provenance2 hsync hmc hmono hmem hhon hmsg
  have hhonj : sm.sender ∉ S.adv ((x[j].time : Int)) := fun had =>
    hhon (hmc _ _ (by exact_mod_cast time_le_of_le hmono (le_of_lt hjk)) had)
  have hAwj : x.Awake j sm.sender := by
    have hstep := x.step j
    rw [hlblj] at hstep
    have h := hstep.1
    simp only [spec] at h
    exact h
  obtain ⟨dt, -, hsend⟩ := tick_delta_send hlblj hem
  have hcontent := handler2_vote_content (voting_reading_mod Q s) hsend
  rw [voting_reading_div Q s, hmsg] at hcontent
  injection hcontent with hE hsrc htgt hslot
  subst hE
  set chMFC := mfc (processProposals2 n proposer (x[j][sm.sender].view) s
      (x[j][sm.sender].st)).vFrozen (x[j][sm.sender].view)
    (processProposals2 n proposer (x[j][sm.sender].view) s
      (x[j][sm.sender].st)).chFrozen s with hMFCdef
  clear_value chMFC
  -- prefixes of earlier honest votes' chains at slots `≤ s` are fine
  have hprefix_ok : ∀ (i' : Nat) (sm' : SignedMsg Node (Msg (Chain Tx) (QCert Node Tx)))
      (s' : Nat), i' < k → sm' ∈ x[i'].sent → sm'.sender ∉ S.adv ((x[i'].time : Int)) →
      (∃ e' src' tgt', sm'.msg = .vote e' src' tgt' s') → s' ≤ s →
      ∀ c : Chain Tx, chainLe c (msgChain sm'.msg) →
      slotsIncreasing c ∧ proposedAt c ≤ s := by
    intro i' sm' s' hi' hmem' hhon' hshape' hs' c hc
    obtain ⟨e', src', tgt', hm'⟩ := hshape'
    obtain ⟨hok, hle⟩ := IH i' hi' sm' e' src' tgt' s' hmem' hhon' hm'
    have hch : msgChain sm'.msg = e' := by rw [hm']; exact rfl
    rw [hch] at hc
    refine ⟨slotsIncreasing_of_prefix hc hok, ?_⟩
    have := proposedAt_le_of_prefix hc hok
    omega
  -- the fork-choice output is fine
  have hMFCok : slotsIncreasing chMFC ∧ proposedAt chMFC ≤ s := by
    rcases mfc_base_or_majority (processProposals2 n proposer (x[j][sm.sender].view) s
        (x[j][sm.sender].st)).vFrozen (x[j][sm.sender].view)
        (processProposals2 n proposer (x[j][sm.sender].view) s
          (x[j][sm.sender].st)).chFrozen s with hb | hmaj
    · -- base: the processed frozen chain
      rw [← hMFCdef] at hb
      rw [hb]
      rcases processProposals2_chFrozen (n := n) (x[j][sm.sender].view) s
          (x[j][sm.sender].st)
        with hfz | ⟨sm', hsm'V, ⟨chp', qc', ck', hsm'msg⟩, hsm'valid⟩
      · rw [hfz]
        cases s with
        | zero =>
            rw [chFrozen_at_slot0_tick hsync hstepw hone hlblj]
            exact ⟨slotsIncreasing_nil, by simp [proposedAt]⟩
        | succ s0 =>
            have hp' : sm.sender ∈ Active Q S ((s0 : Int) + 1) := by
              have hact := mem_active_of_honest_vote2 hsync hstepw hdil hwpt hmc
                (by omega) hmem hhon hmsg
              have hcast : (((s0 + 1 : Nat)) : Int) = (s0 : Int) + 1 := by
                push_cast; omega
              rw [← hcast]
              exact hact
            obtain ⟨im, himj, htim, -, hcfj⟩ :=
              frozen_at_vote_tick hsync hstepw hdil hone hp' hlblj
            rw [hcfj]
            rcases fastConfirmSimple_fst_cases (n := n) (x[im][sm.sender].view) s0
              with h0 | hsupp
            · rw [h0]
              exact ⟨slotsIncreasing_nil, by simp [proposedAt]⟩
            · obtain ⟨q0, hq0mem, hq0hon⟩ :=
                exists_honest_sender (r := ((x[im].time : Int))) hcb hfn hsupp
              obtain ⟨sm'', hsm'', hs''⟩ := Finset.mem_image.mp hq0mem
              rw [Finset.mem_filter] at hsm''
              obtain ⟨hv'', hslot'', hch''⟩ := hsm''
              have hlog'' : sm'' ∈ x[im].sent :=
                views_sound x im sm.sender _
                  (by simp only [votes, Finset.mem_filter] at hv''; exact hv''.1)
              have hhon'' : sm''.sender ∉ S.adv ((x[im].time : Int)) := by
                rw [hs'']
                exact hq0hon
              obtain ⟨e'', s1'', t1'', s2'', hm''⟩ := exists_vote_of_mem_votes hv''
              have hs2 : s2'' = s0 := by
                have e2 : msgSlot sm''.msg = s2'' := by rw [hm'']; exact rfl
                omega
              subst hs2
              exact hprefix_ok im sm'' s2'' (by omega) hlog'' hhon''
                ⟨e'', s1'', t1'', hm''⟩ (by omega) _ hch''
      · -- overwritten by a certificate-checked proposal
        obtain ⟨sd', m0'⟩ := sm'
        have hm0' : m0' = Msg.propose chp'
            ((processProposals2 n proposer (x[j][sm.sender].view) s
              (x[j][sm.sender].st)).chFrozen) qc' ck' s := hsm'msg
        subst hm0'
        have hvp' : sd' = proposer s ∧ proposedAt chp' = s ∧
            chainLe ((processProposals2 n proposer (x[j][sm.sender].view) s
              (x[j][sm.sender].st)).chFrozen) chp' ∧
            (((processProposals2 n proposer (x[j][sm.sender].view) s
              (x[j][sm.sender].st)).chFrozen) = [] ∨
              ∃ cert : QCert Node Tx, qc' = some cert ∧
                2 * n ≤ 3 * (cert.image Prod.fst).card ∧
                ∀ ent ∈ cert, chainLe ((processProposals2 n proposer
                    (x[j][sm.sender].view) s (x[j][sm.sender].st)).chFrozen) ent.2.1 ∧
                  ent.2.2 = s - 1 ∧
                  ∃ src' tgt' : Checkpoint (Chain Tx),
                    (⟨ent.1, Msg.vote ent.2.1 src' tgt' ent.2.2⟩ :
                      SignedMsg Node (Msg (Chain Tx) (QCert Node Tx)))
                      ∈ x[j][sm.sender].view) := hsm'valid
        rcases hvp'.2.2.2 with hgen0 | ⟨cert, -, hcert_card, hcert⟩
        · rw [hgen0]
          exact ⟨slotsIncreasing_nil, by simp [proposedAt]⟩
        · obtain ⟨q0, hq0mem, hq0hon⟩ :=
            exists_honest_sender (r := ((x[j].time : Int))) hcb hfn hcert_card
          obtain ⟨ent, hent, hfst⟩ := Finset.mem_image.mp hq0mem
          obtain ⟨hchC', hslotE, srcE, tgtE, hinV⟩ := hcert ent hent
          have hlogE : (⟨ent.1, Msg.vote ent.2.1 srcE tgtE ent.2.2⟩ :
              SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ x[j].sent :=
            views_sound x j sm.sender _ hinV
          have hhonE : ent.1 ∉ S.adv ((x[j].time : Int)) := by
            rw [hfst]
            exact hq0hon
          exact hprefix_ok j _ ent.2.2 hjk hlogE hhonE ⟨ent.2.1, srcE, tgtE, rfl⟩
            (by omega) _ hchC'
    · -- majority
      rw [← hMFCdef] at hmaj
      cases s with
      | zero =>
          exfalso
          have hempty : (votesFor ((processProposals2 n proposer
              (x[j][sm.sender].view) 0 (x[j][sm.sender].st)).vFrozen) chMFC 0 ∩
                votesFor (x[j][sm.sender].view) chMFC 0) = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]
            intro sm' hsm'
            have h1 := (Finset.mem_inter.mp hsm').1
            have h2 : sm' ∈ fil1Exp (filEq ((processProposals2 n proposer
                (x[j][sm.sender].view) 0 (x[j][sm.sender].st)).vFrozen)) 0 :=
              Finset.filter_subset _ _ (Finset.filter_subset _ _ h1)
            have h3 := (Finset.mem_filter.mp h2).2
            omega
          have hm2 : (voters (x[j][sm.sender].view) 0).card
              < 2 * ((votesFor ((processProposals2 n proposer (x[j][sm.sender].view) 0
                (x[j][sm.sender].st)).vFrozen) chMFC 0 ∩
              votesFor (x[j][sm.sender].view) chMFC 0).image SignedMsg.sender).card :=
            hmaj
          rw [hempty] at hm2
          simp at hm2
      | succ s0 =>
          have hp' : sm.sender ∈ Active Q S ((s0 : Int) + 1) := by
            have hact := mem_active_of_honest_vote2 hsync hstepw hdil hwpt hmc
              (by omega) hmem hhon hmsg
            have hcast : (((s0 + 1 : Nat)) : Int) = (s0 : Int) + 1 := by push_cast; omega
            rw [← hcast]
            exact hact
          obtain ⟨im, himj, htim, hvfj, -⟩ :=
            frozen_at_vote_tick hsync hstepw hdil hone hp' hlblj
          have hvf : (processProposals2 n proposer (x[j][sm.sender].view) (s0 + 1)
              (x[j][sm.sender].st)).vFrozen = x[im][sm.sender].view := by
            rw [processProposals2_vFrozen]
            exact hvfj
          rw [hvf] at hmaj
          have hvot1 : Q.voting ((s0 : Int) + 1)
              = ((Q.slotLength * (s0 + 1) + Q.delta : Nat) : Int) := by
            unfold Params.voting
            push_cast
            omega
          -- actives voted, and their votes reached this view
          have hAVE : ActiveVotesExtend2 x s0 ([] : Chain Tx) :=
            activeVotesExtend_of_le_mfc' hsync hstepw hdiv hdil
              (fun p hp j' hj' => chainLe_nil _)
          have hsubS : Active Q S (s0 : Int) \ S.adv (Q.voting ((s0 : Int) + 1)) ⊆
              voters (x[j][sm.sender].view) (s0 + 1) := by
            intro w hw
            obtain ⟨hwA, -⟩ := Finset.mem_sdiff.mp hw
            obtain ⟨iv, ev, evsrc, evtgt, htiv, hsentv, -⟩ := hAVE w hwA
            have hview : (⟨w, Msg.vote ev evsrc evtgt s0⟩ :
                SignedMsg Node (Msg (Chain Tx) (QCert Node Tx)))
                ∈ x[j][sm.sender].view := by
              refine hsyn iv j sm.sender _ hsentv ?_ hAwj
              rw [htiv, htj]
              have hexp : Q.slotLength * (s0 + 1)
                  = Q.slotLength * s0 + Q.slotLength := Nat.mul_succ ..
              omega
            simp only [voters, Finset.mem_image]
            refine ⟨⟨w, Msg.vote ev evsrc evtgt s0⟩, ?_, rfl⟩
            simp only [fil1Exp, Finset.mem_filter]
            refine ⟨?_, rfl⟩
            simp only [votes, Finset.mem_filter]
            exact ⟨hview, trivial⟩
          -- the supporters cannot all be corrupt
          obtain ⟨q0, hq0mem, hq0hon⟩ : ∃ q0 ∈ ((votesFor (x[im][sm.sender].view) chMFC
              (s0 + 1) ∩ votesFor (x[j][sm.sender].view) chMFC (s0 + 1)).image
                SignedMsg.sender), q0 ∉ S.adv (Q.voting ((s0 : Int) + 1)) := by
            by_contra hno
            have hsubA : ((votesFor (x[im][sm.sender].view) chMFC (s0 + 1) ∩
                votesFor (x[j][sm.sender].view) chMFC (s0 + 1)).image
                  SignedMsg.sender) ⊆ S.adv (Q.voting ((s0 : Int) + 1)) := by
              intro q hq
              by_contra hq'
              exact hno ⟨q, hq, hq'⟩
            have himgvoters : ((votesFor (x[im][sm.sender].view) chMFC (s0 + 1) ∩
                votesFor (x[j][sm.sender].view) chMFC (s0 + 1)).image
                  SignedMsg.sender) ⊆ voters (x[j][sm.sender].view) (s0 + 1) := by
              intro q hq
              obtain ⟨smq, hsmq, rfl⟩ := Finset.mem_image.mp hq
              exact sender_mem_voters_of_votesFor (Finset.mem_inter.mp hsmq).2
            have hdisj : Disjoint (Active Q S (s0 : Int) \
                S.adv (Q.voting ((s0 : Int) + 1)))
                ((votesFor (x[im][sm.sender].view) chMFC (s0 + 1) ∩
                  votesFor (x[j][sm.sender].view) chMFC (s0 + 1)).image
                    SignedMsg.sender) := by
              rw [Finset.disjoint_left]
              intro q hq1 hq2
              exact (Finset.mem_sdiff.mp hq1).2 (hsubA hq2)
            have hunion := Finset.card_le_card
              (Finset.union_subset hsubS himgvoters)
            rw [Finset.card_union_of_disjoint hdisj] at hunion
            have hgstok : (Q.gst : Int) ≤ Q.proposing ((s0 : Int) + 1) := by
              rw [hgst]
              unfold Params.proposing
              push_cast
              exact mul_nonneg (Int.natCast_nonneg _) (by omega)
            have hslp' : (S.adv (Q.voting ((s0 : Int) + 1))).card <
                (Active Q S (s0 : Int) \ S.adv (Q.voting ((s0 : Int) + 1))).card := by
              have h := hslp ((s0 : Int) + 1) hgstok
              simpa using h
            have himgA := Finset.card_le_card hsubA
            have hm2 : (voters (x[j][sm.sender].view) (s0 + 1)).card
                < 2 * ((votesFor (x[im][sm.sender].view) chMFC (s0 + 1) ∩
                  votesFor (x[j][sm.sender].view) chMFC (s0 + 1)).image
                    SignedMsg.sender).card := hmaj
            omega
          obtain ⟨smq, hsmq, hs0q⟩ := Finset.mem_image.mp hq0mem
          have hsmq1 := (Finset.mem_inter.mp hsmq).1
          have hv1 : smq ∈ votes (x[im][sm.sender].view) :=
            votesFor_subset_votes _ chMFC (s0 + 1) hsmq1
          have hlogq : smq ∈ x[im].sent :=
            views_sound x im sm.sender _
              (by simp only [votes, Finset.mem_filter] at hv1; exact hv1.1)
          have hhonq : smq.sender ∉ S.adv ((x[im].time : Int)) := by
            intro had
            refine hq0hon ?_
            rw [← hs0q]
            refine hmc _ _ ?_ had
            rw [htim, hvot1]
            have hexp : Q.slotLength * (s0 + 1)
                = Q.slotLength * s0 + Q.slotLength := Nat.mul_succ ..
            exact_mod_cast (by omega : Q.slotLength * s0 + 3 * Q.delta ≤
              Q.slotLength * (s0 + 1) + Q.delta)
          obtain ⟨eq', sq1, tq1, sq2, hmq⟩ := exists_vote_of_mem_votes hv1
          have hsq : sq2 = s0 := by
            have h1 : smq ∈ fil1Exp (filEq (x[im][sm.sender].view)) (s0 + 1) :=
              Finset.filter_subset _ _ (Finset.filter_subset _ _ hsmq1)
            have h2 := (Finset.mem_filter.mp h1).2
            have e2 : msgSlot smq.msg = sq2 := by rw [hmq]; exact rfl
            omega
          subst hsq
          exact hprefix_ok im smq sq2 (by omega) hlogq hhonq ⟨eq', sq1, tq1, hmq⟩
            (by omega) _ (votesFor_extends hsmq1)
  -- the vote itself: a checked proposal, or the fork-choice
  rw [voteChoice]
  cases hfind : (x[j][sm.sender].view).toList.findSome? (fun sm' => match sm'.msg with
      | .propose chp' _ _ _ t' =>
          if sm'.sender == proposer s && t' == s && proposedAt chp' == s &&
              slotsIncreasing chp' && chainLe chMFC chp' then some chp'
          else none
      | .vote .. => none) with
  | none =>
      simpa using hMFCok
  | some c =>
      simp only [Option.getD_some]
      obtain ⟨a, -, hfa⟩ := List.exists_of_findSome?_eq_some hfind
      obtain ⟨asd, am⟩ := a
      revert hfa
      cases am with
      | vote e1 s1 t1 sl1 => intro h; cases h
      | propose chpa chca qca cka ta =>
          dsimp only
          split_ifs with hcnd
          · intro h
            injection h with h
            subst h
            simp only [Bool.and_eq_true, beq_iff_eq] at hcnd
            exact ⟨hcnd.1.2, le_of_eq hcnd.1.1.2⟩
          · intro h
            cases h

set_option maxHeartbeats 3000000 in
/-- **The vote-round fork choice is structurally sound**: at a vote tick of a validator
    active in its slot, the processed fork-choice output is slot-sorted with `proposedAt`
    at most the *previous* slot. Every path is bounded by an honest previous-slot vote's
    chain and closed by `honest_vote_chain`: the base is genesis or the frozen fast
    confirmation (quorum → honest supporter) possibly overwritten by a certificate-checked
    chain (certificate → honest voter), and a majority has an honest supporter by
    Constraint (1). Lemma 5's `κ`-absorption arithmetic rests on this bound. -/
theorem mfc_vote_ok {x : Exec Pr2 S}
    (hsync : SynchronizedClocks x) (hstepw : TimeStepwise x) (hdiv : TimeDiverges x)
    (hdil : Diligent x) (hone : OneTickPerReading x) (hwpt : WakePrecedesTick x)
    (hmc : S.MonotoneCorruption) (hsyn : Synchrony 0 Q.delta x) (hslp : Sleepiness Q S)
    (hcb : S.CorruptionBounded Q.f) (hfn : 3 * Q.f < n) (hcard : Fintype.card Node ≤ n)
    (hgst : Q.gst = 0) {p : Node} {s : Nat}
    (hp : 1 ≤ s → p ∈ Active Q S (s : Int))
    {j : Nat} (hj : x.lbl j = .tick p (Q.slotLength * s + Q.delta)) :
    slotsIncreasing (mfc (processProposals2 n proposer (x[j][p].view) s
        (x[j][p].st)).vFrozen (x[j][p].view)
      (processProposals2 n proposer (x[j][p].view) s (x[j][p].st)).chFrozen s) ∧
    proposedAt (mfc (processProposals2 n proposer (x[j][p].view) s
        (x[j][p].st)).vFrozen (x[j][p].view)
      (processProposals2 n proposer (x[j][p].view) s (x[j][p].st)).chFrozen s)
      ≤ s - 1 := by
  have hmono := hstepw.timeMonotone
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  have htj : x[j].time = Q.slotLength * s + Q.delta := tick_reading hsync hj
  have hAwj : x.Awake j p := by
    have hstep := x.step j
    rw [hj] at hstep
    have h := hstep.1
    simp only [spec] at h
    exact h
  have hinv := honest_vote_chain hsync hstepw hdiv hdil hone hwpt hmc hsyn hslp hcb hfn
    hcard hgst
  set chMFC := mfc (processProposals2 n proposer (x[j][p].view) s
      (x[j][p].st)).vFrozen (x[j][p].view)
    (processProposals2 n proposer (x[j][p].view) s
      (x[j][p].st)).chFrozen s with hMFCdef
  clear_value chMFC
  -- prefixes of honest votes' chains at slots `≤ s - 1` are fine
  have hprefix_ok : ∀ (i' : Nat) (sm' : SignedMsg Node (Msg (Chain Tx) (QCert Node Tx)))
      (s' : Nat), sm' ∈ x[i'].sent → sm'.sender ∉ S.adv ((x[i'].time : Int)) →
      (∃ e' src' tgt', sm'.msg = .vote e' src' tgt' s') → s' ≤ s - 1 →
      ∀ c : Chain Tx, chainLe c (msgChain sm'.msg) →
      slotsIncreasing c ∧ proposedAt c ≤ s - 1 := by
    intro i' sm' s' hmem' hhon' hshape' hs' c hc
    obtain ⟨e', src', tgt', hm'⟩ := hshape'
    obtain ⟨hok, hle⟩ := hinv i' sm' e' src' tgt' s' hmem' hhon' hm'
    have hch : msgChain sm'.msg = e' := by rw [hm']; exact rfl
    rw [hch] at hc
    refine ⟨slotsIncreasing_of_prefix hc hok, ?_⟩
    have := proposedAt_le_of_prefix hc hok
    omega
  rcases mfc_base_or_majority (processProposals2 n proposer (x[j][p].view) s
      (x[j][p].st)).vFrozen (x[j][p].view)
      (processProposals2 n proposer (x[j][p].view) s
        (x[j][p].st)).chFrozen s with hb | hmaj
  · -- base: the processed frozen chain
    rw [← hMFCdef] at hb
    rw [hb]
    rcases processProposals2_chFrozen (n := n) (x[j][p].view) s (x[j][p].st)
      with hfz | ⟨sm', hsm'V, ⟨chp', qc', ck', hsm'msg⟩, hsm'valid⟩
    · rw [hfz]
      cases s with
      | zero =>
          rw [chFrozen_at_slot0_tick hsync hstepw hone hj]
          exact ⟨slotsIncreasing_nil, by simp [proposedAt]⟩
      | succ s0 =>
          have hp' : p ∈ Active Q S ((s0 : Int) + 1) := by
            have hcast : (((s0 + 1 : Nat)) : Int) = (s0 : Int) + 1 := by
              push_cast; omega
            rw [← hcast]
            exact hp (by omega)
          obtain ⟨im, himj, htim, -, hcfj⟩ :=
            frozen_at_vote_tick hsync hstepw hdil hone hp' hj
          rw [hcfj]
          rcases fastConfirmSimple_fst_cases (n := n) (x[im][p].view) s0
            with h0 | hsupp
          · rw [h0]
            exact ⟨slotsIncreasing_nil, by simp [proposedAt]⟩
          · obtain ⟨q0, hq0mem, hq0hon⟩ :=
              exists_honest_sender (r := ((x[im].time : Int))) hcb hfn hsupp
            obtain ⟨sm'', hsm'', hs''⟩ := Finset.mem_image.mp hq0mem
            rw [Finset.mem_filter] at hsm''
            obtain ⟨hv'', hslot'', hch''⟩ := hsm''
            have hlog'' : sm'' ∈ x[im].sent :=
              views_sound x im p _
                (by simp only [votes, Finset.mem_filter] at hv''; exact hv''.1)
            have hhon'' : sm''.sender ∉ S.adv ((x[im].time : Int)) := by
              rw [hs'']
              exact hq0hon
            obtain ⟨e'', s1'', t1'', s2'', hm''⟩ := exists_vote_of_mem_votes hv''
            have hs2 : s2'' = s0 := by
              have e2 : msgSlot sm''.msg = s2'' := by rw [hm'']; exact rfl
              omega
            subst hs2
            exact hprefix_ok im sm'' s2'' hlog'' hhon''
              ⟨e'', s1'', t1'', hm''⟩ (by omega) _ hch''
    · -- overwritten by a certificate-checked proposal
      obtain ⟨sd', m0'⟩ := sm'
      have hm0' : m0' = Msg.propose chp'
          ((processProposals2 n proposer (x[j][p].view) s
            (x[j][p].st)).chFrozen) qc' ck' s := hsm'msg
      subst hm0'
      have hvp' : sd' = proposer s ∧ proposedAt chp' = s ∧
          chainLe ((processProposals2 n proposer (x[j][p].view) s
            (x[j][p].st)).chFrozen) chp' ∧
          (((processProposals2 n proposer (x[j][p].view) s
            (x[j][p].st)).chFrozen) = [] ∨
            ∃ cert : QCert Node Tx, qc' = some cert ∧
              2 * n ≤ 3 * (cert.image Prod.fst).card ∧
              ∀ ent ∈ cert, chainLe ((processProposals2 n proposer
                  (x[j][p].view) s (x[j][p].st)).chFrozen) ent.2.1 ∧
                ent.2.2 = s - 1 ∧
                ∃ src' tgt' : Checkpoint (Chain Tx),
                  (⟨ent.1, Msg.vote ent.2.1 src' tgt' ent.2.2⟩ :
                    SignedMsg Node (Msg (Chain Tx) (QCert Node Tx)))
                    ∈ x[j][p].view) := hsm'valid
      rcases hvp'.2.2.2 with hgen0 | ⟨cert, -, hcert_card, hcert⟩
      · rw [hgen0]
        exact ⟨slotsIncreasing_nil, by simp [proposedAt]⟩
      · obtain ⟨q0, hq0mem, hq0hon⟩ :=
          exists_honest_sender (r := ((x[j].time : Int))) hcb hfn hcert_card
        obtain ⟨ent, hent, hfst⟩ := Finset.mem_image.mp hq0mem
        obtain ⟨hchC', hslotE, srcE, tgtE, hinV⟩ := hcert ent hent
        have hlogE : (⟨ent.1, Msg.vote ent.2.1 srcE tgtE ent.2.2⟩ :
            SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ x[j].sent :=
          views_sound x j p _ hinV
        have hhonE : ent.1 ∉ S.adv ((x[j].time : Int)) := by
          rw [hfst]
          exact hq0hon
        exact hprefix_ok j _ ent.2.2 hlogE hhonE ⟨ent.2.1, srcE, tgtE, rfl⟩
          (by omega) _ hchC'
  · -- majority
    rw [← hMFCdef] at hmaj
    cases s with
    | zero =>
        exfalso
        have hempty : (votesFor ((processProposals2 n proposer
            (x[j][p].view) 0 (x[j][p].st)).vFrozen) chMFC 0 ∩
              votesFor (x[j][p].view) chMFC 0) = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro sm' hsm'
          have h1 := (Finset.mem_inter.mp hsm').1
          have h2 : sm' ∈ fil1Exp (filEq ((processProposals2 n proposer
              (x[j][p].view) 0 (x[j][p].st)).vFrozen)) 0 :=
            Finset.filter_subset _ _ (Finset.filter_subset _ _ h1)
          have h3 := (Finset.mem_filter.mp h2).2
          omega
        have hm2 : (voters (x[j][p].view) 0).card
            < 2 * ((votesFor ((processProposals2 n proposer (x[j][p].view) 0
              (x[j][p].st)).vFrozen) chMFC 0 ∩
            votesFor (x[j][p].view) chMFC 0).image SignedMsg.sender).card :=
          hmaj
        rw [hempty] at hm2
        simp at hm2
    | succ s0 =>
        have hp' : p ∈ Active Q S ((s0 : Int) + 1) := by
          have hcast : (((s0 + 1 : Nat)) : Int) = (s0 : Int) + 1 := by push_cast; omega
          rw [← hcast]
          exact hp (by omega)
        obtain ⟨im, himj, htim, hvfj, -⟩ :=
          frozen_at_vote_tick hsync hstepw hdil hone hp' hj
        have hvf : (processProposals2 n proposer (x[j][p].view) (s0 + 1)
            (x[j][p].st)).vFrozen = x[im][p].view := by
          rw [processProposals2_vFrozen]
          exact hvfj
        rw [hvf] at hmaj
        have hvot1 : Q.voting ((s0 : Int) + 1)
            = ((Q.slotLength * (s0 + 1) + Q.delta : Nat) : Int) := by
          unfold Params.voting
          push_cast
          omega
        -- actives voted, and their votes reached this view
        have hAVE : ActiveVotesExtend2 x s0 ([] : Chain Tx) :=
          activeVotesExtend_of_le_mfc' hsync hstepw hdiv hdil
            (fun w hw j' hj' => chainLe_nil _)
        have hsubS : Active Q S (s0 : Int) \ S.adv (Q.voting ((s0 : Int) + 1)) ⊆
            voters (x[j][p].view) (s0 + 1) := by
          intro w hw
          obtain ⟨hwA, -⟩ := Finset.mem_sdiff.mp hw
          obtain ⟨iv, ev, evsrc, evtgt, htiv, hsentv, -⟩ := hAVE w hwA
          have hview : (⟨w, Msg.vote ev evsrc evtgt s0⟩ :
              SignedMsg Node (Msg (Chain Tx) (QCert Node Tx)))
              ∈ x[j][p].view := by
            refine hsyn iv j p _ hsentv ?_ hAwj
            rw [htiv, htj]
            have hexp : Q.slotLength * (s0 + 1)
                = Q.slotLength * s0 + Q.slotLength := Nat.mul_succ ..
            omega
          simp only [voters, Finset.mem_image]
          refine ⟨⟨w, Msg.vote ev evsrc evtgt s0⟩, ?_, rfl⟩
          simp only [fil1Exp, Finset.mem_filter]
          refine ⟨?_, rfl⟩
          simp only [votes, Finset.mem_filter]
          exact ⟨hview, trivial⟩
        -- the supporters cannot all be corrupt
        obtain ⟨q0, hq0mem, hq0hon⟩ : ∃ q0 ∈ ((votesFor (x[im][p].view) chMFC
            (s0 + 1) ∩ votesFor (x[j][p].view) chMFC (s0 + 1)).image
              SignedMsg.sender), q0 ∉ S.adv (Q.voting ((s0 : Int) + 1)) := by
          by_contra hno
          have hsubA : ((votesFor (x[im][p].view) chMFC (s0 + 1) ∩
              votesFor (x[j][p].view) chMFC (s0 + 1)).image
                SignedMsg.sender) ⊆ S.adv (Q.voting ((s0 : Int) + 1)) := by
            intro q hq
            by_contra hq'
            exact hno ⟨q, hq, hq'⟩
          have himgvoters : ((votesFor (x[im][p].view) chMFC (s0 + 1) ∩
              votesFor (x[j][p].view) chMFC (s0 + 1)).image
                SignedMsg.sender) ⊆ voters (x[j][p].view) (s0 + 1) := by
            intro q hq
            obtain ⟨smq, hsmq, rfl⟩ := Finset.mem_image.mp hq
            exact sender_mem_voters_of_votesFor (Finset.mem_inter.mp hsmq).2
          have hdisj : Disjoint (Active Q S (s0 : Int) \
              S.adv (Q.voting ((s0 : Int) + 1)))
              ((votesFor (x[im][p].view) chMFC (s0 + 1) ∩
                votesFor (x[j][p].view) chMFC (s0 + 1)).image
                  SignedMsg.sender) := by
            rw [Finset.disjoint_left]
            intro q hq1 hq2
            exact (Finset.mem_sdiff.mp hq1).2 (hsubA hq2)
          have hunion := Finset.card_le_card
            (Finset.union_subset hsubS himgvoters)
          rw [Finset.card_union_of_disjoint hdisj] at hunion
          have hgstok : (Q.gst : Int) ≤ Q.proposing ((s0 : Int) + 1) := by
            rw [hgst]
            unfold Params.proposing
            push_cast
            exact mul_nonneg (Int.natCast_nonneg _) (by omega)
          have hslp' : (S.adv (Q.voting ((s0 : Int) + 1))).card <
              (Active Q S (s0 : Int) \ S.adv (Q.voting ((s0 : Int) + 1))).card := by
            have h := hslp ((s0 : Int) + 1) hgstok
            simpa using h
          have himgA := Finset.card_le_card hsubA
          have hm2 : (voters (x[j][p].view) (s0 + 1)).card
              < 2 * ((votesFor (x[im][p].view) chMFC (s0 + 1) ∩
                votesFor (x[j][p].view) chMFC (s0 + 1)).image
                  SignedMsg.sender).card := hmaj
          omega
        obtain ⟨smq, hsmq, hs0q⟩ := Finset.mem_image.mp hq0mem
        have hsmq1 := (Finset.mem_inter.mp hsmq).1
        have hv1 : smq ∈ votes (x[im][p].view) :=
          votesFor_subset_votes _ chMFC (s0 + 1) hsmq1
        have hlogq : smq ∈ x[im].sent :=
          views_sound x im p _
            (by simp only [votes, Finset.mem_filter] at hv1; exact hv1.1)
        have hhonq : smq.sender ∉ S.adv ((x[im].time : Int)) := by
          intro had
          refine hq0hon ?_
          rw [← hs0q]
          refine hmc _ _ ?_ had
          rw [htim, hvot1]
          have hexp : Q.slotLength * (s0 + 1)
              = Q.slotLength * s0 + Q.slotLength := Nat.mul_succ ..
          exact_mod_cast (by omega : Q.slotLength * s0 + 3 * Q.delta ≤
            Q.slotLength * (s0 + 1) + Q.delta)
        obtain ⟨eq', sq1, tq1, sq2, hmq⟩ := exists_vote_of_mem_votes hv1
        have hsq : sq2 = s0 := by
          have h1 : smq ∈ fil1Exp (filEq (x[im][p].view)) (s0 + 1) :=
            Finset.filter_subset _ _ (Finset.filter_subset _ _ hsmq1)
          have h2 := (Finset.mem_filter.mp h1).2
          have e2 : msgSlot smq.msg = sq2 := by rw [hmq]; exact rfl
          omega
        subst hsq
        exact hprefix_ok im smq sq2 hlogq hhonq ⟨eq', sq1, tq1, hmq⟩
          (by omega) _ (votesFor_extends hsmq1)

/-- **The quorum-direct vote-round bound** — Lemma 3's base case, and Lemma 5's
    fast-confirm edge at the very next slot: a `2n/3` quorum for `ch` in any `fconf(t)`
    view reaches every slot-`t+1` active's merge freeze by synchrony, so the frozen fast
    confirmation is at least as long as `ch` and comparable with it, and the vote-round
    fork choice extends its (monotonically processed) base. -/
theorem le_mfc_at_vote_of_quorum {x : Exec Pr2 S}
    (hsync : SynchronizedClocks x) (hstepw : TimeStepwise x)
    (hdil : Diligent x) (hone : OneTickPerReading x) (hmc : S.MonotoneCorruption)
    (hsyn : Synchrony 0 Q.delta x)
    (hcb : S.CorruptionBounded Q.f) (hfn : 3 * Q.f < n)
    (hcard : Fintype.card Node ≤ n)
    {t : Nat} {ch : Chain Tx} {iw : Nat} {w : Node} {cert : QCert Node Tx}
    (htiw : x[iw].time = Q.slotLength * t + 2 * Q.delta)
    (hfc : fastConfirmSimple n (x[iw][w].view) t = (ch, some cert))
    {p : Node} (hp : p ∈ Active Q S ((t : Int) + 1))
    {j : Nat} (hj : x.lbl j = .tick p (Q.slotLength * (t + 1) + Q.delta)) :
    chainLe ch
      (mfc (processProposals2 n proposer (x[j][p].view) (t + 1) (x[j][p].st)).vFrozen
        (x[j][p].view)
        (processProposals2 n proposer (x[j][p].view) (t + 1) (x[j][p].st)).chFrozen
        (t + 1)) := by
  have hmono := hstepw.timeMonotone
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  by_cases hch0 : ch = []
  · subst hch0
    exact chainLe_nil _
  -- the confirming quorum, in the confirmer's view
  have h1 : (fastConfirmSimple n (x[iw][w].view) t).1 = ch := by rw [hfc]
  rcases fastConfirmSimple_fst_cases (n := n) (x[iw][w].view) t with h0 | hsupp
  · rw [h1] at h0
    exact absurd h0 hch0
  rw [h1] at hsupp
  -- the frozen chain entering the vote tick
  obtain ⟨im, himj, htim, -, hcfj⟩ := frozen_at_vote_tick hsync hstepw hdil hone hp hj
  have hvot1 : Q.voting ((t : Int) + 1)
      = ((Q.slotLength * (t + 1) + Q.delta : Nat) : Int) := by
    unfold Params.voting
    push_cast
    omega
  have hexp : Q.slotLength * (t + 1) = Q.slotLength * t + Q.slotLength := Nat.mul_succ ..
  have hAwm : x.Awake im p := by
    show p ∈ S.awake ((x[im].time : Int))
    rw [htim]
    refine mem_awakeThroughout.mp hp _ ?_ ?_ <;> rw [hvot1] <;> omega
  -- the quorum reaches `p`'s merge view
  have hsub : ((votes (x[iw][w].view)).filter (fun sm => msgSlot sm.msg = t ∧
        chainLe ch (msgChain sm.msg))) ⊆
      ((votes (x[im][p].view)).filter (fun sm => msgSlot sm.msg = t ∧
        chainLe ch (msgChain sm.msg))) := by
    intro sm hsm
    rw [Finset.mem_filter] at hsm ⊢
    obtain ⟨hv, hcond⟩ := hsm
    simp only [votes, Finset.mem_filter] at hv ⊢
    refine ⟨⟨?_, hv.2⟩, hcond⟩
    refine hsyn iw im p _ (views_sound x iw w _ hv.1) ?_ hAwm
    rw [htiw, htim]
    omega
  have hsupp2 : 2 * n ≤ 3 * (((votes (x[im][p].view)).filter (fun sm =>
      msgSlot sm.msg = t ∧ chainLe ch (msgChain sm.msg))).image SignedMsg.sender).card := by
    refine le_trans hsupp ?_
    have h3 := Finset.card_le_card (Finset.image_subset_image (f := SignedMsg.sender) hsub)
    omega
  -- `ch` is a candidate there
  have hcand : ch ∈ candidates (x[im][p].view) ([] : Chain Tx) := by
    have hpos : 0 < (((votes (x[im][p].view)).filter (fun sm =>
        msgSlot sm.msg = t ∧ chainLe ch (msgChain sm.msg))).image SignedMsg.sender).card := by
      omega
    rw [Finset.card_pos] at hpos
    obtain ⟨q, hq⟩ := hpos
    obtain ⟨sm, hsm, -⟩ := Finset.mem_image.mp hq
    rw [Finset.mem_filter] at hsm
    exact mem_candidates_of_extends hsm.1 hsm.2.2
  -- so `p`'s frozen fast-confirmation is at least as long as `ch`, and comparable
  have hlen := fastConfirmSimple_length_ge (n := n) hch0 hcand hsupp2
  have hcomp : chainLe ch (fastConfirmSimple n (x[im][p].view) t).1 := by
    rcases fastConfirmSimple_fst_cases (n := n) (x[im][p].view) t with hb0 | hbsupp
    · exfalso
      have hpos : 0 < ch.length := by
        cases ch with
        | nil => exact absurd rfl hch0
        | cons _ _ => simp
      rw [hb0] at hlen
      simp only [List.length_nil] at hlen
      omega
    · exact chainLe_of_comparable _ _
        (supported_comparable hsync hone hmc hmono hcb hfn hcard hsupp2 hbsupp) hlen
  -- through `processProposals2` (monotone) and `mfc` (base)
  have hstep1 : chainLe ch (x[j][p].st).chFrozen := by
    rw [hcfj]
    exact hcomp
  exact chainLe_trans (chainLe_trans hstep1 (processProposals2_chFrozen_mono _ _ _))
    (base_le_mfc _ _ _ _)

/-- **The quorum-direct propose-round bound** — Lemma 5's fast-confirm edge at the next
    slot's propose round: the quorum's votes are in the log by `fconf(t)`, hence in every
    slot-`t+1` active's `propose(t+1)` view, so that tick's own fast confirmation is at
    least as long as `ch` and comparable with it, and the fork choice extends it as its
    base. -/
theorem le_mfc_at_propose_of_quorum {x : Exec Pr2 S}
    (hsync : SynchronizedClocks x) (hstepw : TimeStepwise x)
    (hone : OneTickPerReading x) (hmc : S.MonotoneCorruption)
    (hsyn : Synchrony 0 Q.delta x)
    (hcb : S.CorruptionBounded Q.f) (hfn : 3 * Q.f < n)
    (hcard : Fintype.card Node ≤ n)
    {t : Nat} {ch : Chain Tx} {iw : Nat} {w : Node} {cert : QCert Node Tx}
    (htiw : x[iw].time = Q.slotLength * t + 2 * Q.delta)
    (hfc : fastConfirmSimple n (x[iw][w].view) t = (ch, some cert))
    {b : Nat} (htb : x[b].time = Q.slotLength * (t + 1))
    {vj : Node} (hv : vj ∈ Active Q S ((t : Int) + 1)) :
    chainLe ch (mfc (x[b][vj].view) (x[b][vj].view)
      (fastConfirmSimple n (x[b][vj].view) t).1 (t + 1)) := by
  have hmono := hstepw.timeMonotone
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  by_cases hch0 : ch = []
  · subst hch0
    exact chainLe_nil _
  have h1 : (fastConfirmSimple n (x[iw][w].view) t).1 = ch := by rw [hfc]
  rcases fastConfirmSimple_fst_cases (n := n) (x[iw][w].view) t with h0 | hsupp
  · rw [h1] at h0
    exact absurd h0 hch0
  rw [h1] at hsupp
  have hvot1 : Q.voting ((t : Int) + 1)
      = ((Q.slotLength * (t + 1) + Q.delta : Nat) : Int) := by
    unfold Params.voting
    push_cast
    omega
  have hexp : Q.slotLength * (t + 1) = Q.slotLength * t + Q.slotLength := Nat.mul_succ ..
  have hAwb : x.Awake b vj := by
    show vj ∈ S.awake ((x[b].time : Int))
    rw [htb]
    refine mem_awakeThroughout.mp hv _ ?_ ?_ <;> rw [hvot1] <;> push_cast <;> omega
  have hsub : ((votes (x[iw][w].view)).filter (fun sm => msgSlot sm.msg = t ∧
        chainLe ch (msgChain sm.msg))) ⊆
      ((votes (x[b][vj].view)).filter (fun sm => msgSlot sm.msg = t ∧
        chainLe ch (msgChain sm.msg))) := by
    intro sm hsm
    rw [Finset.mem_filter] at hsm ⊢
    obtain ⟨hvv, hcond⟩ := hsm
    simp only [votes, Finset.mem_filter] at hvv ⊢
    refine ⟨⟨?_, hvv.2⟩, hcond⟩
    refine hsyn iw b vj _ (views_sound x iw w _ hvv.1) ?_ hAwb
    rw [htiw, htb]
    omega
  have hsupp2 : 2 * n ≤ 3 * (((votes (x[b][vj].view)).filter (fun sm =>
      msgSlot sm.msg = t ∧
        chainLe ch (msgChain sm.msg))).image SignedMsg.sender).card := by
    refine le_trans hsupp ?_
    have h3 := Finset.card_le_card
      (Finset.image_subset_image (f := SignedMsg.sender) hsub)
    omega
  have hcand : ch ∈ candidates (x[b][vj].view) ([] : Chain Tx) := by
    have hpos : 0 < (((votes (x[b][vj].view)).filter (fun sm =>
        msgSlot sm.msg = t ∧
          chainLe ch (msgChain sm.msg))).image SignedMsg.sender).card := by
      omega
    rw [Finset.card_pos] at hpos
    obtain ⟨q, hq⟩ := hpos
    obtain ⟨sm, hsm, -⟩ := Finset.mem_image.mp hq
    rw [Finset.mem_filter] at hsm
    exact mem_candidates_of_extends hsm.1 hsm.2.2
  have hlen := fastConfirmSimple_length_ge (n := n) hch0 hcand hsupp2
  have hcomp : chainLe ch (fastConfirmSimple n (x[b][vj].view) t).1 := by
    rcases fastConfirmSimple_fst_cases (n := n) (x[b][vj].view) t with hb0 | hbsupp
    · exfalso
      have hpos : 0 < ch.length := by
        cases ch with
        | nil => exact absurd rfl hch0
        | cons _ _ => simp
      rw [hb0] at hlen
      simp only [List.length_nil] at hlen
      omega
    · exact chainLe_of_comparable _ _
        (supported_comparable hsync hone hmc hmono hcb hfn hcard hsupp2 hbsupp) hlen
  exact chainLe_trans hcomp (base_le_mfc _ _ _ _)

/-- **Lemma 3's base case**: a fast confirmation of `ch` in slot `t` — a `2n/3` quorum in
    any validator's `fconf(t)` view — makes every slot-`t+1` active vote an extension of
    `ch`. No majority argument: the quorum reaches every active's `merge(t)` view by
    synchrony, so its frozen fast-confirmation is at least as long as `ch` and comparable
    with it (quorum intersection), `processProposals2` only extends the frozen chain, and
    the fork-choice extends its base. -/
theorem activeVotesExtend_of_fastconfirm {x : Exec Pr2 S}
    (hsync : SynchronizedClocks x) (hstepw : TimeStepwise x) (hdiv : TimeDiverges x)
    (hdil : Diligent x) (hone : OneTickPerReading x) (hmc : S.MonotoneCorruption)
    (hsyn : Synchrony 0 Q.delta x)
    (hcb : S.CorruptionBounded Q.f) (hfn : 3 * Q.f < n)
    (hcard : Fintype.card Node ≤ n)
    {t : Nat} {ch : Chain Tx} {iw : Nat} {w : Node} {cert : QCert Node Tx}
    (htiw : x[iw].time = Q.slotLength * t + 2 * Q.delta)
    (hfc : fastConfirmSimple n (x[iw][w].view) t = (ch, some cert)) :
    ActiveVotesExtend2 x (t + 1) ch := by
  have hmono := hstepw.timeMonotone
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  refine activeVotesExtend_of_le_mfc hsync hstepw hdiv hdil ?_
  intro p hp j hj
  exact le_mfc_at_vote_of_quorum hsync hstepw hdil hone hmc hsyn hcb hfn hcard
    htiw hfc hp hj

/-- A `none` certificate only comes from the empty branch, whose chain is genesis. -/
theorem fastConfirmSimple_none_fst {V : View Node (Msg (Chain Tx) (QCert Node Tx))}
    {t : Nat} (h : (fastConfirmSimple n V t).2 = none) :
    (fastConfirmSimple n V t).1 = [] := by
  unfold fastConfirmSimple at h ⊢
  dsimp only at h ⊢
  split at h
  · rename_i hc
    rw [if_pos hc]
  · simp at h

set_option maxHeartbeats 3000000 in
/-- **Lemma 6's engine**: the propose-round fork-choice of any awake validator is
    slot-sorted and headed strictly before the slot — its output is genesis or a prefix
    of an honest previous-slot vote's chain (quorum, or Constraint-(1) majority), and the
    honest-chain invariant bounds those. -/
theorem mfc_propose_ok {x : Exec Pr2 S}
    (hsync : SynchronizedClocks x) (hstepw : TimeStepwise x) (hdiv : TimeDiverges x)
    (hdil : Diligent x) (hone : OneTickPerReading x) (hwpt : WakePrecedesTick x)
    (hmc : S.MonotoneCorruption) (hsyn : Synchrony 0 Q.delta x) (hslp : Sleepiness Q S)
    (hcb : S.CorruptionBounded Q.f) (hfn : 3 * Q.f < n) (hcard : Fintype.card Node ≤ n)
    (hgst : Q.gst = 0)
    {a : Nat} {w : Node} {t0 : Nat} (hta : x[a].time = Q.slotLength * (t0 + 1))
    (hAwa : x.Awake a w) :
    slotsIncreasing (mfc (x[a][w].view) (x[a][w].view)
      (fastConfirmSimple n (x[a][w].view) t0).1 (t0 + 1)) ∧
    proposedAt (mfc (x[a][w].view) (x[a][w].view)
      (fastConfirmSimple n (x[a][w].view) t0).1 (t0 + 1)) ≤ t0 := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  have hmono := hstepw.timeMonotone
  have hexpm : Q.slotLength * (t0 + 1) = Q.slotLength * t0 + Q.slotLength := Nat.mul_succ ..
  have hinv := honest_vote_chain hsync hstepw hdiv hdil hone hwpt hmc hsyn hslp hcb hfn
    hcard hgst
  have hvott1 : Q.voting ((t0 : Int) + 1)
      = ((Q.slotLength * (t0 + 1) + Q.delta : Nat) : Int) := by
    unfold Params.voting
    push_cast
    omega
  have hprefix_ok : ∀ (sm' : SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))),
      sm' ∈ x[a].sent → sm'.sender ∉ S.adv ((x[a].time : Int)) →
      (∃ e' src' tgt', sm'.msg = .vote e' src' tgt' t0) →
      ∀ c : Chain Tx, chainLe c (msgChain sm'.msg) →
      slotsIncreasing c ∧ proposedAt c ≤ t0 := by
    rintro sm' hmem' hhon' ⟨e', src', tgt', hm'⟩ c hc
    obtain ⟨hok, hle⟩ := hinv a sm' e' src' tgt' t0 hmem' hhon' hm'
    have hch : msgChain sm'.msg = e' := by rw [hm']; exact rfl
    rw [hch] at hc
    exact ⟨slotsIncreasing_of_prefix hc hok,
      le_trans (proposedAt_le_of_prefix hc hok) hle⟩
  rcases mfc_base_or_majority (x[a][w].view) (x[a][w].view)
      (fastConfirmSimple n (x[a][w].view) t0).1 (t0 + 1) with hb | hmaj
  · rw [hb]
    rcases fastConfirmSimple_fst_cases (n := n) (x[a][w].view) t0 with h0 | hsupp
    · rw [h0]
      exact ⟨slotsIncreasing_nil, by simp [proposedAt]⟩
    · obtain ⟨q0, hq0mem, hq0hon⟩ :=
        exists_honest_sender (r := ((x[a].time : Int))) hcb hfn hsupp
      obtain ⟨sm'', hsm'', hs''⟩ := Finset.mem_image.mp hq0mem
      rw [Finset.mem_filter] at hsm''
      obtain ⟨hv'', hslot'', hch''⟩ := hsm''
      have hlog'' : sm'' ∈ x[a].sent := views_sound x a w _
        (by simp only [votes, Finset.mem_filter] at hv''; exact hv''.1)
      have hhon'' : sm''.sender ∉ S.adv ((x[a].time : Int)) := by
        rw [hs'']
        exact hq0hon
      obtain ⟨e'', s1'', t1'', s2'', hm''⟩ := exists_vote_of_mem_votes hv''
      have hs2 : s2'' = t0 := by
        have e2 : msgSlot sm''.msg = s2'' := by rw [hm'']; exact rfl
        omega
      subst hs2
      exact hprefix_ok sm'' hlog'' hhon'' ⟨e'', s1'', t1'', hm''⟩ _ hch''
  · -- a majority in the proposer's views has an honest supporter
    have hAVE : ActiveVotesExtend2 x t0 ([] : Chain Tx) :=
      activeVotesExtend_of_le_mfc' hsync hstepw hdiv hdil
        (fun p hp j' hj' => chainLe_nil _)
    have hsubS : Active Q S (t0 : Int) \ S.adv (Q.voting ((t0 : Int) + 1)) ⊆
        voters (x[a][w].view) (t0 + 1) := by
      intro u hu
      obtain ⟨hwA, -⟩ := Finset.mem_sdiff.mp hu
      obtain ⟨iv, ev, evs, evt, htiv, hsentv, -⟩ := hAVE u hwA
      have hview : (⟨u, Msg.vote ev evs evt t0⟩ :
          SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ x[a][w].view := by
        refine hsyn iv a w _ hsentv ?_ hAwa
        rw [htiv, hta]
        omega
      simp only [voters, Finset.mem_image]
      refine ⟨⟨u, Msg.vote ev evs evt t0⟩, ?_, rfl⟩
      simp only [fil1Exp, Finset.mem_filter]
      refine ⟨?_, rfl⟩
      simp only [votes, Finset.mem_filter]
      exact ⟨hview, trivial⟩
    obtain ⟨q0, hq0mem, hq0hon⟩ : ∃ q0 ∈ ((votesFor (x[a][w].view)
        (mfc (x[a][w].view) (x[a][w].view)
          (fastConfirmSimple n (x[a][w].view) t0).1 (t0 + 1)) (t0 + 1) ∩
        votesFor (x[a][w].view) (mfc (x[a][w].view) (x[a][w].view)
          (fastConfirmSimple n (x[a][w].view) t0).1 (t0 + 1)) (t0 + 1)).image
          SignedMsg.sender), q0 ∉ S.adv (Q.voting ((t0 : Int) + 1)) := by
      by_contra hno
      have hsubA : ((votesFor (x[a][w].view) (mfc (x[a][w].view) (x[a][w].view)
          (fastConfirmSimple n (x[a][w].view) t0).1 (t0 + 1)) (t0 + 1) ∩
          votesFor (x[a][w].view) (mfc (x[a][w].view) (x[a][w].view)
            (fastConfirmSimple n (x[a][w].view) t0).1 (t0 + 1)) (t0 + 1)).image
            SignedMsg.sender) ⊆ S.adv (Q.voting ((t0 : Int) + 1)) := by
        intro q hq
        by_contra hq'
        exact hno ⟨q, hq, hq'⟩
      have himgvoters : ((votesFor (x[a][w].view) (mfc (x[a][w].view)
          (x[a][w].view) (fastConfirmSimple n (x[a][w].view) t0).1 (t0 + 1))
            (t0 + 1) ∩
          votesFor (x[a][w].view) (mfc (x[a][w].view) (x[a][w].view)
            (fastConfirmSimple n (x[a][w].view) t0).1 (t0 + 1)) (t0 + 1)).image
            SignedMsg.sender) ⊆ voters (x[a][w].view) (t0 + 1) := by
        intro q hq
        obtain ⟨smq, hsmq, rfl⟩ := Finset.mem_image.mp hq
        exact sender_mem_voters_of_votesFor (Finset.mem_inter.mp hsmq).2
      have hdisj : Disjoint (Active Q S (t0 : Int) \
          S.adv (Q.voting ((t0 : Int) + 1)))
          ((votesFor (x[a][w].view) (mfc (x[a][w].view) (x[a][w].view)
            (fastConfirmSimple n (x[a][w].view) t0).1 (t0 + 1)) (t0 + 1) ∩
            votesFor (x[a][w].view) (mfc (x[a][w].view) (x[a][w].view)
              (fastConfirmSimple n (x[a][w].view) t0).1 (t0 + 1)) (t0 + 1)).image
              SignedMsg.sender) := by
        rw [Finset.disjoint_left]
        intro q hq1 hq2
        exact (Finset.mem_sdiff.mp hq1).2 (hsubA hq2)
      have hunion := Finset.card_le_card (Finset.union_subset hsubS himgvoters)
      rw [Finset.card_union_of_disjoint hdisj] at hunion
      have hgstok : (Q.gst : Int) ≤ Q.proposing ((t0 : Int) + 1) := by
        rw [hgst]
        unfold Params.proposing
        push_cast
        exact mul_nonneg (Int.natCast_nonneg _) (by omega)
      have hslp' : (S.adv (Q.voting ((t0 : Int) + 1))).card <
          (Active Q S (t0 : Int) \ S.adv (Q.voting ((t0 : Int) + 1))).card := by
        have h := hslp ((t0 : Int) + 1) hgstok
        simpa using h
      have himgA := Finset.card_le_card hsubA
      have hm2 := hmaj
      omega
    obtain ⟨smq, hsmq, hs0q⟩ := Finset.mem_image.mp hq0mem
    have hsmq1 := (Finset.mem_inter.mp hsmq).1
    have hv1 : smq ∈ votes (x[a][w].view) := votesFor_subset_votes _ _ (t0 + 1) hsmq1
    have hlogq : smq ∈ x[a].sent := views_sound x a w _
      (by simp only [votes, Finset.mem_filter] at hv1; exact hv1.1)
    have hhonq : smq.sender ∉ S.adv ((x[a].time : Int)) := by
      intro had
      refine hq0hon ?_
      rw [← hs0q]
      refine hmc _ _ ?_ had
      rw [hta, hvott1]
      exact_mod_cast (by omega : Q.slotLength * (t0 + 1) ≤
        Q.slotLength * (t0 + 1) + Q.delta)
    obtain ⟨eq', sq1, tq1, sq2, hmq⟩ := exists_vote_of_mem_votes hv1
    have hsq : sq2 = t0 := by
      have h1 : smq ∈ fil1Exp (filEq (x[a][w].view)) (t0 + 1) :=
        Finset.filter_subset _ _ (Finset.filter_subset _ _ hsmq1)
      have h2 := (Finset.mem_filter.mp h1).2
      have e2 : msgSlot smq.msg = sq2 := by rw [hmq]; exact rfl
      omega
    subst hsq
    exact hprefix_ok smq hlogq hhonq ⟨eq', sq1, tq1, hmq⟩ _ (votesFor_extends hsmq1)


set_option maxHeartbeats 3000000 in
/-- **Lemma 4's base case**: an honest proposer's slot-`t` proposal is voted for by every
    validator active in slot `t` — the vote *is* `chp`. The fork-choice at each vote tick
    is bounded by `chp` (base-or-majority: the frozen chain is the merge value or, by the
    sender check, the proposer's own `chC`, both `⪯ chp`; a majority transfers into the
    proposer's views, where `chp` extends the longest majority chain), so the proposal
    branch fires — and the sender check plus one-tick-per-reading pins the chosen chain
    to the proposer's one message. -/
theorem activeVotesExtend_of_propose {x : Exec Pr2 S}
    (hsync : SynchronizedClocks x) (hstepw : TimeStepwise x) (hdiv : TimeDiverges x)
    (hdil : Diligent x) (hone : OneTickPerReading x) (hwpt : WakePrecedesTick x)
    (hmc : S.MonotoneCorruption)
    (hsyn : Synchrony 0 Q.delta x) (hrel : Relay 0 Q.delta x) (hslp : Sleepiness Q S)
    (hcb : S.CorruptionBounded Q.f) (hfn : 3 * Q.f < n) (hcard : Fintype.card Node ≤ n)
    (hgst : Q.gst = 0)
    {t : Nat} (ht : 1 ≤ t) {vp : Node} {chp chC : Chain Tx} {qc : Option (QCert Node Tx)}
    {ck : Checkpoint (Chain Tx)} {i : Nat}
    (hsent : (⟨vp, Msg.propose chp chC qc ck t⟩ :
      SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ x[i].sent)
    (hhon_i : vp ∉ S.adv ((x[i].time : Int)))
    (hhon_t : vp ∉ S.adv (Q.voting (t : Int))) :
    ActiveVotesExtend2 x t chp := by
  obtain ⟨t0, rfl⟩ : ∃ t0, t = t0 + 1 := ⟨t - 1, by omega⟩
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  have hmono := hstepw.timeMonotone
  have hexpm : Q.slotLength * (t0 + 1) = Q.slotLength * t0 + Q.slotLength := Nat.mul_succ ..
  have hvott : Q.voting ((t0 + 1 : Nat) : Int)
      = ((Q.slotLength * (t0 + 1) + Q.delta : Nat) : Int) := by
    unfold Params.voting
    push_cast
    omega
  -- the proposal's provenance: the proposer's tick at `propose(t0+1)`
  obtain ⟨hvpprop, k, hki, hlblk, htk, hemk, hchp, hchC, hqc⟩ :=
    propose_provenance2 hsync hmc hmono hsent hhon_i rfl
  have hvp_prop : vp = proposer (t0 + 1) := hvpprop
  simp only [Nat.add_sub_cancel] at hchp hchC hqc
  have hAwk : x.Awake k vp := by
    have hstep := x.step k
    rw [hlblk] at hstep
    have h := hstep.1
    simp only [spec] at h
    exact h
  have hmemk : (⟨vp, Msg.propose chp chC qc ck (t0 + 1)⟩ :
      SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ x[k + 1].sent := by
    have h := hemk
    rw [← Multiset.count_pos] at h ⊢
    rw [Multiset.count_sub] at h
    omega
  have htk1 : x[k + 1].time = Q.slotLength * (t0 + 1) := by
    rw [tick_time hlblk, htk]
  -- honesty through `voting(t0+1)`
  have hhon_le : ∀ r : Time, r ≤ Q.slotLength * (t0 + 1) + Q.delta →
      vp ∉ S.adv ((r : Int)) := by
    intro r hr had
    refine hhon_t (hmc _ _ ?_ had)
    rw [hvott]
    exact_mod_cast hr
  -- `chC ⪯ chp`
  have hchCchp : chainLe chC chp := by
    rw [hchp, hchC]
    exact chainLe_trans (base_le_mfc _ _ _ _) (chainLe_extend _ _ _)
  -- the proposer's fork-choice output is structurally sound, so `chp` is
  have hMFCpok := mfc_propose_ok hsync hstepw hdiv hdil hone hwpt hmc hsyn hslp hcb hfn
    hcard hgst (a := k) (w := vp) (t0 := t0) htk hAwk
  have hSIchp : slotsIncreasing chp := by
    rw [hchp]
    exact slotsIncreasing_extend pool hMFCpok.1 (lt_of_le_of_lt hMFCpok.2 (by omega))
  intro p hp
  have hp' : p ∈ Active Q S ((t0 : Int) + 1) := by
    have hcast : (((t0 + 1 : Nat)) : Int) = (t0 : Int) + 1 := by push_cast; omega
    rw [← hcast]
    exact hp
  -- the vote tick of `p`
  obtain ⟨i₁, hi₁⟩ := hdiv (Q.slotLength * (t0 + 1) + Q.delta)
  obtain ⟨i₀, hi₀, hti₀⟩ := exists_time_eq hstepw hi₁
  have hAw0 : x.Awake i₀ p := by
    show p ∈ S.awake ((x[i₀].time : Int))
    rw [hti₀]
    refine mem_awakeThroughout.mp hp _ ?_ ?_ <;> rw [hvott] <;> omega
  obtain ⟨j, htj, hlblj⟩ := hdil (Q.slotLength * (t0 + 1) + Q.delta) p ⟨i₀, hti₀, hAw0⟩
  have hAwj : x.Awake j p := by
    have hstep := x.step j
    rw [hlblj] at hstep
    have h := hstep.1
    simp only [spec] at h
    exact h
  have hgate : x[j][p].st.activeAt ≤ Q.slotLength * (t0 + 1) + Q.delta := by
    refine activeAt_le_voting hsync hmono (t1 := t0 + 1) ?_ (le_of_eq htj)
    intro r h1 h2
    refine mem_awakeThroughout.mp hp _ ?_ ?_ <;> rw [hvott] <;> omega
  obtain ⟨dotj, -, hemit⟩ := tick_effect hlblj
  have hsend := handler2_vote_send_eq (Q := Q) (n := n) (kappa := kappa) (pool := pool)
    (proposer := proposer) (dot := dotj) (p := p) (V := x[j][p].view) (s := x[j][p].st)
    (voting_reading_mod Q (t0 + 1)) hgate
  rw [voting_reading_div Q (t0 + 1)] at hsend
  -- the proposal reaches `p`'s vote view, valid
  have hviewprop : (⟨vp, Msg.propose chp chC qc ck (t0 + 1)⟩ :
      SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ x[j][p].view := by
    refine hsyn (k + 1) j p _ hmemk ?_ hAwj
    rw [htk1, htj]
    omega
  have hdeliver_kj : ∀ m, m ∈ x[k][vp].view → m ∈ x[j][p].view := by
    intro m hm
    refine hsyn k j p m (views_sound x k vp m hm) ?_ hAwj
    rw [htk, htj]
    omega
  have hvalidprop : ValidProposal2 n proposer (x[j][p].view)
      ⟨vp, Msg.propose chp chC qc ck (t0 + 1)⟩ := by
    refine ⟨hvp_prop, by rw [hchp]; exact proposedAt_extend _ _ _, hchCchp, ?_⟩
    by_cases hchC0 : chC = []
    · exact Or.inl hchC0
    · right
      cases hsnd : (fastConfirmSimple n (x[k][vp].view) t0).2 with
      | none =>
          exact absurd (hchC.trans (fastConfirmSimple_none_fst hsnd)) hchC0
      | some cert =>
          have hfc : fastConfirmSimple n (x[k][vp].view) t0
              = ((fastConfirmSimple n (x[k][vp].view) t0).1, some cert) := by
            rw [← hsnd]
          have hcert := fastConfirmSimple_snd_spec hfc
          refine ⟨cert, by rw [hqc, hsnd], ?_, ?_⟩
          · rcases fastConfirmSimple_fst_cases (n := n) (x[k][vp].view) t0 with h0 | hsupp
            · exact absurd (hchC.trans h0) hchC0
            · rw [hcert, Finset.image_image]
              exact hsupp
          · rintro e hemem
            rw [hcert] at hemem
            obtain ⟨sm, hsm_supp, rfl⟩ := Finset.mem_image.mp hemem
            rw [Finset.mem_filter] at hsm_supp
            obtain ⟨hsmv, hsmslot, hsmch⟩ := hsm_supp
            have hsmview : sm ∈ x[k][vp].view := by
              simp only [votes, Finset.mem_filter] at hsmv
              exact hsmv.1
            obtain ⟨e0, s0, t0', slot0, hm0⟩ := exists_vote_of_mem_votes hsmv
            refine ⟨by rw [hchC]; exact hsmch,
              (by show msgSlot sm.msg = t0 + 1 - 1; omega), s0, t0', ?_⟩
            have heq : (⟨sm.sender, Msg.vote (msgChain sm.msg) s0 t0' (msgSlot sm.msg)⟩ :
                SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) = sm := by
              have h1 : msgChain sm.msg = e0 := by rw [hm0]; exact rfl
              have h2 : msgSlot sm.msg = slot0 := by rw [hm0]; exact rfl
              rw [h1, h2, ← hm0]
            rw [heq]
            exact hdeliver_kj sm hsmview
  -- the frozen state entering `p`'s vote tick
  obtain ⟨im, himj, htim, hvfj, hcfj⟩ := frozen_at_vote_tick hsync hstepw hdil hone hp' hlblj
  -- the merge value is below `chC`
  have hbmchC : chainLe ((fastConfirmSimple n (x[im][p].view) t0).1) chC := by
    by_cases hbm0 : (fastConfirmSimple n (x[im][p].view) t0).1 = []
    · rw [hbm0]
      exact chainLe_nil _
    · rcases fastConfirmSimple_fst_cases (n := n) (x[im][p].view) t0 with h0 | hsuppm
      · exact absurd h0 hbm0
      · have hsubm : ((votes (x[im][p].view)).filter (fun sm => msgSlot sm.msg = t0 ∧
              chainLe ((fastConfirmSimple n (x[im][p].view) t0).1) (msgChain sm.msg))) ⊆
            ((votes (x[k][vp].view)).filter (fun sm => msgSlot sm.msg = t0 ∧
              chainLe ((fastConfirmSimple n (x[im][p].view) t0).1) (msgChain sm.msg))) := by
          intro sm hsm
          rw [Finset.mem_filter] at hsm ⊢
          obtain ⟨hv, hcond⟩ := hsm
          simp only [votes, Finset.mem_filter] at hv ⊢
          refine ⟨⟨?_, hv.2⟩, hcond⟩
          refine hsyn im k vp _ (views_sound x im p _ hv.1) ?_ hAwk
          rw [htim, htk]
          omega
        have hsuppp : 2 * n ≤ 3 * (((votes (x[k][vp].view)).filter (fun sm =>
            msgSlot sm.msg = t0 ∧ chainLe ((fastConfirmSimple n (x[im][p].view) t0).1)
              (msgChain sm.msg))).image SignedMsg.sender).card := by
          refine le_trans hsuppm ?_
          have h3 := Finset.card_le_card
            (Finset.image_subset_image (f := SignedMsg.sender) hsubm)
          omega
        have hcand : (fastConfirmSimple n (x[im][p].view) t0).1
            ∈ candidates (x[k][vp].view) ([] : Chain Tx) := by
          have hpos : 0 < (((votes (x[k][vp].view)).filter (fun sm =>
              msgSlot sm.msg = t0 ∧ chainLe ((fastConfirmSimple n (x[im][p].view) t0).1)
                (msgChain sm.msg))).image SignedMsg.sender).card := by
            omega
          rw [Finset.card_pos] at hpos
          obtain ⟨q, hq⟩ := hpos
          obtain ⟨sm, hsm, -⟩ := Finset.mem_image.mp hq
          rw [Finset.mem_filter] at hsm
          exact mem_candidates_of_extends hsm.1 hsm.2.2
        have hlen := fastConfirmSimple_length_ge (n := n) hbm0 hcand hsuppp
        rcases fastConfirmSimple_fst_cases (n := n) (x[k][vp].view) t0 with h0p | hsuppP
        · exfalso
          have hpos : 0 < ((fastConfirmSimple n (x[im][p].view) t0).1).length := by
            cases hb : (fastConfirmSimple n (x[im][p].view) t0).1 with
            | nil => exact absurd hb hbm0
            | cons _ _ => simp [hb]
          rw [h0p] at hlen
          simp only [List.length_nil] at hlen
          omega
        · rw [← hchC] at hlen hsuppP
          exact chainLe_of_comparable _ _
            (supported_comparable hsync hone hmc hmono hcb hfn hcard hsuppp hsuppP) hlen
  -- the processed frozen chain: the merge value or, sender-pinned, the proposer's `chC`
  have hfz : ((processProposals2 n proposer (x[j][p].view) (t0 + 1) (x[j][p].st)).chFrozen
        = (fastConfirmSimple n (x[im][p].view) t0).1 ∨
      (processProposals2 n proposer (x[j][p].view) (t0 + 1) (x[j][p].st)).chFrozen
        = chC) := by
    rcases processProposals2_chFrozen (n := n) (x[j][p].view) (t0 + 1) (x[j][p].st)
      with hfz0 | ⟨sm', hsm'V, ⟨chp', qc', ck', hsm'msg⟩, hsm'valid⟩
    · rw [hfz0, hcfj]
      exact Or.inl rfl
    · obtain ⟨sd', m0'⟩ := sm'
      have hm0' : m0' = Msg.propose chp' ((processProposals2 n proposer (x[j][p].view)
          (t0 + 1) (x[j][p].st)).chFrozen) qc' ck' (t0 + 1) := hsm'msg
      subst hm0'
      have hsd' : sd' = proposer (t0 + 1) := hsm'valid.1
      have hhon_j : sd' ∉ S.adv ((x[j].time : Int)) := by
        rw [hsd', ← hvp_prop]
        refine hhon_le _ ?_
        rw [htj]
      obtain ⟨-, k', hk'j, hlblk', htk', hem', -, -, -⟩ :=
        propose_provenance2 hsync hmc hmono (views_sound x j p _ hsm'V) hhon_j rfl
      have hlblk'' : x.lbl k' = .tick vp (Q.slotLength * (t0 + 1)) := by
        rw [hlblk']
        simp only [hsd', ← hvp_prop]
      have hkk : k' = k := hone k' k vp _ hlblk'' hlblk
      subst hkk
      have heqmsg := tick_sends_subsingleton hlblk hem' hemk
      have hinj := congrArg SignedMsg.msg heqmsg
      injection hinj with h1 h2 h3 h4 h5
      exact Or.inr h2
  have hfz_le_chp : chainLe ((processProposals2 n proposer (x[j][p].view) (t0 + 1)
      (x[j][p].st)).chFrozen) chp := by
    rcases hfz with heq | heq
    · rw [heq]
      exact chainLe_trans hbmchC hchCchp
    · rw [heq]
      exact hchCchp
  -- `chC` is below the processed frozen chain
  have hbase : chainLe chC ((processProposals2 n proposer (x[j][p].view) (t0 + 1)
      (x[j][p].st)).chFrozen) := by
    have hlb := processProposals2_chFrozen_lb (n := n) (x[j][p].view) (t0 + 1)
      (x[j][p].st) hviewprop rfl hvalidprop
    rcases hlb with h | ⟨y, hy1, hy2⟩
    · exact h
    · exfalso
      rcases hfz with heq | heq
      · exact hy1 (chainLe_trans hy2 (heq ▸ hbmchC))
      · exact hy1 (heq ▸ hy2)
  -- the fork-choice is bounded by `chp`
  have hchMFCchp : chainLe (mfc (processProposals2 n proposer (x[j][p].view) (t0 + 1)
      (x[j][p].st)).vFrozen (x[j][p].view)
      (processProposals2 n proposer (x[j][p].view) (t0 + 1) (x[j][p].st)).chFrozen
      (t0 + 1)) chp := by
    rcases mfc_base_or_majority (processProposals2 n proposer (x[j][p].view) (t0 + 1)
        (x[j][p].st)).vFrozen (x[j][p].view)
        (processProposals2 n proposer (x[j][p].view) (t0 + 1) (x[j][p].st)).chFrozen
        (t0 + 1) with hmfcb | hmfcm
    · rw [hmfcb]
      exact hfz_le_chp
    · have hvf : (processProposals2 n proposer (x[j][p].view) (t0 + 1)
          (x[j][p].st)).vFrozen = x[im][p].view := by
        rw [processProposals2_vFrozen]
        exact hvfj
      rw [hvf] at hmfcm ⊢
      have hmajp := majority_transfer hsync hsyn hrel hlblj htim hlblk htk hmfcm
      have hle := le_mfc_of_majority (x[k][vp].view) (x[k][vp].view) chC (t0 + 1) _
        (chainLe_trans hbase (base_le_mfc _ _ _ _)) hmajp
      refine chainLe_trans hle ?_
      rw [hchp, hchC]
      exact chainLe_extend _ _ _
  -- the vote is the proposal itself
  have hvote_eq : voteChoice proposer (x[j][p].view) (t0 + 1)
      (mfc (processProposals2 n proposer (x[j][p].view) (t0 + 1) (x[j][p].st)).vFrozen
        (x[j][p].view)
        (processProposals2 n proposer (x[j][p].view) (t0 + 1) (x[j][p].st)).chFrozen
        (t0 + 1)) = chp := by
    unfold voteChoice
    have hcondtrue : ((⟨vp, Msg.propose chp chC qc ck (t0 + 1)⟩ :
          SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))).sender == proposer (t0 + 1)
        && ((t0 + 1 : Nat) == (t0 + 1)) && (proposedAt chp == (t0 + 1))
        && slotsIncreasing chp
        && chainLe (mfc (processProposals2 n proposer (x[j][p].view) (t0 + 1)
          (x[j][p].st)).vFrozen (x[j][p].view)
          (processProposals2 n proposer (x[j][p].view) (t0 + 1) (x[j][p].st)).chFrozen
          (t0 + 1)) chp) = true := by
      simp only [Bool.and_eq_true, beq_iff_eq]
      exact ⟨⟨⟨⟨hvp_prop, trivial⟩, by rw [hchp]; exact proposedAt_extend _ _ _⟩,
        hSIchp⟩, hchMFCchp⟩
    cases hfind : (x[j][p].view).toList.findSome? (fun sm => match sm.msg with
        | .propose chp' _ _ _ t' =>
            if sm.sender == proposer (t0 + 1) && t' == (t0 + 1) &&
                proposedAt chp' == (t0 + 1) && slotsIncreasing chp' &&
                chainLe (mfc (processProposals2 n proposer (x[j][p].view) (t0 + 1)
                  (x[j][p].st)).vFrozen (x[j][p].view)
                  (processProposals2 n proposer (x[j][p].view) (t0 + 1)
                    (x[j][p].st)).chFrozen (t0 + 1)) chp' then some chp'
            else none
        | .vote .. => none) with
    | none =>
        exfalso
        have hall := List.findSome?_eq_none_iff.mp hfind
          (⟨vp, Msg.propose chp chC qc ck (t0 + 1)⟩ :
            SignedMsg Node (Msg (Chain Tx) (QCert Node Tx)))
          (Finset.mem_toList.mpr hviewprop)
        dsimp only at hall
        rw [if_pos hcondtrue] at hall
        cases hall
    | some c =>
        simp only [Option.getD_some]
        obtain ⟨a, haV, hfa⟩ := List.exists_of_findSome?_eq_some hfind
        obtain ⟨asd, am⟩ := a
        revert hfa
        cases am with
        | vote e src tgt s₁ => intro h; cases h
        | propose chpa chca qca cka ta =>
            dsimp only
            split_ifs with hcnd
            · intro h
              injection h with h
              subst h
              simp only [Bool.and_eq_true, beq_iff_eq] at hcnd
              obtain ⟨⟨⟨⟨hsda, hta⟩, -⟩, -⟩, -⟩ := hcnd
              subst hta
              have hhon_a : asd ∉ S.adv ((x[j].time : Int)) := by
                rw [hsda, ← hvp_prop]
                refine hhon_le _ ?_
                rw [htj]
              obtain ⟨-, k', hk'j, hlblk', htk', hem', -, -, -⟩ :=
                propose_provenance2 hsync hmc hmono
                  (views_sound x j p _ (Finset.mem_toList.mp haV)) hhon_a rfl
              have hlblk'' : x.lbl k' = .tick vp (Q.slotLength * (t0 + 1)) := by
                rw [hlblk']
                simp only [hsda, ← hvp_prop]
              have hkk : k' = k := hone k' k vp _ hlblk'' hlblk
              subst hkk
              have heqmsg := tick_sends_subsingleton hlblk hem' hemk
              have hinj := congrArg SignedMsg.msg heqmsg
              injection hinj with h1 h2 h3 h4 h5
            · intro h
              cases h
  rw [hvote_eq] at hsend
  have hmem : ⟪vote, chp, dotj, dotj, (t0 + 1), p⟫ ∈ x[j + 1].sent := by
    refine hemit _ ?_
    rw [hsend]
    exact Multiset.mem_singleton_self _
  exact ⟨j + 1, chp, dotj, dotj, by rw [tick_time hlblj, htj], hmem, chainLe_refl chp⟩

/-- **Lemma 7's engine**: if every slot-`t` active voted an extension of `chp` and there
    are at least `2n/3` actives, then any validator's fast-confirm tick of slot `t`
    leaves its confirmed chain extending `chp` — the quorum is in its view by synchrony,
    so `fastconfirmsimple` returns a certificate for a chain at least as long as `chp`
    and comparable with it. No activity window needed: the tick's own enabling gives
    awakeness. -/
theorem le_chi_at_fconf {x : Exec Pr2 S}
    (hsync : SynchronizedClocks x) (hstepw : TimeStepwise x)
    (hone : OneTickPerReading x) (hmc : S.MonotoneCorruption)
    (hsyn : Synchrony 0 Q.delta x)
    (hcb : S.CorruptionBounded Q.f) (hfn : 3 * Q.f < n) (hcard : Fintype.card Node ≤ n)
    {t : Nat} {chp : Chain Tx} (hvotes : ActiveVotesExtend2 x t chp)
    (hbig : 2 * n ≤ 3 * (Active Q S (t : Int)).card)
    {vi : Node} {j : Nat} (hj : x.lbl j = .tick vi (Q.slotLength * t + 2 * Q.delta)) :
    chainLe chp (x[j + 1][vi].st.chi) := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  have hmono := hstepw.timeMonotone
  have htj : x[j].time = Q.slotLength * t + 2 * Q.delta := tick_reading hsync hj
  have hAwj : x.Awake j vi := by
    have hstep := x.step j
    rw [hj] at hstep
    have h := hstep.1
    simp only [spec] at h
    exact h
  -- the post-state chain
  obtain ⟨dt, hst, -⟩ := tick_effect hj
  rw [hst, handler2_fastconfirm (fconf_reading_mod Q t), fconf_reading_div Q t]
  -- every active's vote is in the view, supporting `chp`
  have hsub : Active Q S (t : Int) ⊆ (((votes (x[j][vi].view)).filter (fun sm =>
      msgSlot sm.msg = t ∧ chainLe chp (msgChain sm.msg))).image SignedMsg.sender) := by
    intro w hw
    obtain ⟨iv, e, esrc, etgt, htiv, hsent, hext⟩ := hvotes w hw
    have hview : (⟨w, Msg.vote e esrc etgt t⟩ :
        SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ x[j][vi].view := by
      refine hsyn iv j vi _ hsent ?_ hAwj
      rw [htiv, htj]
      omega
    refine Finset.mem_image.mpr ⟨⟨w, Msg.vote e esrc etgt t⟩, ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨?_, rfl, hext⟩
    simp only [votes, Finset.mem_filter]
    exact ⟨hview, trivial⟩
  have hsupp : 2 * n ≤ 3 * (((votes (x[j][vi].view)).filter (fun sm =>
      msgSlot sm.msg = t ∧ chainLe chp (msgChain sm.msg))).image SignedMsg.sender).card := by
    have h := Finset.card_le_card hsub
    omega
  by_cases hchp0 : chp = []
  · subst hchp0
    split_ifs <;> exact chainLe_nil _
  · -- `chp` bounds the fast confirmation from below, and a certificate exists
    have hcand : chp ∈ candidates (x[j][vi].view) ([] : Chain Tx) := by
      have hpos : 0 < (((votes (x[j][vi].view)).filter (fun sm =>
          msgSlot sm.msg = t ∧ chainLe chp (msgChain sm.msg))).image
            SignedMsg.sender).card := by
        omega
      rw [Finset.card_pos] at hpos
      obtain ⟨q, hq⟩ := hpos
      obtain ⟨sm, hsm, -⟩ := Finset.mem_image.mp hq
      rw [Finset.mem_filter] at hsm
      exact mem_candidates_of_extends hsm.1 hsm.2.2
    have hlen := fastConfirmSimple_length_ge (n := n) hchp0 hcand hsupp
    have hle : chainLe chp ((fastConfirmSimple n (x[j][vi].view) t).1) := by
      rcases fastConfirmSimple_fst_cases (n := n) (x[j][vi].view) t with h0 | hsuppF
      · exfalso
        have hpos : 0 < chp.length := by
          cases hb : chp with
          | nil => exact absurd hb hchp0
          | cons _ _ => simp [hb]
        rw [h0] at hlen
        simp only [List.length_nil] at hlen
        omega
      · exact chainLe_of_comparable _ _
          (supported_comparable hsync hone hmc hmono hcb hfn hcard hsupp hsuppF) hlen
    have hsome : (fastConfirmSimple n (x[j][vi].view) t).2.isSome := by
      cases hsnd : (fastConfirmSimple n (x[j][vi].view) t).2 with
      | none =>
          exfalso
          have h0 := fastConfirmSimple_none_fst hsnd
          have hpos : 0 < chp.length := by
            cases hb : chp with
            | nil => exact absurd hb hchp0
            | cons _ _ => simp [hb]
          rw [h0] at hlen
          simp only [List.length_nil] at hlen
          omega
      | some _ => rfl
    rw [if_pos hsome]
    split_ifs with hg
    · exact chainLe_trans hle hg
    · exact hle

end Lemma2Vote

/-! ### Lemma 5: the confirmed chain is a prefix of every later fork choice

The paper's proof is a minimality contradiction; here it is a strong induction on the
execution index of the last `chi` write (`chi_step2`). The κ-deep write is bounded
through the honest proposal of the window hypothesis (`kappaPrefix_le_of_close` after
`mfc_vote_ok`); the fast-confirm write propagates by Lemma 3's machinery, with the
quorum-direct lemmas covering the very next slot. -/

section Lemma5

variable [Fintype Node]

/-- **Lemma 1, de-probabilized** — the conclusion the κ-window argument consumes as a
    hypothesis: behind every slot `t ≥ κ` there is a slot `tp ≥ 1` in the window
    `[t−κ, t)` whose (honest) proposer sent a proposal. The paper derives this with
    overwhelming probability from proposer sortition (`Lemma 1, arXiv:2601.03862v1`);
    this model takes the conclusion as an assumption wherever the paper says "w.o.p.".
    The proposer's identity is not mentioned: it is derivable (`propose_provenance2`),
    as in `lemma4`.

    Two deliberate edges (2026-08-04, with the slot-indexed `kappaPrefix`):

    * The quantification starts at `t = κ`, not `t = κ + 1`: at slot `κ` the paper's
      prefix `(·)⌈κ,κ` can retain a slot-`0` block, so the absorption argument needs a
      windowed proposal there too. Below `κ` nothing qualifies for the prefix and no
      window is needed (`kappaPrefix_nil_of_lt`).
    * `1 ≤ tp` strengthens the paper's window `[t−κ, t)`, which at `t = κ` reaches slot
      `0`. `lemma4`'s machinery assumes `1 ≤ t` (`activeVotesExtend_of_propose`), so
      slot-`0` proposals are excluded here instead of extending it; for `t > κ` the
      conjunct is implied. The cost: at `κ = 1` the `t = κ` instance is unsatisfiable
      and Lemma 5 holds vacuously — a degenerate parameter for the paper too, whose
      w.o.p. arguments need `κ` large. If `κ = 1` ever matters, the alternative is to
      prove `lemma4` at `t = 0` (its base case simplifies there: no previous-slot votes,
      the frozen chain is genesis) and let `tp = 0` back in. -/
def HonestProposalWindow (x : Exec Pr2 S) : Prop :=
  ∀ t : Nat, kappa ≤ t → ∃ tp, 1 ≤ tp ∧ t - kappa ≤ tp ∧ tp < t ∧
    ∃ (i : Nat) (vp : Node) (chp chC : Chain Tx) (qc : Option (QCert Node Tx))
      (ck : Checkpoint (Chain Tx)),
      (⟨vp, Msg.propose chp chC qc ck tp⟩ :
        SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ x[i].sent ∧
      vp ∉ S.adv ((x[i].time : Int)) ∧ vp ∉ S.adv (Q.voting (tp : Int))

/-- `ActiveVotesExtend2` persists forward — Lemma 2's step, iterated. -/
theorem ave_propagate {x : Exec Pr2 S}
    (hsync : SynchronizedClocks x) (hstepw : TimeStepwise x) (hdiv : TimeDiverges x)
    (hdil : Diligent x) (hone : OneTickPerReading x) (hwpt : WakePrecedesTick x)
    (hmc : S.MonotoneCorruption) (hsyn : Synchrony 0 Q.delta x) (hslp : Sleepiness Q S)
    (hcb : S.CorruptionBounded Q.f) (hfn : 3 * Q.f < n) (hgst : Q.gst = 0)
    {t : Nat} (ht : 1 ≤ t) {ch : Chain Tx} (h : ActiveVotesExtend2 x t ch)
    {t' : Nat} (ht' : t ≤ t') : ActiveVotesExtend2 x t' ch := by
  induction t', ht' using Nat.le_induction with
  | base => exact h
  | succ m hm ih =>
      exact activeVotesExtend_of_le_mfc hsync hstepw hdiv hdil fun p hp j hj =>
        le_mfc_at_vote2 hsync hstepw hdil hwpt hone hmc hsyn hslp hcb hfn hgst
          (by omega) ih hp hj

/-- An honestly sent proposal is extended by every slot's actives from its own slot on —
    Lemma 4's content, assembled where the Lemma 5 machinery can reach it. -/
theorem ave_of_honest_proposal {x : Exec Pr2 S}
    (hsync : SynchronizedClocks x) (hstepw : TimeStepwise x) (hdiv : TimeDiverges x)
    (hdil : Diligent x) (hone : OneTickPerReading x) (hwpt : WakePrecedesTick x)
    (hmc : S.MonotoneCorruption) (hsyn : Synchrony 0 Q.delta x) (hrel : Relay 0 Q.delta x)
    (hslp : Sleepiness Q S) (hcb : S.CorruptionBounded Q.f) (hfn : 3 * Q.f < n)
    (hcard : Fintype.card Node ≤ n) (hgst : Q.gst = 0)
    {t : Nat} (ht : 1 ≤ t) {vp : Node} {chp chC : Chain Tx} {qc : Option (QCert Node Tx)}
    {ck : Checkpoint (Chain Tx)} {i : Nat}
    (hsent : (⟨vp, Msg.propose chp chC qc ck t⟩ :
      SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ x[i].sent)
    (hhon_i : vp ∉ S.adv ((x[i].time : Int)))
    (hhon_t : vp ∉ S.adv (Q.voting (t : Int)))
    {t' : Nat} (ht' : t ≤ t') : ActiveVotesExtend2 x t' chp :=
  ave_propagate hsync hstepw hdiv hdil hone hwpt hmc hsyn hslp hcb hfn hgst ht
    (activeVotesExtend_of_propose hsync hstepw hdiv hdil hone hwpt hmc hsyn hrel hslp
      hcb hfn hcard hgst ht hsent hhon_i hhon_t) ht'

/-- **The propose-round bound over the tick's real base**: `le_mfc_at_propose2` takes
    `base ⪯ ch` as input, but the propose tick's base is its own fast confirmation. An
    honest supporter of a nonempty base has one slot-`t` vote (`honest_vote_unique2`),
    which extends both the base and — through `ActiveVotesExtend2` — `ch`, so the two are
    comparable and either `le_mfc_at_propose2` or `base_le_mfc` closes. -/
theorem le_mfc_at_propose_of_ave {x : Exec Pr2 S}
    (hsync : SynchronizedClocks x) (hstepw : TimeStepwise x) (hdil : Diligent x)
    (hwpt : WakePrecedesTick x) (hone : OneTickPerReading x) (hmc : S.MonotoneCorruption)
    (hsyn : Synchrony 0 Q.delta x) (hslp : Sleepiness Q S)
    (hcb : S.CorruptionBounded Q.f) (hfn : 3 * Q.f < n) (hcard : Fintype.card Node ≤ n)
    (hgst : Q.gst = 0)
    {t : Nat} (ht : 1 ≤ t) {ch : Chain Tx} (hvotes : ActiveVotesExtend2 x t ch)
    {b : Nat} (htb : x[b].time = Q.slotLength * (t + 1))
    {vj : Node} (hv : vj ∈ Active Q S ((t : Int) + 1)) :
    chainLe ch (mfc (x[b][vj].view) (x[b][vj].view)
      (fastConfirmSimple n (x[b][vj].view) t).1 (t + 1)) := by
  have hmono := hstepw.timeMonotone
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  rcases fastConfirmSimple_fst_cases (n := n) (x[b][vj].view) t with h0 | hsupp
  · refine le_mfc_at_propose2 hsync hstepw hdil hwpt hone hmc hsyn hslp hgst ht hvotes
      htb hv ?_
    rw [h0]
    exact chainLe_nil _
  · obtain ⟨q0, hq0mem, hq0hon⟩ :=
      exists_honest_sender (r := ((x[b].time : Int))) hcb hfn hsupp
    obtain ⟨smq, hsmq, hs0q⟩ := Finset.mem_image.mp hq0mem
    rw [Finset.mem_filter] at hsmq
    obtain ⟨hvq, hslotq, hchq⟩ := hsmq
    have hlogq : smq ∈ x[b].sent := views_sound x b vj _
      (by simp only [votes, Finset.mem_filter] at hvq; exact hvq.1)
    have hhonq : smq.sender ∉ S.adv ((x[b].time : Int)) := by
      rw [hs0q]
      exact hq0hon
    obtain ⟨eq', sq1, tq1, sq2, hmq⟩ := exists_vote_of_mem_votes hvq
    have hsq : sq2 = t := by
      have e2 : msgSlot smq.msg = sq2 := by rw [hmq]; exact rfl
      omega
    subst hsq
    have hactq : smq.sender ∈ Active Q S (sq2 : Int) :=
      mem_active_of_honest_vote2 hsync hstepw hdil hwpt hmc ht hlogq hhonq hmq
    obtain ⟨iv, ev, evs, evt, htiv, hsentv, hext⟩ := hvotes smq.sender hactq
    have hhon_iv : smq.sender ∉ S.adv ((x[iv].time : Int)) := by
      intro had
      refine hhonq (hmc _ _ ?_ had)
      rw [htiv, htb]
      have hexp : Q.slotLength * (sq2 + 1) = Q.slotLength * sq2 + Q.slotLength :=
        Nat.mul_succ ..
      exact_mod_cast (by omega : Q.slotLength * sq2 + Q.delta ≤ Q.slotLength * (sq2 + 1))
    have huniq : (⟪vote, ev, evs, evt, sq2, smq.sender⟫ :
        SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) = smq :=
      honest_vote_unique2 hsync hone hmc hmono hlogq hsentv hhonq hhon_iv rfl hmq rfl
    have hchain : msgChain smq.msg = ev := by rw [← huniq]; exact rfl
    rcases comparable_of_common_extension hchq
        (by rw [hchain]; exact hext : chainLe ch (msgChain smq.msg)) with hbc | hcb2
    · exact le_mfc_at_propose2 hsync hstepw hdil hwpt hone hmc hsyn hslp hgst ht hvotes
        htb hv hbc
    · exact chainLe_trans hcb2 (base_le_mfc _ _ _ _)

set_option maxHeartbeats 2000000 in
/-- **Lemma 5's engine**: any validator's confirmed chain at any point is a prefix of the
    fork-choice output of any validator active at a later (or simultaneous) propose or
    vote round. Strong induction on the execution index via `chi_step2`:

    * an untouched `chi` inherits the bound (the time constraint only relaxes);
    * the **κ-deep write** happens with the joining check open, hence at a slot the
      writer is active in (`active_of_open_join`); below slot `κ` nothing qualifies
      for the slot-indexed prefix (`kappaPrefix_nil_of_lt`), and from `κ` on the
      window's honest proposal is a prefix of the fork choice
      (`le_mfc_at_vote2`) that absorbs the κ-deep prefix (`kappaPrefix_le_of_close`) and
      reaches every later fork choice (Lemma 4's machinery);
    * the **fast-confirm write** is a current-view quorum: the very next slot reads it
      directly (`le_mfc_at_*_of_quorum`), later slots through Lemma 3's propagation. -/
theorem chi_le_mfc {x : Exec Pr2 S}
    (hsync : SynchronizedClocks x) (hstepw : TimeStepwise x) (hdiv : TimeDiverges x)
    (hdil : Diligent x) (hone : OneTickPerReading x) (hwpt : WakePrecedesTick x)
    (hmc : S.MonotoneCorruption) (hsyn : Synchrony 0 Q.delta x) (hrel : Relay 0 Q.delta x)
    (hslp : Sleepiness Q S) (hcb : S.CorruptionBounded Q.f) (hfn : 3 * Q.f < n)
    (hcard : Fintype.card Node ≤ n) (hgst : Q.gst = 0)
    (hκ : 1 ≤ kappa) (hwin : HonestProposalWindow x) :
    ∀ (a : Nat) (vi : Node) (b : Nat) (vj : Node) (s0 : Nat),
      vj ∈ Active Q S ((s0 : Int) + 1) →
      ((x[b].time = Q.slotLength * (s0 + 1) → x[a].time ≤ Q.slotLength * (s0 + 1) →
        chainLe (x[a][vi].st.chi) (mfc (x[b][vj].view) (x[b][vj].view)
          (fastConfirmSimple n (x[b][vj].view) s0).1 (s0 + 1))) ∧
       (x.lbl b = .tick vj (Q.slotLength * (s0 + 1) + Q.delta) →
          x[a].time ≤ Q.slotLength * (s0 + 1) + Q.delta →
        chainLe (x[a][vi].st.chi)
          (mfc (processProposals2 n proposer (x[b][vj].view) (s0 + 1)
              (x[b][vj].st)).vFrozen (x[b][vj].view)
            (processProposals2 n proposer (x[b][vj].view) (s0 + 1)
              (x[b][vj].st)).chFrozen (s0 + 1)))) := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  have hmono := hstepw.timeMonotone
  have hSL0 : 0 < Q.slotLength := by omega
  intro a
  induction a with
  | zero =>
      intro vi b vj s0 hact
      have h0 : x[0][vi].st.chi = [] := by
        have h := x.init.2.1 vi
        show ((x.cfg 0)[vi]).st.chi = []
        rw [h]
        rfl
      exact ⟨fun _ _ => by rw [h0]; exact chainLe_nil _,
        fun _ _ => by rw [h0]; exact chainLe_nil _⟩
  | succ a ih =>
      intro vi b vj s0 hact
      rcases chi_step2 (x := x) (m := a) (p := vi) with hun | ⟨ti, hlbl, hguard, hchieq⟩ |
        ⟨ti, hlbl, hqsome, -, hchieq⟩
      · -- untouched: inherit
        have hle : x[a].time ≤ x[a + 1].time := time_le_of_le hmono (Nat.le_succ a)
        exact ⟨fun htb hab => by
            rw [hun]; exact (ih vi b vj s0 hact).1 htb (by omega),
          fun hjb hab => by
            rw [hun]; exact (ih vi b vj s0 hact).2 hjb (by omega)⟩
      · -- the κ-deep write
        have hta : x[a].time = Q.slotLength * ti + Q.delta := tick_reading hsync hlbl
        have hta1 : x[a + 1].time = x[a].time := tick_time hlbl
        have hMok := mfc_vote_ok hsync hstepw hdiv hdil hone hwpt hmc hsyn hslp hcb hfn
          hcard hgst (p := vi) (s := ti)
          (fun h1 => active_of_open_join hsync hstepw hdil hwpt h1 hlbl hta hguard) hlbl
        by_cases hshort : ti < kappa
        · -- below `κ`, nothing qualifies: the prefix is genesis
          have hnil : x[a + 1][vi].st.chi = [] := by
            rw [hchieq]
            exact kappaPrefix_nil_of_lt hshort _
          exact ⟨fun _ _ => by rw [hnil]; exact chainLe_nil _,
            fun _ _ => by rw [hnil]; exact chainLe_nil _⟩
        · -- from `κ` on: the window's honest proposal absorbs the prefix
          obtain ⟨t0, rfl⟩ : ∃ t0, ti = t0 + 1 := ⟨ti - 1, by omega⟩
          obtain ⟨tp, htp0, htp1, htp2, i, vp, chp, chC, qc, ck, hsent, hhon_i,
            hhon_t⟩ := hwin (t0 + 1) (by omega)
          obtain ⟨-, k, -, -, -, -, hchp_ext, -, -⟩ :=
            propose_provenance2 hsync hmc hmono hsent hhon_i rfl
          have hchp0 : chp ≠ [] := by
            rw [hchp_ext]
            unfold extend
            simp
          have hpa : proposedAt chp = tp := by
            rw [hchp_ext]
            exact proposedAt_extend _ _ _
          have hAVE : ∀ t', tp ≤ t' → ActiveVotesExtend2 x t' chp := fun t' ht' =>
            ave_of_honest_proposal hsync hstepw hdiv hdil hone hwpt hmc hsyn hrel hslp
              hcb hfn hcard hgst htp0 hsent hhon_i hhon_t ht'
          have hvi_act : vi ∈ Active Q S ((t0 : Int) + 1) := by
            have hcast : (((t0 + 1 : Nat)) : Int) = (t0 : Int) + 1 := by push_cast; omega
            rw [← hcast]
            exact active_of_open_join hsync hstepw hdil hwpt (by omega) hlbl hta hguard
          have hchpM := le_mfc_at_vote2 hsync hstepw hdil hwpt hone hmc hsyn hslp hcb hfn
            hgst (by omega : 1 ≤ t0) (hAVE t0 (by omega)) hvi_act hlbl
          have habs : chainLe (kappaPrefix kappa (t0 + 1) (mfc (processProposals2
              n proposer (x[a][vi].view) (t0 + 1) (x[a][vi].st)).vFrozen (x[a][vi].view)
              (processProposals2 n proposer (x[a][vi].view) (t0 + 1)
                (x[a][vi].st)).chFrozen (t0 + 1))) chp := by
            refine kappaPrefix_le_of_close hchpM hMok.1 hchp0 ?_
            rw [hpa]
            omega
          constructor
          · intro htb hab
            rw [hchieq]
            refine chainLe_trans habs ?_
            have hmul : Q.slotLength * (t0 + 1) < Q.slotLength * (s0 + 1) := by
              rw [hta1, hta] at hab
              omega
            have hts : t0 + 1 < s0 + 1 := Nat.lt_of_mul_lt_mul_left hmul
            exact le_mfc_at_propose_of_ave hsync hstepw hdil hwpt hone hmc hsyn hslp
              hcb hfn hcard hgst (by omega : 1 ≤ s0) (hAVE s0 (by omega)) htb hact
          · intro hjb hab
            rw [hchieq]
            refine chainLe_trans habs ?_
            have hmul : Q.slotLength * (t0 + 1) ≤ Q.slotLength * (s0 + 1) := by
              rw [hta1, hta] at hab
              omega
            have hts : t0 + 1 ≤ s0 + 1 := Nat.le_of_mul_le_mul_left hmul hSL0
            exact le_mfc_at_vote2 hsync hstepw hdil hwpt hone hmc hsyn hslp hcb hfn hgst
              (by omega : 1 ≤ s0) (hAVE s0 (by omega)) hact hjb
      · -- the fast-confirm write
        have hta : x[a].time = Q.slotLength * ti + 2 * Q.delta := tick_reading hsync hlbl
        have hta1 : x[a + 1].time = x[a].time := tick_time hlbl
        obtain ⟨cert, hcert⟩ := Option.isSome_iff_exists.mp hqsome
        have hfc : fastConfirmSimple n (x[a][vi].view) ti
            = ((fastConfirmSimple n (x[a][vi].view) ti).1, some cert) := by
          rw [← hcert]
        constructor
        · intro htb hab
          rw [hchieq]
          have hmul : Q.slotLength * ti < Q.slotLength * (s0 + 1) := by
            rw [hta1, hta] at hab
            omega
          have hts : ti < s0 + 1 := Nat.lt_of_mul_lt_mul_left hmul
          rcases Nat.lt_or_ge ti s0 with hlt | hge
          · have hAVE1 := activeVotesExtend_of_fastconfirm hsync hstepw hdiv hdil hone
              hmc hsyn hcb hfn hcard hta hfc
            have hAVEs := ave_propagate hsync hstepw hdiv hdil hone hwpt hmc hsyn hslp
              hcb hfn hgst (by omega : 1 ≤ ti + 1) hAVE1 (show ti + 1 ≤ s0 by omega)
            exact le_mfc_at_propose_of_ave hsync hstepw hdil hwpt hone hmc hsyn hslp
              hcb hfn hcard hgst (by omega : 1 ≤ s0) hAVEs htb hact
          · have hs0 : s0 = ti := by omega
            subst hs0
            exact le_mfc_at_propose_of_quorum hsync hstepw hone hmc hsyn hcb hfn hcard
              hta hfc htb hact
        · intro hjb hab
          rw [hchieq]
          have hmul : Q.slotLength * ti < Q.slotLength * (s0 + 1) := by
            rw [hta1, hta] at hab
            omega
          have hts : ti < s0 + 1 := Nat.lt_of_mul_lt_mul_left hmul
          rcases Nat.lt_or_ge ti s0 with hlt | hge
          · have hAVE1 := activeVotesExtend_of_fastconfirm hsync hstepw hdiv hdil hone
              hmc hsyn hcb hfn hcard hta hfc
            have hAVEs := ave_propagate hsync hstepw hdiv hdil hone hwpt hmc hsyn hslp
              hcb hfn hgst (by omega : 1 ≤ ti + 1) hAVE1 (show ti + 1 ≤ s0 by omega)
            exact le_mfc_at_vote2 hsync hstepw hdil hwpt hone hmc hsyn hslp hcb hfn hgst
              (by omega : 1 ≤ s0) hAVEs hact hjb
          · have hs0 : s0 = ti := by omega
            subst hs0
            exact le_mfc_at_vote_of_quorum hsync hstepw hdil hone hmc hsyn hcb hfn hcard
              hta hfc hact hjb

set_option maxHeartbeats 3000000 in
/-- **Theorem 2's liveness engine**: an honestly proposed chain at least `κ` slots
    stale is a prefix of the confirmed chain of every validator active at any strictly
    later round.

    The paper's argument, made inductive: the validator's activity window contains a
    vote round of some slot `s' ≥ tp + κ` (its activation rounds are vote rounds, so
    the first covered one past `voting(tp + κ)` qualifies); at that tick the fork
    choice sits above `chp` (Lemma 4's machinery) and its κ-deep prefix *retains* `chp`
    (`le_kappaPrefix_of_stale` — this is where the slot-indexed prefix earns its keep),
    so the κ-deep write lands at or above `chp` — the kept-old case is comparable with
    the prefix through the fork choice by Lemma 5's engine. From there the bound
    persists: later κ-deep writes retain `chp` the same way, and a fast-confirm write
    either adopts a chain extending `chp` or — when the quorum chain is `⪯ chp`, hence
    `⪯` the current chain — is stopped by Algorithm 5's line-23 guard. -/
theorem le_chi_of_honest_proposal {x : Exec Pr2 S}
    (hsync : SynchronizedClocks x) (hstepw : TimeStepwise x) (hdiv : TimeDiverges x)
    (hdil : Diligent x) (hone : OneTickPerReading x) (hwpt : WakePrecedesTick x)
    (hmc : S.MonotoneCorruption) (hsyn : Synchrony 0 Q.delta x) (hrel : Relay 0 Q.delta x)
    (hslp : Sleepiness Q S) (hcb : S.CorruptionBounded Q.f) (hfn : 3 * Q.f < n)
    (hcard : Fintype.card Node ≤ n) (hgst : Q.gst = 0) (hκ : 1 ≤ kappa)
    (hwin : HonestProposalWindow x)
    {tp : Nat} (htp : 1 ≤ tp) {vp : Node} {chp chC : Chain Tx}
    {qc : Option (QCert Node Tx)} {ck : Checkpoint (Chain Tx)} {ip : Nat}
    (hsent : (⟨vp, Msg.propose chp chC qc ck tp⟩ :
      SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ x[ip].sent)
    (hhon_i : vp ∉ S.adv ((x[ip].time : Int)))
    (hhon_t : vp ∉ S.adv (Q.voting (tp : Int)))
    {a : Nat} {vi : Node} (hact : ActiveAtRound Q S vi (x[a].time))
    (hlate : Q.slotLength * (tp + kappa) + Q.delta < x[a].time) :
    chainLe chp (x[a][vi].st.chi) := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  have hmono := hstepw.timeMonotone
  have hSL0 : 0 < Q.slotLength := by omega
  obtain ⟨tw, htw, hawake⟩ := hact
  -- every slot from `tp` on votes above `chp`
  have hAVE : ∀ t', tp ≤ t' → ActiveVotesExtend2 x t' chp := fun t' ht' =>
    ave_of_honest_proposal hsync hstepw hdiv hdil hone hwpt hmc hsyn hrel hslp hcb hfn
      hcard hgst htp hsent hhon_i hhon_t ht'
  -- the proposal's chain: slot-sorted, tipped at `tp`, nonempty
  obtain ⟨-, k, -, hlblk, htk, -, hchp_ext, -, -⟩ :=
    propose_provenance2 hsync hmc hmono hsent hhon_i rfl
  have hAwk : x.Awake k vp := by
    have hstep := x.step k
    rw [hlblk] at hstep
    have h := hstep.1
    simp only [spec] at h
    exact h
  obtain ⟨tp0, rfl⟩ : ∃ tp0, tp = tp0 + 1 := ⟨tp - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hchp_ext
  have hMokP := mfc_propose_ok hsync hstepw hdiv hdil hone hwpt hmc hsyn hslp hcb hfn
    hcard hgst (a := k) (w := vp) (t0 := tp0) htk hAwk
  have hchp_sorted : slotsIncreasing chp := by
    rw [hchp_ext]
    exact slotsIncreasing_extend pool hMokP.1 (lt_of_le_of_lt hMokP.2 (by omega))
  have hpa : proposedAt chp = tp0 + 1 := by
    rw [hchp_ext]
    exact proposedAt_extend _ _ _
  -- the first covered vote round past `voting(tp + κ)`
  obtain ⟨s', hs'w, hs'κ, hs'lt⟩ : ∃ s', tw ≤ s' ∧ tp0 + 1 + kappa ≤ s' ∧
      Q.slotLength * s' + Q.delta < x[a].time := by
    rcases Nat.le_total tw (tp0 + 1 + kappa) with hcmp | hcmp
    · exact ⟨tp0 + 1 + kappa, hcmp, le_refl _, hlate⟩
    · exact ⟨tw, le_refl _, hcmp, htw⟩
  have hmulw : Q.slotLength * tw ≤ Q.slotLength * s' := Nat.mul_le_mul_left _ hs'w
  -- `vi` is awake there, so it ticks there
  obtain ⟨i₁, hi₁⟩ := hdiv (Q.slotLength * s' + Q.delta)
  obtain ⟨i₀, hi₀, hti₀⟩ := exists_time_eq hstepw hi₁
  have hAw₀ : x.Awake i₀ vi := by
    show vi ∈ S.awake ((x[i₀].time : Int))
    rw [hti₀]
    refine hawake _ ?_ ?_
    · unfold Params.voting
      push_cast
      omega
    · exact_mod_cast le_of_lt hs'lt
  obtain ⟨j, htj, hlblj⟩ := hdil (Q.slotLength * s' + Q.delta) vi ⟨i₀, hti₀, hAw₀⟩
  -- the joining check is open at the tick
  have hopen : x[j][vi].st.activeAt ≤ Q.slotLength * s' + Q.delta := by
    refine activeAt_le_voting hsync hmono (t1 := s') ?_ (le_of_eq htj)
    intro ρ h1 h2
    refine hawake ρ ?_ ?_
    · have hmulI : (Q.slotLength : Int) * tw ≤ (Q.slotLength : Int) * s' := by
        exact_mod_cast hmulw
      unfold Params.voting
      push_cast at h1 ⊢
      omega
    · have hlt : ((Q.slotLength * s' + Q.delta : Nat) : Int) ≤ ((x[a].time : Nat) : Int) := by
        exact_mod_cast le_of_lt hs'lt
      omega
  -- so `vi` is active in slot `s'`
  have hs'1 : 1 ≤ s' := by omega
  have hActs' : vi ∈ Active Q S (s' : Int) :=
    active_of_open_join hsync hstepw hdil hwpt hs'1 hlblj htj hopen
  obtain ⟨s0, rfl⟩ : ∃ s0, s' = s0 + 1 := ⟨s' - 1, by omega⟩
  have hActs0 : vi ∈ Active Q S ((s0 : Int) + 1) := by
    have hcast : (((s0 + 1 : Nat)) : Int) = (s0 : Int) + 1 := by push_cast; omega
    rw [← hcast]
    exact hActs'
  -- the tick's fork choice sits above `chp` …
  have hchpM := le_mfc_at_vote2 hsync hstepw hdil hwpt hone hmc hsyn hslp hcb hfn hgst
    (by omega : 1 ≤ s0) (hAVE s0 (by omega)) hActs0 hlblj
  -- … the old confirmed chain sits below the same fork choice …
  have hold := (chi_le_mfc hsync hstepw hdiv hdil hone hwpt hmc hsyn hrel hslp hcb hfn
    hcard hgst hκ hwin j vi j vi s0 hActs0).2 hlblj (le_of_eq htj)
  -- … and the κ-deep write lands at or above `chp`
  obtain ⟨dt, hst, -⟩ := tick_effect hlblj
  have hvstate := handler2_vote_state (Q := Q) (n := n) (kappa := kappa) (pool := pool)
    (proposer := proposer) (dot := dt) (p := vi)
    (r := Q.slotLength * (s0 + 1) + Q.delta)
    (V := x[j][vi].view) (s := x[j][vi].st) (voting_reading_mod Q (s0 + 1))
  rw [voting_reading_div Q (s0 + 1)] at hvstate
  rw [hvstate, if_pos hopen] at hst
  set M := mfc (processProposals2 n proposer (x[j][vi].view) (s0 + 1)
      (x[j][vi].st)).vFrozen (x[j][vi].view)
    (processProposals2 n proposer (x[j][vi].view) (s0 + 1) (x[j][vi].st)).chFrozen
    (s0 + 1) with hMdef
  have hkp : chainLe chp (kappaPrefix kappa (s0 + 1) M) :=
    le_kappaPrefix_of_stale hchpM hchp_sorted (by rw [hpa]; omega)
  have hbase : chainLe chp (x[j + 1][vi].st.chi) := by
    have hchi : x[j + 1][vi].st.chi
        = [(processProposals2 n proposer (x[j][vi].view) (s0 + 1) (x[j][vi].st)).chi,
            kappaPrefix kappa (s0 + 1) M].foldl
            (fun acc c => if chainLe c M then (if chainLe acc c then c else acc)
              else acc)
            (processProposals2 n proposer (x[j][vi].view) (s0 + 1)
              (x[j][vi].st)).chi := by
      rw [hst]
    rw [processProposals2_chi] at hchi
    rw [List.foldl_cons, List.foldl_cons, List.foldl_nil] at hchi
    have hfold : x[j + 1][vi].st.chi = kappaPrefix kappa (s0 + 1) M ∨
        (x[j + 1][vi].st.chi = x[j][vi].st.chi ∧
          ¬ chainLe (x[j][vi].st.chi) (kappaPrefix kappa (s0 + 1) M)) := by
      rw [hchi]
      split_ifs <;>
        first
          | exact Or.inl rfl
          | exact Or.inr ⟨rfl, by assumption⟩
          | exact absurd (chainLe_refl _) (by assumption)
          | exact absurd (kappaPrefix_le_self _ _ _) (by assumption)
    rcases hfold with h | ⟨h, hneg⟩
    · rw [h]
      exact hkp
    · rw [h]
      rcases comparable_of_common_extension hold
          (kappaPrefix_le_self kappa (s0 + 1) M) with hok | hko
      · exact absurd hok hneg
      · exact chainLe_trans hkp hko
  -- the tick precedes `a` …
  have hja : j + 1 ≤ a := by
    rcases Nat.lt_or_ge j a with h | h
    · omega
    · exfalso
      have hle2 := time_le_of_le hmono h
      rw [htj] at hle2
      omega
  -- … and the bound persists to it
  have hpers : ∀ m, j + 1 ≤ m → chainLe chp (x[m][vi].st.chi) := by
    intro m
    induction m with
    | zero => omega
    | succ m ih =>
        intro hm
        rcases Nat.eq_or_lt_of_le hm with heq | hlt2
        · have hjm : j = m := by omega
          subst hjm
          exact hbase
        · have hprev := ih (by omega)
          have htm : Q.slotLength * (s0 + 1) + Q.delta ≤ x[m].time := by
            have h1 := time_le_of_le hmono (show j ≤ m by omega)
            rw [htj] at h1
            exact h1
          rcases chi_step2 (x := x) (m := m) (p := vi) with hun |
            ⟨t', hlbl', hguard', hchieq'⟩ | ⟨t', hlbl', hq', hgneg', hchieq'⟩
          · rw [hun]
            exact hprev
          · -- a later guarded κ-deep write retains `chp` the same way
            have hta' : x[m].time = Q.slotLength * t' + Q.delta :=
              tick_reading hsync hlbl'
            have ht's : s0 + 1 ≤ t' := by
              rw [hta'] at htm
              exact Nat.le_of_mul_le_mul_left (by omega) hSL0
            obtain ⟨t'0, rfl⟩ : ∃ u, t' = u + 1 := ⟨t' - 1, by omega⟩
            have hAct' : vi ∈ Active Q S ((t'0 : Int) + 1) := by
              have hcast : (((t'0 + 1 : Nat)) : Int) = (t'0 : Int) + 1 := by
                push_cast; omega
              rw [← hcast]
              exact active_of_open_join hsync hstepw hdil hwpt (by omega) hlbl'
                hta' hguard'
            have hchpM' := le_mfc_at_vote2 hsync hstepw hdil hwpt hone hmc hsyn hslp
              hcb hfn hgst (by omega : 1 ≤ t'0) (hAVE t'0 (by omega)) hAct' hlbl'
            rw [hchieq']
            exact le_kappaPrefix_of_stale hchpM' hchp_sorted (by rw [hpa]; omega)
          · -- a fast-confirm write: comparable with `chp`, and the line-23 guard
            -- blocks the regressive direction
            have hta' : x[m].time = Q.slotLength * t' + 2 * Q.delta :=
              tick_reading hsync hlbl'
            have ht's : s0 + 1 ≤ t' := by
              rw [hta'] at htm
              by_contra hc
              have hmm : Q.slotLength * t' ≤ Q.slotLength * s0 :=
                Nat.mul_le_mul_left _ (by omega)
              have hexp : Q.slotLength * (s0 + 1)
                  = Q.slotLength * s0 + Q.slotLength := Nat.mul_succ ..
              omega
            rcases fastConfirmSimple_fst_cases (n := n) (x[m][vi].view) t'
              with h0 | hsupp
            · exfalso
              refine hgneg' ?_
              rw [h0]
              exact chainLe_nil _
            · obtain ⟨q0, hq0mem, hq0hon⟩ :=
                exists_honest_sender (r := ((x[m].time : Int))) hcb hfn hsupp
              obtain ⟨smq, hsmq, hs0q⟩ := Finset.mem_image.mp hq0mem
              rw [Finset.mem_filter] at hsmq
              obtain ⟨hvq, hslotq, hchq⟩ := hsmq
              have hlogq : smq ∈ x[m].sent := views_sound x m vi _
                (by simp only [votes, Finset.mem_filter] at hvq; exact hvq.1)
              have hhonq : smq.sender ∉ S.adv ((x[m].time : Int)) := by
                rw [hs0q]
                exact hq0hon
              obtain ⟨eq', sq1, tq1, sq2, hmq⟩ := exists_vote_of_mem_votes hvq
              have hsq : sq2 = t' := by
                have e2 : msgSlot smq.msg = sq2 := by rw [hmq]; exact rfl
                omega
              subst hsq
              have hactq : smq.sender ∈ Active Q S (sq2 : Int) :=
                mem_active_of_honest_vote2 hsync hstepw hdil hwpt hmc (by omega)
                  hlogq hhonq hmq
              obtain ⟨iv, ev, evs, evt, htiv, hsentv, hextv⟩ :=
                hAVE sq2 (by omega) smq.sender hactq
              have hhon_iv : smq.sender ∉ S.adv ((x[iv].time : Int)) := by
                intro had
                refine hhonq (hmc _ _ ?_ had)
                rw [htiv, hta']
                exact_mod_cast (by omega : Q.slotLength * sq2 + Q.delta ≤
                  Q.slotLength * sq2 + 2 * Q.delta)
              have huniq : (⟪vote, ev, evs, evt, sq2, smq.sender⟫ :
                  SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) = smq :=
                honest_vote_unique2 hsync hone hmc hmono hlogq hsentv hhonq hhon_iv
                  rfl hmq rfl
              have hchain : msgChain smq.msg = ev := by rw [← huniq]; exact rfl
              rcases comparable_of_common_extension hchq
                  (show chainLe chp (msgChain smq.msg) by
                    rw [hchain]; exact hextv) with hbc | hcb2
              · exact absurd (chainLe_trans hbc hprev) hgneg'
              · rw [hchieq']
                exact hcb2
  exact hpers a hja

end Lemma5

end Majorum
