import Examples.StsMultisetLog.majorum.Nda.Provenance2

/-!
# Lemma 2 for the nondeterministic-assignment Algorithm 2

`Majorum.lemma2`, restated and re-proved over `Nda.protocol2` — same statement,
same proof, against the membership-style handler. Its existence is the point of the
`Nda` comparison: once `mem_handler2_iff` recovers the deterministic core, nothing
downstream changes.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 400

namespace Majorum.Nda

open the framework's flat multiset-log flavour

variable {Node Tx : Type} [DecidableEq Node] [DecidableEq Tx] [Fintype Node]
  {Q : Params} {S : Schedule Node} {kappa : Nat} {pool : Nat → Tx} {proposer : Nat → Node}

/-- Algorithm 2, its quorum threshold instantiated with the structural validator count.
    The paper's "·" — the blank finality fields — is nondeterministic in the protocol
    itself: each tick fills it with any value. -/
local notation "Pr2" => protocol2 Q (Fintype.card Node) kappa pool proposer

/-- **Lemma 2** (`Lemma 2, arXiv:2601.03862v1 p.8`, for Algorithm 2). If, in slot `t`,
    all validators in `H_vote(t)` send vote messages for chains extending `ch`, then, in
    slot `t+1`, all validators in `H_vote(t+1)` send vote messages for chains extending
    `ch`.

    Hypotheses: `SettingGA`, the bundled setting of the whole Appendix-A analysis. The
    proof: a validator active in slot `t+1` ticks at `voting(t+1)` with the joining check
    open (`activeAt_le_voting` — the framework's wake event fires only on sleep→awake
    transitions, so no wake inside the activity window can close it), and the vote that
    tick sends extends this tick's fork-choice (`handler2_vote_send`), which extends `ch`
    by `le_mfc_at_vote2`. -/
theorem lemma2 {x : Exec Pr2 S} (H : SettingGA Q S x)
    {t : Nat} (ht : 1 ≤ t) {ch : Chain Tx} (hvotes : ActiveVotesExtend2 x t ch) :
    ActiveVotesExtend2 x (t + 1) ch := by
  obtain ⟨⟨hmc, -, hsync, -, -, hdiv, hdil⟩, hstepw, hwpt, hone, ⟨hsyn, -⟩, hslp,
    ⟨hcb, hfn⟩, hgst⟩ := H
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
  -- the vote tick of `p` at `voting(t+1)` exists: time diverges, `p` is awake there,
  -- and a diligent validator ticks every reading it is awake for
  obtain ⟨i₁, hi₁⟩ := hdiv (Q.slotLength * (t + 1) + Q.delta)
  obtain ⟨i₀, hi₀, hti₀⟩ := exists_time_eq hstepw hi₁
  have hAw0 : x.Awake i₀ p := by
    show p ∈ S.awake ((x[i₀].time : Int))
    rw [hti₀]
    refine mem_awakeThroughout.mp hp _ ?_ ?_ <;> rw [hvot1] <;> omega
  obtain ⟨j, htj, hlblj⟩ := hdil (Q.slotLength * (t + 1) + Q.delta) p ⟨i₀, hti₀, hAw0⟩
  -- the joining check is open at that tick
  have hgate : x[j][p].st.activeAt ≤ Q.slotLength * (t + 1) + Q.delta := by
    refine activeAt_le_voting hsync hmono (t1 := t + 1) ?_ (le_of_eq htj)
    intro r h1 h2
    refine mem_awakeThroughout.mp hp _ ?_ ?_ <;> rw [hvot1] <;> omega
  -- so the tick votes — with whatever filler it chose — for an extension of its
  -- fork-choice, which does not depend on the filler
  obtain ⟨dotj, -, hemit⟩ := tick_effect hlblj
  obtain ⟨chS, hsend, hchS⟩ :=
    handler2_vote_send (Q := Q) (n := Fintype.card Node) (kappa := kappa) (pool := pool)
      (proposer := proposer) (dot := dotj) (p := p) (V := x[j][p].view) (s := x[j][p].st)
      (voting_reading_mod Q (t + 1)) hgate
  rw [voting_reading_div Q (t + 1)] at hsend hchS
  -- and the fork-choice extends `ch`: the vote-round half
  have hmfc := le_mfc_at_vote2 hsync hstepw hdil hwpt hone hmc hsyn hslp hcb hfn hgst
    ht hvotes hp hlblj
  have hchain : chainLe ch chS := chainLe_trans hmfc hchS
  have hmem : (⟨p, Msg.vote chS dotj dotj (t + 1)⟩ :
      SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ x[j + 1].sent := by
    refine hemit _ ?_
    rw [hsend]
    exact Multiset.mem_singleton_self _
  exact ⟨j + 1, chS, dotj, dotj, by rw [tick_time hlblj, htj], hmem, hchain⟩

end Majorum.Nda
