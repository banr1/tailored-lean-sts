import Examples.StsMultisetLog.majorum.Spec.Security
import Examples.StsMultisetLog.majorum.Analysis.Proofs.Availability5
import Examples.StsMultisetLog.majorum.Analysis.Proofs.Finality5

/-!
# Definitions 4 and 7 for Algorithm 5

The last assembly of Appendix C: **Theorem 4** as Definition 4 (`chainava` is dynamically
available) and **Theorem 7** as Definition 7 (Algorithm 5 is a secure ebb-and-flow protocol).
Both are re-cuts of results proved elsewhere — `Availability5.theorem4` and, for the finalized
chain, `Finality5`'s Theorem 6 development — into the shapes `Spec/Security.lean` states, so
that `Analysis/Theorems.lean` can name them in one line each.

## What the paper's Lemma 1 becomes

Definition 2 asks that a pooled transaction reach *every* active validator's chain within
`Tconf`, so the finalized half needs an honest proposer to turn up, and Theorem 6 needs two in
consecutive slots. The paper has that from Lemma 1, with overwhelming probability. There is no
probability layer here, so `HonestProposerPairs` assumes it, with an explicit window `W` — the
parameter that makes `Tconf` finite. `MfcEquiv.HonestProposalWindow5` will not substitute: it
gives *one* honest proposal per `κ` slots, and Cases 1 and 2 of Theorem 6 each need two.
-/

set_option autoImplicit false

namespace Majorum.EbbAndFlow5

open the framework's flat multiset-log flavour

variable {Node Tx : Type} [DecidableEq Node] [DecidableEq Tx] [Fintype Node]
  {Q : Params} {S : Schedule Node} {kappa : Nat} {pool : Nat → Tx} {proposer : Nat → Node}

/-- Algorithm 5, its quorum threshold instantiated with the structural validator count. -/
local notation "Pr5" =>
  protocol (components (Fintype.card Node) kappa pool proposer) Q

local notation "M" => Msg (Chain Tx) (QCert Node Tx)

/-- **Lemma 1, as a hypothesis with an explicit window.** From any time `τ`, a pair of
    consecutive slots `t`, `t+1` with honest proposers, `propose(t)` landing in
    `[τ, τ + W·4Δ]`. Each half carries what the Theorem 6 development consumes: the proposal
    in the log, and the proposer honest both when it emitted and at its slot's vote round. -/
def HonestProposerPairs (W : Nat) (x5 : Exec Pr5 S) : Prop :=
  ∀ τ : Time, ∃ t : Nat, 1 ≤ t ∧ τ ≤ Q.slotLength * t ∧
    Q.slotLength * t ≤ τ + Q.slotLength * W ∧
    ∃ (ip : Nat) (vp : Node) (chp chC : Chain Tx) (qc : Option (QCert Node Tx))
      (gjp : Checkpoint (Chain Tx)),
      (⟨vp, Msg.propose chp chC qc gjp t⟩ : SignedMsg Node M) ∈ x5[ip].sent ∧
      vp ∉ S.adv ((x5[ip].time : Int)) ∧ vp ∉ S.adv (Q.voting (t : Int)) ∧
      ∃ (ip' : Nat) (vp' : Node) (chp' chC' : Chain Tx) (qc' : Option (QCert Node Tx))
        (gjp' : Checkpoint (Chain Tx)),
        (⟨vp', Msg.propose chp' chC' qc' gjp' (t + 1)⟩ : SignedMsg Node M) ∈ x5[ip'].sent ∧
        vp' ∉ S.adv ((x5[ip'].time : Int)) ∧
        vp' ∉ S.adv (Q.voting (((t + 1 : Nat)) : Int))

/-- "`q` proposed `o` in slot `t`", for Algorithm 5: an honest emission of a slot-`t` proposal
    whose chain is `o`. Honesty *at the emission* is part of the predicate, as it is in
    `MfcEquiv.HonestProposalWindow5`; honesty later in the slot is what `ReorgResilient` asks
    for separately. -/
def proposedBy5 (x5 : Exec Pr5 S) (t : Int) (q : Node) (o : Chain Tx) : Prop :=
  ∃ tn : Nat, 1 ≤ tn ∧ (tn : Int) = t ∧
    ∃ (chC : Chain Tx) (qc : Option (QCert Node Tx)) (ck : Checkpoint (Chain Tx)) (i : Nat),
      (⟨q, Msg.propose o chC qc ck tn⟩ : SignedMsg Node M) ∈ x5[i].sent ∧
      q ∉ S.adv ((x5[i].time : Int))

/-- **Theorem 3 as Definition 5**, with `proposing := voting`: an honestly proposed chain
    never conflicts with any validator's available chain, at any round.

    **The round matters, and it is not the paper's.** Definition 5 asks this of a proposer
    "honest in `propose(t)`"; here it is asked of one honest at `voting(t)`, which is a
    stronger hypothesis and so a weaker theorem. The propose-round version is *false* of this
    model, and of the paper's: the adversary is adaptive, so a proposer honest when it
    proposes can be corrupted before the vote round and equivocate, and two valid slot-`t`
    proposals split the honest votes — after which nothing pins the later fork choice to
    either chain. Constraint (1) does not help; it bounds corruption of *voters* after a
    voting phase, not of the proposer before one. See the fifteenth finding in
    `Examples/StsMultisetLog/majorum/CONTEXT.md`. -/
theorem reorgResilient5 {x5 : Exec Pr5 S} (H5 : SettingGA Q S x5) (hκ : 1 ≤ kappa)
    (hwin5 : MfcEquiv.HonestProposalWindow5 (kappa := kappa) x5) :
    ReorgResilient (fun p c => c[p].st.chAva) (fun a b => a ⪯ b) (proposedBy5 x5)
      (fun t => Q.voting t) 0 0 x5 := by
  intro i p q t o _ _ _ hprop hhon
  obtain ⟨tn, htn1, htneq, chC, qc, ck, ip, hsent, hhon_i⟩ := hprop
  have hhon_t : q ∉ S.adv (Q.voting ((tn : Nat) : Int)) := by rw [htneq]; exact hhon
  rcases Availability5.theorem3 H5 hκ hwin5 htn1 hsent hhon_i hhon_t i p with h | h
  · exact fun hc => hc.1 h
  · exact fun hc => hc.2 h

set_option maxHeartbeats 1000000 in
/-- **Theorem 4 as Definition 4**: `chainava` is dynamically available — `SecureActive` from
    time 0, over the paper's `H_r`, with `Tconf = 8κΔ + Δ + 1` (spelled
    `slotLength * 2κ + Δ + 1`).

    Both halves are `Availability5.theorem4`'s, re-cut to Definitions 1–2: safety is
    unconditional, and for liveness the slot the paper's proof works in is `⌊r / 4Δ⌋`, whose
    `+2κ` vote round has passed by `r + Tconf`. The `+1` is the model's strict inequality at
    that round; the paper's `Tconf = O(κ)` absorbs it. -/
theorem dynamicallyAvailable5 {x5 : Exec Pr5 S} {τ : Type}
    (memTx : τ → Tx → Prop) (poolSet : Time → Set τ)
    (hmonoP : ∀ r r' : Time, r ≤ r' → poolSet r ⊆ poolSet r')
    (hcover : ∀ s : Nat, ∀ tx ∈ poolSet (Q.slotLength * s), memTx tx (pool s))
    (H5 : SettingGA Q S x5) (hκ : 1 ≤ kappa)
    (hwin5 : MfcEquiv.HonestProposalWindow5 (kappa := kappa) x5) :
    DynamicallyAvailable (fun p c => c[p].st.chAva) (fun a b => a ⪯ b)
      (fun (tx : τ) (o : Chain Tx) => ∃ b ∈ o, memTx tx b.txs) poolSet
      (ActiveAtRound Q S) 0 (Q.slotLength * (2 * kappa) + Q.delta + 1) x5 := by
  obtain ⟨hsafe, hlive⟩ := Availability5.theorem4 memTx poolSet hmonoP hcover H5 hκ hwin5
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  refine ⟨fun i j p q _ _ _ _ => hsafe i p j q, ?_⟩
  intro i j p tx _ htx hlate hact
  have hdm : Q.slotLength * (x5[i].time / Q.slotLength) + x5[i].time % Q.slotLength
      = x5[i].time := Nat.div_add_mod _ _
  have hmod : x5[i].time % Q.slotLength < Q.slotLength :=
    Nat.mod_lt _ (by rw [hsl]; omega)
  have hbase : Q.slotLength * (x5[i].time / Q.slotLength) ≤ x5[i].time := Nat.le.intro hdm
  refine hlive (x5[i].time / Q.slotLength) j p hact ?_ x5[i].time ?_ tx htx
  · -- the `+2κ` vote round has passed
    have hstep : Q.slotLength * (x5[i].time / Q.slotLength + 2 * kappa) + Q.delta
        = Q.slotLength * (x5[i].time / Q.slotLength)
          + (Q.slotLength * (2 * kappa) + Q.delta) := by
      rw [Nat.mul_add, Nat.add_assoc]
    rw [hstep]
    refine lt_of_lt_of_le (lt_of_le_of_lt (Nat.add_le_add_right hbase _) ?_) hlate
    exact Nat.add_lt_add_left (Nat.lt_succ_self _) _
  · -- and the pooling round is inside slot `⌊r / 4Δ⌋`
    have h1 : Q.slotLength * (x5[i].time / Q.slotLength) + x5[i].time % Q.slotLength
        ≤ Q.slotLength * (x5[i].time / Q.slotLength) + Q.slotLength :=
      Nat.add_le_add_left (Nat.le_of_lt hmod) _
    rw [hdm] at h1
    have hexp : Q.slotLength * (x5[i].time / Q.slotLength + 1)
        = Q.slotLength * (x5[i].time / Q.slotLength) + Q.slotLength := Nat.mul_succ ..
    rw [hexp]
    exact h1

set_option maxHeartbeats 1000000 in
/-- **Theorem 7 as Definition 7**: Algorithm 5 is a secure ebb-and-flow protocol.

    * `chainava` is dynamically available — `dynamicallyAvailable5`, relaxed to the shared
      confirmation time (`LiveActive.mono_tconf`);
    * `chainfin` is always safe (`Finality5.chFin_comparable`, at every pair of indices) and
      live after `max(GST, GAT) + slack`: the liveness half runs Theorem 6 at the honest pair
      `HonestProposerPairs` provides, splitting on the second proposer's carried checkpoint
      exactly as the paper's proof does — Case 1 when it is of slot `t`, Case 2 when it is
      not, which is Lemma 18 one slot up;
    * `chainfin ⪯ chainava` — `Finality5.chFin_le_chAva5`.

    `GST = 0`, as `SettingGA` fixes it. The two chains' confirmation times differ and
    Definition 7 states one, so `tconf` must dominate both: `4Δ·2κ + Δ + 1` for the available
    chain, `4Δ·(W + 4) + 2Δ` for the finalized one, whose `+4` is Case 2's extra slot. `slack`
    need only clear `2Δ`, which is what puts the pair's vote window past `GAT`.

    A validator active at the later round need not have been active in slot `t+3` or `t+4`
    itself: past `GAT` every honest validator is awake (`GlobalAwakeTime`) and corruption is
    monotone, so activity at any later round hands back activity at those slots. -/
theorem secureEbbAndFlow5 {x5 : Exec Pr5 S} {τ : Type}
    (memTx : τ → Tx → Prop) (poolSet : Time → Set τ)
    (hmonoP : ∀ r r' : Time, r ≤ r' → poolSet r ⊆ poolSet r')
    (hcover : ∀ s : Nat, ∀ tx ∈ poolSet (Q.slotLength * s), memTx tx (pool s))
    (H5 : SettingGA Q S x5) (hκ : 1 ≤ kappa)
    (hwin5 : MfcEquiv.HonestProposalWindow5 (kappa := kappa) x5)
    (hga : S.GlobalAwakeTime Q.gat Finset.univ)
    {W : Nat} (hpairs : HonestProposerPairs W x5)
    {slack tconf : Time} (hslack : 2 * Q.delta ≤ slack)
    (htc1 : Q.slotLength * (2 * kappa) + Q.delta + 1 ≤ tconf)
    (htc2 : Q.slotLength * (W + 4) + 2 * Q.delta ≤ tconf) :
    SecureEbbAndFlow (fun p c => c[p].st.chAva) (fun p c => c[p].st.chFin) (fun a b => a ⪯ b)
      (fun (tx : τ) (o : Chain Tx) => ∃ b ∈ o, memTx tx b.txs) poolSet (ActiveAtRound Q S)
      0 Q.gat slack tconf x5 := by
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  obtain ⟨⟨hmc, hah, hsync, hmono, -, -, -⟩, -, -, hone, -, -, ⟨hcb, hfn⟩, -⟩ := id H5
  refine ⟨⟨(dynamicallyAvailable5 memTx poolSet hmonoP hcover H5 hκ hwin5).1,
      (dynamicallyAvailable5 memTx poolSet hmonoP hcover H5 hκ hwin5).2.mono_tconf htc1⟩,
    ⟨fun i j p q _ _ _ _ =>
      Finality5.chFin_comparable hsync hmono hone hmc hcb hfn i p j q, ?_⟩,
    fun i p _ => Finality5.chFin_le_chAva5 hsync hmono hone hmc hcb hfn i p⟩
  -- the finalized chain's liveness, after `max(0, GAT) + slack`
  intro i j p tx hafter htx hlate hact
  have hgat_le : Q.gat + slack ≤ x5[i].time := by
    have h := le_max_right 0 Q.gat
    omega
  -- the honest pair of slots past the pooling round
  obtain ⟨t, ht1, htlo, hthi, ip, vp, chp, chC, qc, gjp, hsent, hhon_i, hhon_t,
    ip', vp', chp', chC', qc', gjp', hsent', hhon_i', hhon_t'⟩ := hpairs x5[i].time
  -- `p` is honest at the later round, hence honest and awake from `GAT` on
  obtain ⟨t', ht'lt, hawk'⟩ := hact
  have hawkj : p ∈ S.awake ((x5[j].time : Int)) := by
    refine hawk' ((x5[j].time : Int)) ?_ (le_refl _)
    have h1 : Q.voting ((t' : Nat) : Int) = ((Q.slotLength * t' + Q.delta : Nat) : Int) := by
      unfold Params.voting
      push_cast
      omega
    have h2 : ((Q.slotLength * t' + Q.delta : Nat) : Int) ≤ ((x5[j].time : Int)) := by
      have h : Q.slotLength * t' + Q.delta ≤ x5[j].time := by omega
      exact_mod_cast h
    rw [h1]
    omega
  have hhonj : p ∉ S.adv ((x5[j].time : Int)) := Finset.disjoint_left.mp (hah _) hawkj
  -- activity in any slot whose vote window sits between `GAT` and the later round
  have hactive_of : ∀ s : Nat, Q.gat + 3 * Q.delta ≤ Q.slotLength * s + Q.delta →
      Q.slotLength * s + Q.delta ≤ x5[j].time → p ∈ Active Q S (((s : Nat)) : Int) := by
    intro s hlo hhi
    have hvots : Q.voting (((s : Nat)) : Int) = ((Q.slotLength * s + Q.delta : Nat) : Int) := by
      unfold Params.voting
      push_cast
      omega
    have hcastlo : ((Q.gat + 3 * Q.delta : Nat) : Int)
        ≤ ((Q.slotLength * s + Q.delta : Nat) : Int) := by exact_mod_cast hlo
    have hcasthi : ((Q.slotLength * s + Q.delta : Nat) : Int) ≤ ((x5[j].time : Int)) := by
      exact_mod_cast hhi
    refine mem_awakeThroughout.mpr ?_
    intro ρ h1 h2
    rw [hvots] at h1 h2
    have hρ1 : (Q.gat : Int) ≤ ρ := by push_cast at hcastlo; omega
    have hρ2 : ρ ≤ ((x5[j].time : Int)) := by omega
    have hhonρ : p ∉ S.adv ρ := fun hadv => hhonj (hmc ρ _ hρ2 hadv)
    exact hga ρ hρ1 (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hhonρ⟩)
  -- the slot arithmetic: the pair's vote window is past `GAT`, and slot `t+4`'s fast confirm
  -- has passed by the later round
  have hexpW : Q.slotLength * (W + 4) = Q.slotLength * W + Q.slotLength * 4 := Nat.mul_add ..
  have hexp4 : Q.slotLength * (t + 1 + 1 + 1 + 1)
      = Q.slotLength * t + Q.slotLength * 4 := by
    have h : t + 1 + 1 + 1 + 1 = t + 4 := by omega
    rw [h, Nat.mul_add]
  have hexp3 : Q.slotLength * (t + 1 + 1 + 1) = Q.slotLength * t + Q.slotLength * 3 := by
    have h : t + 1 + 1 + 1 = t + 3 := by omega
    rw [h, Nat.mul_add]
  have hgatT : (Q.gat : Int) ≤ Q.voting (t : Int) - 3 * (Q.delta : Int) := by
    have hvotT : Q.voting (t : Int) = ((Q.slotLength * t + Q.delta : Nat) : Int) := by
      unfold Params.voting
      push_cast
      omega
    have hnat : Q.gat + 2 * Q.delta ≤ Q.slotLength * t := by omega
    have hcast : ((Q.gat + 2 * Q.delta : Nat) : Int) ≤ ((Q.slotLength * t : Nat) : Int) := by
      exact_mod_cast hnat
    have hsplit : ((Q.slotLength * t + Q.delta : Nat) : Int)
        = ((Q.slotLength * t : Nat) : Int) + ((Q.delta : Nat) : Int) :=
      Nat.cast_add (Q.slotLength * t) Q.delta
    rw [hvotT, hsplit]
    push_cast at hcast ⊢
    omega
  have hgat1 := Finality5.gat_le_voting_succ5 hgatT
  -- the two branches of the paper's proof
  by_cases hgjc : gjp'.c = t
  · -- Case 1: the slot-`(t+1)` proposal carries a slot-`t` checkpoint
    refine Finality5.chFin_txpool5 memTx poolSet hmonoP hcover H5 hκ hwin5 hga ht1 hsent
      hhon_i (Finality5.slotPinned_case1_5 H5 hκ hwin5 hga ht1 hsent hhon_i hhon_t hgatT
        hsent' hhon_i' hhon_t' hgjc).self hgat1
      (hactive_of (t + 1 + 1 + 1) (by omega) (by omega)) (by omega) htlo tx htx
  · -- Case 2: it does not, so Lemma 18 applies at slot `t+1`
    exact Finality5.chFin_txpool_case2_5 memTx poolSet hmonoP hcover H5 hκ hwin5 hga ht1
      hsent' hhon_i' hhon_t' hgjc hgatT
      (hactive_of (t + 1 + 1 + 1 + 1) (by omega) (by omega)) (by omega) htlo tx htx

end Majorum.EbbAndFlow5
