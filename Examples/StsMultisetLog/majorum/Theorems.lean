import Examples.StsMultisetLog.majorum.Assumptions
import Examples.StsMultisetLog.majorum.Security
import Examples.StsMultisetLog.majorum.Lemmas

/-!
# Majorum's theorems, as statements

All seven theorems of arXiv:2601.03862v1, rendered in the vocabulary of
`Security.lean` as **statements** (`def … : Prop`), plus — at the end of the file —
the theorems *proved* for Algorithm 2 concretely (`theorem1`, `theorem2_safety`,
`theorem2_liveness`, `theorem2_liveness_txpool`, 2026-08-04), in the same
direct style as `Lemmas.lean` rather than through the `Security.lean` renderings (which
quantify differently: no probability layer, and a hypothesis row that predates
`SettingGA`).

## Why these are `def … : Prop` and not `theorem`

The repository forbids `sorry`: a statement that cannot be proved is not to be stated as a
theorem. Writing the paper's claims as `Prop`-valued definitions says exactly what is
intended — *this is the proposition* — without asserting it. When a proof arrives, it
becomes `theorem foo : ThmLiveness … := …` and the definition is what it proves.

## What each statement is missing

The paper's theorems are one line each because they cite the definitions; the content is in
`Security.lean`, and so are the caveats. Two apply throughout:

* Four of the seven hold **with overwhelming probability**. There is no probability layer,
  so the qualifier is dropped and the statement below is *not* the paper's claim.
* The two algorithms are not modelled. Every statement is therefore parameterised by the
  model rather than asserted of a protocol, and which algorithm a theorem is about survives
  only as a section heading. Two pairs of statements consequently coincide.

Slots: the paper's slot `t` spans `4Δ` rounds, `proposing t` and `voting t` are rounds
within it. They are fields of this directory's own `Params`, in `Assumptions.lean`; nothing
here depends on `the framework's flat multiset-log flavour.Models`.
-/

set_option autoImplicit false

namespace Majorum

open the framework's flat multiset-log flavour

variable {Node Msg NodeState Ev Out Tx : Type} [Fintype Node] [DecidableEq Node]
  [DecidableEq Msg] {Pr : Protocol Node Msg NodeState Ev} {S : Schedule Node}

/-! ### The dynamically available component — Algorithm `prob-ga-fast` (§ GA-based) -/

/-- **Theorem `Theorem 1`** (Reorg Resilience). "Algorithm `prob-ga-fast` is
    reorg-resilient." Unqualified, so after slot 0 and time 0.

    A **theorem**, not a property: it quantifies over the executions the paper's model
    admits, rather than taking one as a parameter. An earlier version took `x` as an
    argument and so asserted nothing — instantiated at a hostile execution it is simply
    false.

    Assumptions: `Wellformed`, `Network`, `Sleepiness`, `Resilience`. The corruption bound
    `f < n/3` comes with `Q` (it is `Params.fBound`), and Constraint (1) is the paper's
    standing requirement for slots after GST (the model section).

    **Not yet checked against the paper**: whether the GA section fixes further standing
        assumptions. Its theorems sit at Theorems 1 and 2, before the the FFG analysis preamble
    block that assumes
    `GST = 0` for the FFG analysis, so they inherit the model section and possibly more. -/
def ThmReorgResilienceGA (Q : Params) (out : Node → Config Node Msg NodeState → Out)
    (Pre : Out → Out → Prop) (proposedBy : Int → Node → Out → Prop) : Prop :=
  ∀ x : Exec Pr S,
    Wellformed x → Network Q x → Sleepiness Q S → Resilience Q S →
    ReorgResilient out Pre proposedBy Q.proposing 0 0 x

/-- **Theorem 2.** "Algorithm `prob-ga-fast` is dynamically-available `\wop`."

    Reviewed. Unqualified dynamic availability is Definition 4's second sentence — "always
    secure when `GST = 0`" — so `tdyn = 0` and the network assumption is `Synchronous`, the
    `Δ` bound holding from the start, rather than `Network`, which only binds after `Q.gst`.
    That distinction is the whole content of the qualifier and is easy to lose: passing
    `Network Q x` here would state something the paper does not claim.

    The `\wop` is dropped, so this is the deterministic shadow of the theorem — see the
    module docstring. `tconf` stands for Definition 4's `O(κ)`.

    Same open question as Theorem 1: whether the GA section fixes standing assumptions
    beyond `f < n/3` and Constraint (1).

    (This statement was silently lost when Theorem 1 was corrected — a span replacement
    swallowed it — and is restored here.) -/
def ThmDynamicAvailabilityGA (Q : Params)
    (out : Node → Config Node Msg NodeState → Out) (Pre : Out → Out → Prop)
    (mem : Tx → Out → Prop) (pool : Time → Set Tx) (tconf : Time) : Prop :=
  ∀ x : Exec Pr S,
    Wellformed x → Synchronous Q x → Sleepiness Q S → Resilience Q S →
    DynamicallyAvailable out Pre mem pool 0 tconf x

/-! ### Not yet reviewed

Everything below still has the two defects `ThmReorgResilienceGA` was just corrected for:
it takes the execution as a **parameter** rather than quantifying over the ones the model
admits, so it asserts nothing; and it therefore names no assumptions, where the paper gives
each theorem its own. They are being worked through one at a time.

### The full protocol — Algorithm `3sf-tob-noga` (§ FFG) -/

/-- **Theorem `Theorem 3`** (Reorg Resilience, analogous of
    `Theorem 1`). "Algorithm `3sf-tob-noga` is reorg-resilient."

    Signature updated to track `ReorgResilient`'s corrected one; the statement itself is
    still unreviewed — it takes `x` as a parameter and names no assumptions. -/
def ThmReorgResilienceFFG (out : Node → Config Node Msg NodeState → Out)
    (Pre : Out → Out → Prop) (proposedBy : Int → Node → Out → Prop)
    (proposing : Int → Int) (x : Exec Pr S) : Prop :=
  ReorgResilient out Pre proposedBy proposing 0 0 x

/-- **Theorem `Theorem 4`** (dynamic availability, analogous of
    `Theorem 2`). "Algorithm `3sf-tob-noga` is dynamically-available
    `\wop`." -/
def ThmDynamicAvailabilityFFG (out : Node → Config Node Msg NodeState → Out)
    (Pre : Out → Out → Prop) (mem : Tx → Out → Prop) (pool : Time → Set Tx) (tconf : Time)
    (x : Exec Pr S) : Prop :=
  DynamicallyAvailable out Pre mem pool 0 tconf x

/-- **Theorem `Theorem 5`** (Accountable Safety). "Let `f ∈ [0, n]`. The
    finalized chain `chainfin` is `n/3`-accountable."

    `n / 3` is `Nat` division, which truncates; the paper's `n/3` is exact and the
    resilience is the largest integer below it. For `n` not divisible by 3 these agree; at
    `n = 3k` the paper's reading is `k`, and so is this. Left as `n / 3` rather than
    parameterised, because the constant is the content of the theorem. -/
def ThmAccountableSafety (finalized : Node → Config Node Msg NodeState → Out)
    (Pre : Out → Out → Prop) (culprits : Multiset (SignedMsg Node Msg) → Finset Node)
    (n : Nat) (x : Exec Pr S) : Prop :=
  AccountableSafety finalized Pre culprits (n / 3) x

/-- **Theorem `Theorem 6`** (Liveness). "Assume `f < n/3`, and let `t` and `t+1`
    be slots after `max(GST, GAT) + 4Δ`. Then the chain `chain_p` proposed by the proposer
    of slot `t` is finalized at slot `t+2` or slot `t+3`. In particular, for any validator
    `v_i ∈ H_r` where `r ≥ 4Δ(t+3) + 2Δ`, it holds that `chain_p ⪯ chainfin^r_i` and
    `txpool^{proposing t} ⊆ chainfin^r_i`."

    The only theorem in the paper whose statement is not a one-line citation, so it is the
    only one rendered in full. Both conclusions of the "in particular" are here; the
    "finalized at slot `t+2` or `t+3`" sentence is *implied* by them for this model, since
    the framework has no notion of "finalized at slot `s`" separate from what validators
    output — that would need a per-slot finalization predicate the model does not have.

    `f < n/3` and the slot arithmetic `4Δ(t+3) + 2Δ` are hypotheses of the caller, not of
    this proposition: the first is a `Schedule` constraint, the second is spelled out. -/
def ThmLiveness (finalized : Node → Config Node Msg NodeState → Out) (Pre : Out → Out → Prop)
    (mem : Tx → Out → Prop) (pool : Time → Set Tx) (proposedBy : Time → Out → Prop)
    (proposing : Time → Time) (delta gst gat : Time) (x : Exec Pr S) : Prop :=
  ∀ (t : Time) (chainP : Out),
    max gst gat + 4 * delta ≤ 4 * delta * t →
    proposedBy t chainP →
    ∀ (i : Nat) (p : Node),
      4 * delta * (t + 3) + 2 * delta ≤ x[i].time → x.Honest i p →
      Pre chainP (finalized p x[i]) ∧
        ∀ tx ∈ pool (proposing t), mem tx (finalized p x[i])

/-- **Theorem `Theorem 7`.** "Algorithm `3sf-tob-noga` is a secure ebb-and-flow
    protocol `\wop`." -/
def ThmEbbAndFlow (available finalized : Node → Config Node Msg NodeState → Out)
    (Pre : Out → Out → Prop) (mem : Tx → Out → Prop) (pool : Time → Set Tx)
    (gst gat slack tconf : Time) (x : Exec Pr S) : Prop :=
  SecureEbbAndFlow available finalized Pre mem pool gst gat slack tconf x

end Majorum

/-! ### Proved: Algorithm 2, concretely

In a fresh namespace scope: the statement block above declares `Msg` as a *type
variable* (the abstract renderings range over any message type), which would shadow
Algorithm 5's `Msg` inductive here. -/

namespace Majorum

open the framework's flat multiset-log flavour

section Algorithm2Proved

variable {Node Tx : Type} [DecidableEq Node] [DecidableEq Tx] [Fintype Node]
  {Q : Params} {S : Schedule Node} {kappa : Nat} {pool : Nat → Tx}
  {proposer : Nat → Node}

/-- Algorithm 2, its quorum threshold instantiated with the structural validator count —
    the same protocol `Lemmas.lean` states the lemmas over. -/
local notation "Pr2" => protocol2 Q (Fintype.card Node) kappa pool proposer

/-- **Theorem 1** (`Theorem 1, arXiv:2601.03862v1 p.16`, Reorg Resilience, for
    Algorithm 2). An honestly proposed chain never conflicts with any validator's
    confirmed chain: `chp` and `Ch^{ri}_i` are comparable, at every index.

    The paper's proof, followed exactly: pick a slot `tj` past both `tp` and `ri`'s
    slot; `Sleepiness` makes `H_vote(tj)` inhabited, `TimeDiverges`/`Diligent` produce
    an active validator's vote tick there; Lemma 4's machinery puts `chp` below that
    tick's fork choice, Lemma 5 puts `Ch^{ri}_i` below the same fork choice, and two
    prefixes of one chain are comparable.

    Hypotheses as in `lemma5`: `SettingGA`, `1 ≤ κ`, and `HonestProposalWindow` (the
    de-probabilized Lemma 1) — the paper's "w.o.p." qualifier lives in the latter. The
    conclusion is `¬ Conflicts` unfolded (`Security.Conflicts`: neither is a prefix of
    the other); `vi`'s honesty is not needed, as in Lemma 5. -/
theorem theorem1 {x : Exec Pr2 S} (H : SettingGA Q S x) (hκ : 1 ≤ kappa)
    (hwin : HonestProposalWindow x)
    {tp : Nat} (htp : 1 ≤ tp) {vp : Node} {chp chC : Chain Tx}
    {qc : Option (QCert Node Tx)} {ck : Checkpoint (Chain Tx)} {i : Nat}
    (hsent : (⟨vp, Msg.propose chp chC qc ck tp⟩ :
      SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ x[i].sent)
    (hhon_i : vp ∉ S.adv ((x[i].time : Int)))
    (hhon_t : vp ∉ S.adv (Q.voting (tp : Int)))
    (a : Nat) (vi : Node) :
    chp ⪯ x[a][vi].st.chi ∨ x[a][vi].st.chi ⪯ chp := by
  obtain ⟨⟨hmc, -, hsync, -, -, hdiv, hdil⟩, hstepw, hwpt, hone, ⟨hsyn, hrel⟩, hslp,
    ⟨hcb, hfn⟩, hgst⟩ := id H
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  have hmono := hstepw.timeMonotone
  have hSL0 : 0 < Q.slotLength := by omega
  -- a slot past both the proposal and `ri`
  set s0 := max tp (x[a].time / Q.slotLength) with hs0def
  have htps0 : tp ≤ s0 := le_max_left _ _
  have hs01 : 1 ≤ s0 := le_trans htp htps0
  -- `H_vote(s0+1)` is inhabited
  have hgstok : (Q.gst : Int) ≤ Q.proposing ((s0 : Int) + 1 + 1) := by
    rw [hgst]
    unfold Params.proposing
    push_cast
    exact mul_nonneg (Int.natCast_nonneg _) (by omega)
  have hcount := hslp ((s0 : Int) + 1 + 1) hgstok
  rw [show ((s0 : Int) + 1 + 1 - 1) = (s0 : Int) + 1 by omega] at hcount
  have hpos : 0 < (Active Q S ((s0 : Int) + 1) \
      S.adv (Q.voting ((s0 : Int) + 1 + 1))).card := by omega
  obtain ⟨vj, hvjmem⟩ := Finset.card_pos.mp hpos
  have hvj : vj ∈ Active Q S ((s0 : Int) + 1) := (Finset.mem_sdiff.mp hvjmem).1
  -- its vote tick at `voting(s0+1)`
  have hvot1 : Q.voting ((s0 : Int) + 1)
      = ((Q.slotLength * (s0 + 1) + Q.delta : Nat) : Int) := by
    unfold Params.voting
    push_cast
    omega
  obtain ⟨i₁, hi₁⟩ := hdiv (Q.slotLength * (s0 + 1) + Q.delta)
  obtain ⟨i₀, hi₀, hti₀⟩ := exists_time_eq hstepw hi₁
  have hAw0 : x.Awake i₀ vj := by
    show vj ∈ S.awake ((x[i₀].time : Int))
    rw [hti₀]
    refine mem_awakeThroughout.mp hvj _ ?_ ?_ <;> rw [hvot1] <;> omega
  obtain ⟨j, htj, hlblj⟩ := hdil (Q.slotLength * (s0 + 1) + Q.delta) vj ⟨i₀, hti₀, hAw0⟩
  -- Lemma 4's side: the proposal is below the tick's fork choice
  have hAVE : ActiveVotesExtend2 x s0 chp :=
    ave_of_honest_proposal hsync hstepw hdiv hdil hone hwpt hmc hsyn hrel hslp hcb hfn
      (le_refl _) hgst htp hsent hhon_i hhon_t htps0
  have h4 := le_mfc_at_vote2 hsync hstepw hdil hwpt hone hmc hsyn hslp hcb hfn hgst
    hs01 hAVE hvj hlblj
  -- Lemma 5's side: the confirmed chain is below the same fork choice
  have hact : vj ∈ Active Q S (((s0 + 1 : Nat)) : Int) := by
    have hcast : (((s0 + 1 : Nat)) : Int) = (s0 : Int) + 1 := by push_cast; omega
    rw [hcast]
    exact hvj
  have hab : x[a].time ≤ Q.slotLength * (s0 + 1) + Q.delta := by
    have hdm := Nat.div_add_mod (x[a].time) Q.slotLength
    have hml := Nat.mod_lt (x[a].time) hSL0
    have hq1 : Q.slotLength * (x[a].time / Q.slotLength + 1)
        ≤ Q.slotLength * (s0 + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have hexp : Q.slotLength * (x[a].time / Q.slotLength + 1)
        = Q.slotLength * (x[a].time / Q.slotLength) + Q.slotLength := Nat.mul_succ ..
    omega
  have h5 := (lemma5 (a := a) (vi := vi) (b := j) (vj := vj) H hκ hwin
    (show 1 ≤ s0 + 1 by omega) hact).2 hlblj hab
  exact comparable_of_common_extension h4 h5

/-- **Theorem 2, the safety half** (`Theorem 2, arXiv:2601.03862v1 p.17`, for
    Algorithm 2). Any two validators' confirmed chains, at any two points of the
    execution, are comparable — the paper's "we now show safety" paragraph: pick a slot
    `tk` past both rounds, Constraint (1) makes `H_vote(tk)` inhabited, and Lemma 5
    bounds both confirmed chains by the same validator's fork choice there.

    Stated (and named) as a *half*: the paper's Theorem 2 is dynamic availability,
    safety **and liveness** with `Tconf = 8κΔ + Δ` — the liveness half is
    `theorem2_liveness` / `theorem2_liveness_txpool` below. Honesty of neither
    validator is assumed, as in Lemma 5. -/
theorem theorem2_safety {x : Exec Pr2 S} (H : SettingGA Q S x) (hκ : 1 ≤ kappa)
    (hwin : HonestProposalWindow x) (a : Nat) (vi : Node) (b : Nat) (vj : Node) :
    x[a][vi].st.chi ⪯ x[b][vj].st.chi ∨ x[b][vj].st.chi ⪯ x[a][vi].st.chi := by
  obtain ⟨⟨hmc, -, hsync, -, -, hdiv, hdil⟩, hstepw, hwpt, hone, ⟨hsyn, hrel⟩, hslp,
    ⟨hcb, hfn⟩, hgst⟩ := id H
  have hδ := Q.deltaPos
  have hsl : Q.slotLength = 4 * Q.delta := rfl
  have hmono := hstepw.timeMonotone
  have hSL0 : 0 < Q.slotLength := by omega
  -- a slot past both rounds
  set s0 := max (x[a].time / Q.slotLength) (x[b].time / Q.slotLength) with hs0def
  have hs0a : x[a].time / Q.slotLength ≤ s0 := le_max_left _ _
  have hs0b : x[b].time / Q.slotLength ≤ s0 := le_max_right _ _
  clear_value s0
  -- `H_vote(s0+1)` is inhabited
  have hgstok : (Q.gst : Int) ≤ Q.proposing ((s0 : Int) + 1 + 1) := by
    rw [hgst]
    unfold Params.proposing
    push_cast
    exact mul_nonneg (Int.natCast_nonneg _) (by omega)
  have hcount := hslp ((s0 : Int) + 1 + 1) hgstok
  rw [show ((s0 : Int) + 1 + 1 - 1) = (s0 : Int) + 1 by omega] at hcount
  have hpos : 0 < (Active Q S ((s0 : Int) + 1) \
      S.adv (Q.voting ((s0 : Int) + 1 + 1))).card := by omega
  obtain ⟨vk, hvkmem⟩ := Finset.card_pos.mp hpos
  have hvk : vk ∈ Active Q S ((s0 : Int) + 1) := (Finset.mem_sdiff.mp hvkmem).1
  -- its vote tick at `voting(s0+1)`
  have hvot1 : Q.voting ((s0 : Int) + 1)
      = ((Q.slotLength * (s0 + 1) + Q.delta : Nat) : Int) := by
    unfold Params.voting
    push_cast
    omega
  obtain ⟨i₁, hi₁⟩ := hdiv (Q.slotLength * (s0 + 1) + Q.delta)
  obtain ⟨i₀, hi₀, hti₀⟩ := exists_time_eq hstepw hi₁
  have hAw0 : x.Awake i₀ vk := by
    show vk ∈ S.awake ((x[i₀].time : Int))
    rw [hti₀]
    refine mem_awakeThroughout.mp hvk _ ?_ ?_ <;> rw [hvot1] <;> omega
  obtain ⟨j, htj, hlblj⟩ := hdil (Q.slotLength * (s0 + 1) + Q.delta) vk ⟨i₀, hti₀, hAw0⟩
  have hact : vk ∈ Active Q S (((s0 + 1 : Nat)) : Int) := by
    have hcast : (((s0 + 1 : Nat)) : Int) = (s0 : Int) + 1 := by push_cast; omega
    rw [hcast]
    exact hvk
  -- both confirmed chains sit below `vk`'s fork choice there
  have htime : ∀ c : Nat, c ∈ ({a, b} : Set Nat) →
      x[c].time / Q.slotLength ≤ s0 → x[c].time ≤ Q.slotLength * (s0 + 1) + Q.delta := by
    intro c _ hcs
    have hdm := Nat.div_add_mod (x[c].time) Q.slotLength
    have hml := Nat.mod_lt (x[c].time) hSL0
    have hq1 : Q.slotLength * (x[c].time / Q.slotLength + 1)
        ≤ Q.slotLength * (s0 + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have hexp : Q.slotLength * (x[c].time / Q.slotLength + 1)
        = Q.slotLength * (x[c].time / Q.slotLength) + Q.slotLength := Nat.mul_succ ..
    omega
  have h5a := (lemma5 (a := a) (vi := vi) (b := j) (vj := vk) H hκ hwin
    (show 1 ≤ s0 + 1 by omega) hact).2 hlblj
    (htime a (Or.inl rfl) hs0a)
  have h5b := (lemma5 (a := b) (vi := vj) (b := j) (vj := vk) H hκ hwin
    (show 1 ≤ s0 + 1 by omega) hact).2 hlblj
    (htime b (Or.inr rfl) hs0b)
  exact comparable_of_common_extension h5a h5b

/-- **Theorem 2, the liveness half** (`Theorem 2, arXiv:2601.03862v1 p.17`, for
    Algorithm 2), the chain fact: past any slot `t`, once `2κ` slots and a round have
    gone by, every validator active at that round confirms a chain extending some
    honest proposal from the window `[t+1, t+κ]`.

    This is the paper's `Tconf = 8κΔ + Δ` claim: `hri` reads
    `ri > vote(t + 2κ) = 4Δt + 8κΔ + Δ ≥ r + Tconf` for any round `r` of slot `t` (the
    strict `<` is the one-round shift of `ActiveAtRound`, see its docstring). The
    honest window slot exists by `HonestProposalWindow` — Lemma 1, where the paper says
    "there is a high probability of finding a slot `tp ∈ [t+1, t+κ]` hosted by an
    honest proposer". The transaction-pool conclusion is `theorem2_liveness_txpool`. -/
theorem theorem2_liveness {x : Exec Pr2 S} (H : SettingGA Q S x) (hκ : 1 ≤ kappa)
    (hwin : HonestProposalWindow x) {t : Nat}
    {a : Nat} {vi : Node} (hact : ActiveAtRound Q S vi (x[a].time))
    (hri : Q.slotLength * (t + 2 * kappa) + Q.delta < x[a].time) :
    ∃ tp, t + 1 ≤ tp ∧ tp ≤ t + kappa ∧
      ∃ (ip : Nat) (vp : Node) (chp chC : Chain Tx) (qc : Option (QCert Node Tx))
        (ck : Checkpoint (Chain Tx)),
        (⟨vp, Msg.propose chp chC qc ck tp⟩ :
          SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ x[ip].sent ∧
        vp ∉ S.adv ((x[ip].time : Int)) ∧ vp ∉ S.adv (Q.voting (tp : Int)) ∧
        chp ⪯ x[a][vi].st.chi := by
  obtain ⟨⟨hmc, -, hsync, -, -, hdiv, hdil⟩, hstepw, hwpt, hone, ⟨hsyn, hrel⟩, hslp,
    ⟨hcb, hfn⟩, hgst⟩ := id H
  obtain ⟨tp, htp0, htp1, htp2, ip, vp, chp, chC, qc, ck, hsent, hh1, hh2⟩ :=
    hwin (t + kappa + 1) (by omega)
  refine ⟨tp, by omega, by omega, ip, vp, chp, chC, qc, ck, hsent, hh1, hh2, ?_⟩
  refine le_chi_of_honest_proposal hsync hstepw hdiv hdil hone hwpt hmc hsyn hrel hslp
    hcb hfn (le_refl _) hgst hκ hwin htp0 hsent hh1 hh2 hact ?_
  have hmul : Q.slotLength * (tp + kappa) ≤ Q.slotLength * (t + 2 * kappa) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-- **Theorem 2, the liveness half, with the transaction pool** — Definition 2's
    shape. The mempool is interpreted at the statement level (decision of 2026-08-04,
    `CONTEXT.md`): `poolSet r` is the pool's content at round `r` over some transaction
    type `τ`, `memTx` reads the abstract block payloads, `hmonoP` is the paper's
    "ever-growing set", and `hcover` renders `Extend`'s contract — the body an honest
    slot-`s` proposer packs covers the pool at `propose(s)` (the "Property 1" the
    paper's proof cites but never states). Any transaction pooled by a round of slot
    `t` is then in a block of every sufficiently-later active validator's confirmed
    chain. -/
theorem theorem2_liveness_txpool {x : Exec Pr2 S} {τ : Type}
    (memTx : τ → Tx → Prop) (poolSet : Time → Set τ)
    (hmonoP : ∀ r r' : Time, r ≤ r' → poolSet r ⊆ poolSet r')
    (hcover : ∀ s : Nat, ∀ tx ∈ poolSet (Q.slotLength * s), memTx tx (pool s))
    (H : SettingGA Q S x) (hκ : 1 ≤ kappa) (hwin : HonestProposalWindow x)
    {t : Nat} {a : Nat} {vi : Node} (hact : ActiveAtRound Q S vi (x[a].time))
    (hri : Q.slotLength * (t + 2 * kappa) + Q.delta < x[a].time)
    {r : Time} (hr : r ≤ Q.slotLength * (t + 1)) :
    ∀ tx ∈ poolSet r, ∃ b ∈ x[a][vi].st.chi, memTx tx b.txs := by
  obtain ⟨tp, htp1, htp2, ip, vp, chp, chC, qc, ck, hsent, hh1, hh2, hle⟩ :=
    theorem2_liveness H hκ hwin hact hri (t := t)
  obtain ⟨⟨hmc, -, hsync, -, -, hdiv, hdil⟩, hstepw, -, -, -, -, -, -⟩ := id H
  obtain ⟨-, k, -, -, -, -, hchp_ext, -, -⟩ :=
    propose_provenance2 hsync hmc hstepw.timeMonotone hsent hh1 rfl
  intro tx htx
  refine ⟨⟨tp, pool tp⟩, ?_, ?_⟩
  · -- the proposal's own block sits in the confirmed chain
    have hmem : (⟨tp, pool tp⟩ : Block Tx) ∈ chp := by
      rw [hchp_ext]
      unfold extend
      simp
    have hsub : chp ⊆ x[a][vi].st.chi := by
      have h := hle
      rw [chainLe_iff_prefix] at h
      exact h.subset
    exact hsub hmem
  · -- and its body covers the pool at `propose(tp)`, hence at `r`
    refine hcover tp tx (hmonoP r (Q.slotLength * tp) ?_ htx)
    have hmul : Q.slotLength * (t + 1) ≤ Q.slotLength * tp :=
      Nat.mul_le_mul_left _ (by omega)
    omega

end Algorithm2Proved

end Majorum
