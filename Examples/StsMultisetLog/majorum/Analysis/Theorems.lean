import Examples.StsMultisetLog.majorum.Spec.Assumptions
import Examples.StsMultisetLog.majorum.Spec.Security
import Examples.StsMultisetLog.majorum.Analysis.Proofs.Analysis2
import Examples.StsMultisetLog.majorum.Analysis.Proofs.Availability5
import Examples.StsMultisetLog.majorum.Analysis.Proofs.Finality5

/-!
# Majorum's theorems, as statements

All seven theorems of arXiv:2601.03862v1, rendered in the vocabulary of
`Security.lean` as **statements** (`def … : Prop`), plus — at the end of the file —
the theorems *proved* for Algorithm 2 concretely (`theorem1` and `theorem2`,
2026-08-04), in the same direct style as `Analysis/Lemmas.lean` rather than through the
`Security.lean` renderings (which quantify differently: no probability layer, and a
hypothesis row that predates `SettingGA`).

**Proof convention (2026-08-04)**: only the paper's actual theorems appear here, each
proved by a single call into `Analysis2.lean`; the split faces Theorem 2 is assembled
from (`theorem2_safety`, `theorem2_liveness`, `theorem2_liveness_txpool`) live there.

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

One-call faces of `Analysis2.lean`'s assembled results. In a fresh namespace scope:
the statement block above declares `Msg` as a *type variable* (the abstract renderings
range over any message type), which would shadow Algorithm 5's `Msg` inductive here. -/

namespace Majorum

open the framework's flat multiset-log flavour

section Algorithm2Proved

variable {Node Tx : Type} [DecidableEq Node] [DecidableEq Tx] [Fintype Node]
  {Q : Params} {S : Schedule Node} {kappa : Nat} {pool : Nat → Tx}
  {proposer : Nat → Node}

/-- Algorithm 2, its quorum threshold instantiated with the structural validator count —
    the same protocol `Analysis/Lemmas.lean` states the lemmas over. -/
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
    chp ⪯ x[a][vi].st.chi ∨ x[a][vi].st.chi ⪯ chp :=
  Analysis2.theorem1 H hκ hwin htp hsent hhon_i hhon_t a vi

/-- **Theorem 2** (`Theorem 2, arXiv:2601.03862v1 p.17`, for Algorithm 2). "Algorithm
    `prob-ga-fast` is dynamically-available w.o.p." — Definition 4: always secure when
    `GST = 0`, that is, **safe** and **live** with `Tconf = O(κ)`, here `8κΔ + Δ`.

    * The **safety** conjunct: any two validators' confirmed chains, at any two points
      of the execution, are comparable. Honesty of neither validator is assumed.
    * The **liveness** conjunct, Definition 2's shape: any transaction pooled by a
      round of slot `t` is in a block of the confirmed chain of every validator active
      at any round past `vote(t + 2κ)`. The mempool is interpreted at the statement
      level (`CONTEXT.md`, 2026-08-04): `poolSet` is the pool's content over some
      transaction type `τ`, `memTx` reads the abstract block payloads, `hmonoP` is the
      paper's "ever-growing set", and `hcover` renders `Extend`'s contract — the
      "Property 1" the paper's proof cites but never states.

    The "w.o.p." lives in `HonestProposalWindow`, Lemma 1 de-probabilized, as
    throughout; `1 ≤ κ` the paper needs too. Assembled in `Analysis2.lean` from
    `theorem2_safety` and `theorem2_liveness_txpool` (with `theorem2_liveness` the
    chain fact under the txpool conclusion). -/
theorem theorem2 {x : Exec Pr2 S} {τ : Type}
    (memTx : τ → Tx → Prop) (poolSet : Time → Set τ)
    (hmonoP : ∀ r r' : Time, r ≤ r' → poolSet r ⊆ poolSet r')
    (hcover : ∀ s : Nat, ∀ tx ∈ poolSet (Q.slotLength * s), memTx tx (pool s))
    (H : SettingGA Q S x) (hκ : 1 ≤ kappa) (hwin : HonestProposalWindow x) :
    (∀ (a : Nat) (vi : Node) (b : Nat) (vj : Node),
      x[a][vi].st.chi ⪯ x[b][vj].st.chi ∨ x[b][vj].st.chi ⪯ x[a][vi].st.chi) ∧
    (∀ (t a : Nat) (vi : Node), ActiveAtRound Q S vi (x[a].time) →
      Q.slotLength * (t + 2 * kappa) + Q.delta < x[a].time →
      ∀ r : Time, r ≤ Q.slotLength * (t + 1) →
      ∀ tx ∈ poolSet r, ∃ b ∈ x[a][vi].st.chi, memTx tx b.txs) :=
  Analysis2.theorem2 memTx poolSet hmonoP hcover H hκ hwin

end Algorithm2Proved

/-! ### Proved: Algorithm 5, concretely

Appendix C.1's two theorems, in the same direct style — the available chain in place of
Algorithm 2's confirmed chain. Both reach Appendix A through Lemma 10's MFC-equivalent
run; the assembly is in `Analysis/Proofs/Availability5.lean`. -/

section Algorithm5Proved

variable {Node Tx : Type} [DecidableEq Node] [DecidableEq Tx] [Fintype Node]
  {Q : Params} {S : Schedule Node} {kappa : Nat} {pool : Nat → Tx}
  {proposer : Nat → Node}

/-- Algorithm 5, its quorum threshold instantiated with the structural validator count. -/
local notation "Pr5" =>
  protocol (components (Fintype.card Node) kappa pool proposer) Q

/-- **Theorem 3** (`Theorem 3, arXiv:2601.03862v1 p.21`, Reorg Resilience, for
    Algorithm 5). An honestly proposed chain never conflicts with any validator's
    *available* chain — `ReorgResilient` for `chainava`, unqualified.

    The paper's proof is Theorem 1's with `Chain` replaced by `chainava`, Lemma 4 by Lemma
    12 and Lemma 5 by Lemma 13, and that is how it is proved here: a slot past both the
    proposal and the round in question has an active validator (Constraint (1)) whose vote
    tick bounds both chains from above.

    Hypotheses as for Theorem 1, with `HonestProposalWindow5` — Lemma 1 de-probabilized,
    stated over Algorithm-5 runs — carrying the paper's "w.o.p.". -/
theorem theorem3 {x5 : Exec Pr5 S} (H : SettingGA Q S x5) (hκ : 1 ≤ kappa)
    (hwin : MfcEquiv.HonestProposalWindow5 (kappa := kappa) x5)
    {tp : Nat} (htp : 1 ≤ tp) {vp : Node} {chp chC : Chain Tx}
    {qc : Option (QCert Node Tx)} {ck : Checkpoint (Chain Tx)} {i : Nat}
    (hsent : (⟨vp, Msg.propose chp chC qc ck tp⟩ :
      SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ x5[i].sent)
    (hhon_i : vp ∉ S.adv ((x5[i].time : Int)))
    (hhon_t : vp ∉ S.adv (Q.voting (tp : Int)))
    (a : Nat) (vi : Node) :
    chp ⪯ x5[a][vi].st.chAva ∨ x5[a][vi].st.chAva ⪯ chp :=
  Availability5.theorem3 H hκ hwin htp hsent hhon_i hhon_t a vi

/-- **Theorem 4** (`Theorem 4, arXiv:2601.03862v1 p.22`, for Algorithm 5). "Algorithm
    `3sf-tob-noga` is dynamically-available w.o.p." — Definition 4 for `chainava`, with
    `Tconf = 8κΔ + Δ` as in Theorem 2.

    * **Safety**: any two validators' available chains, at any two points, are comparable.
      Proved through Lemma 10: each is dominated by an Algorithm-2 confirmed chain
      (conditions 2.3/2.4) and those are comparable by Theorem 2.
    * **Liveness**: any transaction pooled by a round of slot `t` is in a block of the
      available chain of every validator active past `vote(t + 2κ)`. The mempool is
      interpreted at the statement level exactly as in Theorem 2.

    The paper's proof is Theorem 2's with `chainava` for `Chain` and Lemmas 12/13 for 4/5,
    plus the extra case its Algorithm-5 `chainava` write forces — the fast-confirm round
    can adopt the greatest justified chain, which is handled here (as the paper does) by the
    justified descent plus Theorem 3. -/
theorem theorem4 {x5 : Exec Pr5 S} {τ : Type}
    (memTx : τ → Tx → Prop) (poolSet : Time → Set τ)
    (hmonoP : ∀ r r' : Time, r ≤ r' → poolSet r ⊆ poolSet r')
    (hcover : ∀ s : Nat, ∀ tx ∈ poolSet (Q.slotLength * s), memTx tx (pool s))
    (H : SettingGA Q S x5) (hκ : 1 ≤ kappa)
    (hwin : MfcEquiv.HonestProposalWindow5 (kappa := kappa) x5) :
    (∀ (a : Nat) (vi : Node) (b : Nat) (vj : Node),
      x5[a][vi].st.chAva ⪯ x5[b][vj].st.chAva ∨
        x5[b][vj].st.chAva ⪯ x5[a][vi].st.chAva) ∧
    (∀ (t a : Nat) (vi : Node), ActiveAtRound Q S vi (x5[a].time) →
      Q.slotLength * (t + 2 * kappa) + Q.delta < x5[a].time →
      ∀ r : Time, r ≤ Q.slotLength * (t + 1) →
      ∀ tx ∈ poolSet r, ∃ b ∈ x5[a][vi].st.chAva, memTx tx b.txs) :=
  Availability5.theorem4 memTx poolSet hmonoP hcover H hκ hwin

/-- **Theorem 5** (`Theorem 5, arXiv:2601.03862v1 p.23`, Accountable Safety). The finalized
    chain is `n/3`-accountable: on a safety violation between two honest validators, the
    messages sent name at least `n/3` validators, and no validator is ever named while
    honest.

    This one *is* the `Security.lean` rendering — `ThmAccountableSafety` with the naming
    procedure supplied (`culprits5`: the validators whose own fin-votes in the log violate
    E1 or E2) — because Definition 6 carries no probability layer and no hypothesis row of
    its own. As in the paper, no corruption bound is assumed (`f ∈ [0, n]`); the two
    conjuncts are Lemma 9's counting and Lemma 15. -/
theorem theorem5 {x5 : Exec Pr5 S} (H : SettingGA Q S x5) (hne : Nonempty Node) :
    ThmAccountableSafety (fun p c => c[p].st.chFin) (fun a b => a ⪯ b)
      Finality5.culprits5 (Fintype.card Node) x5 :=
  Finality5.theorem5 H.wellformed.2.2.1 H.wellformed.2.2.2.1 H.oneTick H.wellformed.1
    Fintype.card_pos

/-- **The finalized chain is safe** — Theorem 6's safety half, and Definition 7's second
    conjunct in part: any two validators' finalized chains are comparable. Each prefixes a
    checkpoint finalized in its own view, and those nest by Lemma 8 once `f < n/3` rules out
    the slashing alternative. -/
theorem chFin_safe {x5 : Exec Pr5 S} (H : SettingGA Q S x5)
    (i : Nat) (p : Node) (j : Nat) (q : Node) :
    x5[i][p].st.chFin ⪯ x5[j][q].st.chFin ∨ x5[j][q].st.chFin ⪯ x5[i][p].st.chFin :=
  Finality5.chFin_comparable H.wellformed.2.2.1 H.wellformed.2.2.2.1 H.oneTick
    H.wellformed.1 H.resilience.1 H.resilience.2 i p j q

/-- **The finalized chain is a prefix of the available chain** — Definition 7's third
    conjunct, at every validator and round. -/
theorem chFin_le_chAva {x5 : Exec Pr5 S} (H : SettingGA Q S x5) (i : Nat) (p : Node) :
    x5[i][p].st.chFin ⪯ x5[i][p].st.chAva :=
  Finality5.chFin_le_chAva5 H.wellformed.2.2.1 H.wellformed.2.2.2.1 H.oneTick
    H.wellformed.1 H.resilience.1 H.resilience.2 i p

/-- **Theorem 6's liveness half, in the regime Lemma 18 covers**
    (`Theorem 6, arXiv:2601.03862v1 p.24`). With honest proposers at slots `t` and `t+1` —
    the paper's "let `t` and `t+1` be slots after `max(GST, GAT) + 4Δ`", whose honesty its
    proof takes from Lemma 1 — and a slot-`t` proposal whose carried checkpoint is older than
    the previous slot, the proposed chain prefixes the finalized chain of every validator
    active in slot `t+3`, from `fconf(t+3)` on: `chp ⪯ chainfin^r_i`.

    Two things this is not. It is **not** the whole of Theorem 6: the paper splits on
    `GJ^{propose(t)}_p.c`, and the complementary case `= t − 1` (its Case 1 and Case 2) is
    still owed — that case reaches `(chp, t+1)` through the slot-`(t+1)` proposer's own
    checkpoint rather than through re-justification. And the transaction-pool clause
    (`txpool^{propose(t)} ⊆ chainfin^r_i`) is not included; it is Lemma 6's, as in Theorem 4's
    liveness half.

    The activity hypothesis replaces the paper's `v_i ∈ H_r`, for the reason Theorem 4's
    liveness half carries one: a validator that has just woken has written nothing, and this
    model starts `chainfin` at genesis. -/
theorem theorem6_liveness_of_low {x5 : Exec Pr5 S} (H : SettingGA Q S x5) (hκ : 1 ≤ kappa)
    (hwin : MfcEquiv.HonestProposalWindow5 (kappa := kappa) x5)
    (hga : S.GlobalAwakeTime Q.gat Finset.univ)
    {t : Nat} (ht : 1 ≤ t)
    {vp : Node} {chp chC : Chain Tx} {qc : Option (QCert Node Tx)}
    {gjp : Checkpoint (Chain Tx)} {ip : Nat}
    (hsent : (⟨vp, Msg.propose chp chC qc gjp t⟩ :
      SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ x5[ip].sent)
    (hhon_i : vp ∉ S.adv ((x5[ip].time : Int)))
    (hhon_t : vp ∉ S.adv (Q.voting (t : Int)))
    (hlow : gjp.c < t - 1)
    (hgat : (Q.gat : Int) ≤ Q.voting (t : Int) - 3 * (Q.delta : Int))
    {vp' : Node} {chp' chC' : Chain Tx} {qc' : Option (QCert Node Tx)}
    {gjp' : Checkpoint (Chain Tx)} {ip' : Nat}
    (hsent' : (⟨vp', Msg.propose chp' chC' qc' gjp' (t + 1)⟩ :
      SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ x5[ip'].sent)
    (hhon_i' : vp' ∉ S.adv ((x5[ip'].time : Int)))
    (hhon_t' : vp' ∉ S.adv (Q.voting (((t + 1 : Nat)) : Int)))
    {vi : Node} {a : Nat} (hact3 : vi ∈ Active Q S (((t + 1 + 1 + 1 : Nat)) : Int))
    (hlate : Q.slotLength * (t + 1 + 1 + 1) + 2 * Q.delta ≤ x5[a].time) :
    chp ⪯ x5[a][vi].st.chFin :=
  Finality5.chp_le_chFin5 H hκ hwin hga hsent' hhon_i' hhon_t'
    (Finality5.slotPinned_next5 H hκ hwin hga ht hsent hhon_i hhon_t
      (Finality5.slotPinned_of_low H hκ hwin hga ht hsent hhon_i hhon_t hlow hgat) hgat
      hsent' hhon_i' hhon_t')
    (Finality5.gat_le_voting_succ5 hgat) hact3 hlate

/-- **Theorem 6's liveness half with the transaction pool**, in the same regime: every
    transaction pooled by a round of slot `t` sits in a block of the finalized chain from
    `fconf(t+3)` on. The pool is interpreted at the statement level exactly as in Theorems 2
    and 4 — `poolSet` for what is pooled by a round, `memTx` for membership in a block's
    body, and `hcover` tying the two at slot boundaries. -/
theorem theorem6_liveness_txpool_of_low {x5 : Exec Pr5 S} {τ : Type}
    (memTx : τ → Tx → Prop) (poolSet : Time → Set τ)
    (hmonoP : ∀ r r' : Time, r ≤ r' → poolSet r ⊆ poolSet r')
    (hcover : ∀ s : Nat, ∀ tx ∈ poolSet (Q.slotLength * s), memTx tx (pool s))
    (H : SettingGA Q S x5) (hκ : 1 ≤ kappa)
    (hwin : MfcEquiv.HonestProposalWindow5 (kappa := kappa) x5)
    (hga : S.GlobalAwakeTime Q.gat Finset.univ)
    {t : Nat} (ht : 1 ≤ t)
    {vp : Node} {chp chC : Chain Tx} {qc : Option (QCert Node Tx)}
    {gjp : Checkpoint (Chain Tx)} {ip : Nat}
    (hsent : (⟨vp, Msg.propose chp chC qc gjp t⟩ :
      SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ x5[ip].sent)
    (hhon_i : vp ∉ S.adv ((x5[ip].time : Int)))
    (hhon_t : vp ∉ S.adv (Q.voting (t : Int)))
    (hlow : gjp.c < t - 1)
    (hgat : (Q.gat : Int) ≤ Q.voting (t : Int) - 3 * (Q.delta : Int))
    {vp' : Node} {chp' chC' : Chain Tx} {qc' : Option (QCert Node Tx)}
    {gjp' : Checkpoint (Chain Tx)} {ip' : Nat}
    (hsent' : (⟨vp', Msg.propose chp' chC' qc' gjp' (t + 1)⟩ :
      SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ x5[ip'].sent)
    (hhon_i' : vp' ∉ S.adv ((x5[ip'].time : Int)))
    (hhon_t' : vp' ∉ S.adv (Q.voting (((t + 1 : Nat)) : Int)))
    {vi : Node} {a : Nat} (hact3 : vi ∈ Active Q S (((t + 1 + 1 + 1 : Nat)) : Int))
    (hlate : Q.slotLength * (t + 1 + 1 + 1) + 2 * Q.delta ≤ x5[a].time)
    {r : Time} (hr : r ≤ Q.slotLength * t) :
    ∀ tx ∈ poolSet r, ∃ b ∈ x5[a][vi].st.chFin, memTx tx b.txs :=
  Finality5.chFin_txpool5 memTx poolSet hmonoP hcover H hκ hwin hga ht hsent hhon_i hsent'
    hhon_i' hhon_t'
    (Finality5.slotPinned_next5 H hκ hwin hga ht hsent hhon_i hhon_t
      (Finality5.slotPinned_of_low H hκ hwin hga ht hsent hhon_i hhon_t hlow hgat) hgat
      hsent' hhon_i' hhon_t')
    (Finality5.gat_le_voting_succ5 hgat) hact3 hlate hr

/-- **Theorem 6's liveness half, in the paper's Case 1**
    (`Theorem 6, arXiv:2601.03862v1 p.24`). The complementary regime to
    `theorem6_liveness_of_low`: the slot-`(t+1)` proposal carries a checkpoint of slot `t` —
    the paper's "`GJ^{propose(t+1)}_{p2} = C = (ch', t)`" — and then the slot-`t` proposal
    prefixes the finalized chain of every validator active in slot `t+3`.

    Nothing is assumed about slot `t`'s own carried checkpoint here, so between this and
    `theorem6_liveness_of_low` the only case of Theorem 6 left open is the paper's Case 2:
    `GJ^{propose(t)}_p.c = t − 1` *and* no slot-`t` justification at `propose(t+1)`. That
    case does not follow from Theorem 6's hypotheses at all — see the fourteenth
    authors'-note finding in `CONTEXT.md`; it needs an honest proposer at `t+2`. -/
theorem theorem6_liveness_case1 {x5 : Exec Pr5 S} (H : SettingGA Q S x5) (hκ : 1 ≤ kappa)
    (hwin : MfcEquiv.HonestProposalWindow5 (kappa := kappa) x5)
    (hga : S.GlobalAwakeTime Q.gat Finset.univ)
    {t : Nat} (ht : 1 ≤ t)
    {vp : Node} {chp chC : Chain Tx} {qc : Option (QCert Node Tx)}
    {gjp : Checkpoint (Chain Tx)} {ip : Nat}
    (hsent : (⟨vp, Msg.propose chp chC qc gjp t⟩ :
      SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ x5[ip].sent)
    (hhon_i : vp ∉ S.adv ((x5[ip].time : Int)))
    (hhon_t : vp ∉ S.adv (Q.voting (t : Int)))
    (hgat : (Q.gat : Int) ≤ Q.voting (t : Int) - 3 * (Q.delta : Int))
    {vp' : Node} {chp' chC' : Chain Tx} {qc' : Option (QCert Node Tx)}
    {gjp' : Checkpoint (Chain Tx)} {ip' : Nat}
    (hsent' : (⟨vp', Msg.propose chp' chC' qc' gjp' (t + 1)⟩ :
      SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ x5[ip'].sent)
    (hhon_i' : vp' ∉ S.adv ((x5[ip'].time : Int)))
    (hhon_t' : vp' ∉ S.adv (Q.voting (((t + 1 : Nat)) : Int)))
    (hgjc : gjp'.c = t)
    {vi : Node} {a : Nat} (hact3 : vi ∈ Active Q S (((t + 1 + 1 + 1 : Nat)) : Int))
    (hlate : Q.slotLength * (t + 1 + 1 + 1) + 2 * Q.delta ≤ x5[a].time) :
    chp ⪯ x5[a][vi].st.chFin :=
  Finality5.chp_le_chFin5 H hκ hwin hga hsent' hhon_i' hhon_t'
    (Finality5.slotPinned_case1_5 H hκ hwin hga ht hsent hhon_i hhon_t hgat hsent' hhon_i'
      hhon_t' hgjc)
    (Finality5.gat_le_voting_succ5 hgat) hact3 hlate

/-- **Theorem 6's transaction-pool clause, in Case 1** — the companion of
    `theorem6_liveness_txpool_of_low`. -/
theorem theorem6_liveness_txpool_case1 {x5 : Exec Pr5 S} {τ : Type}
    (memTx : τ → Tx → Prop) (poolSet : Time → Set τ)
    (hmonoP : ∀ r r' : Time, r ≤ r' → poolSet r ⊆ poolSet r')
    (hcover : ∀ s : Nat, ∀ tx ∈ poolSet (Q.slotLength * s), memTx tx (pool s))
    (H : SettingGA Q S x5) (hκ : 1 ≤ kappa)
    (hwin : MfcEquiv.HonestProposalWindow5 (kappa := kappa) x5)
    (hga : S.GlobalAwakeTime Q.gat Finset.univ)
    {t : Nat} (ht : 1 ≤ t)
    {vp : Node} {chp chC : Chain Tx} {qc : Option (QCert Node Tx)}
    {gjp : Checkpoint (Chain Tx)} {ip : Nat}
    (hsent : (⟨vp, Msg.propose chp chC qc gjp t⟩ :
      SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ x5[ip].sent)
    (hhon_i : vp ∉ S.adv ((x5[ip].time : Int)))
    (hhon_t : vp ∉ S.adv (Q.voting (t : Int)))
    (hgat : (Q.gat : Int) ≤ Q.voting (t : Int) - 3 * (Q.delta : Int))
    {vp' : Node} {chp' chC' : Chain Tx} {qc' : Option (QCert Node Tx)}
    {gjp' : Checkpoint (Chain Tx)} {ip' : Nat}
    (hsent' : (⟨vp', Msg.propose chp' chC' qc' gjp' (t + 1)⟩ :
      SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ x5[ip'].sent)
    (hhon_i' : vp' ∉ S.adv ((x5[ip'].time : Int)))
    (hhon_t' : vp' ∉ S.adv (Q.voting (((t + 1 : Nat)) : Int)))
    (hgjc : gjp'.c = t)
    {vi : Node} {a : Nat} (hact3 : vi ∈ Active Q S (((t + 1 + 1 + 1 : Nat)) : Int))
    (hlate : Q.slotLength * (t + 1 + 1 + 1) + 2 * Q.delta ≤ x5[a].time)
    {r : Time} (hr : r ≤ Q.slotLength * t) :
    ∀ tx ∈ poolSet r, ∃ b ∈ x5[a][vi].st.chFin, memTx tx b.txs :=
  Finality5.chFin_txpool5 memTx poolSet hmonoP hcover H hκ hwin hga ht hsent hhon_i hsent'
    hhon_i' hhon_t'
    (Finality5.slotPinned_case1_5 H hκ hwin hga ht hsent hhon_i hhon_t hgat hsent' hhon_i'
      hhon_t' hgjc)
    (Finality5.gat_le_voting_succ5 hgat) hact3 hlate hr

end Algorithm5Proved

end Majorum
