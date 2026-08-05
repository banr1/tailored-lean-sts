import Examples.StsMultisetLog.majorum.Analysis.Proofs.Analysis2
import Examples.StsMultisetLog.majorum.Analysis.Proofs.Finality
import Examples.StsMultisetLog.majorum.Analysis.Proofs.MfcEquiv

/-!
# The paper's lemmas

**Convention (2026-08-03): one theorem here per numbered lemma of
arXiv:2601.03862v1, and nothing else.** Supporting material lives in `Mfc.lean`
(view-local: filters, majorities, `MFC`), `Provenance.lean` (execution-level, Algorithm
5) and `Provenance2.lean` (execution-level, Algorithm 2); the paper's *theorems* are
stated in `Theorems.lean` as `Prop`s awaiting proof.

**Lemma 2** (`lemma2` below) is proved, for Algorithm 2 — the algorithm the lemma is
about (Appendix A). The paper states three conclusions: `MFC^{propose(t+1)}_i ⪰ ch`
(`Provenance2.le_mfc_at_propose2`), `MFC^{vote(t+1)}_i ⪰ ch`
(`Provenance2.le_mfc_at_vote2`), and "which implies that, in slot `t+1`, all validators
in `H_vote(t+1)` send vote messages for chains extending `ch`" — the operative clause,
the one Lemma 3's induction consumes, and the statement of `lemma2`: the lemma's
hypothesis `ActiveVotesExtend2`, reproduced one slot later.

**Lemma 3** (`lemma3` below) is proved: a fast confirmation in slot `t` makes every
later slot's actives vote extensions of the confirmed chain — base case from the frozen
fast-confirmation (no majority needed), inductive step `lemma2`.

**Lemma 4** (`lemma4` below) is proved: an honest proposer's chain is voted for by every
active of its own slot (the vote *is* `chp`) and extended by all later slots' actives —
the base case is where the proposer-identity check earns its keep and `Relay` sees its
first use; the step is `lemma2` again.

**Proof convention (2026-08-04)**: every proof here is a single call into
`Analysis2.lean`, where the identical statement is proved in full — this file is the
paper's lemma list, readable without stepping through proofs.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 400

namespace Majorum

open the framework's flat multiset-log flavour

variable {Node Tx : Type} [DecidableEq Node] [DecidableEq Tx] [Fintype Node]
  {Q : Params} {S : Schedule Node} {kappa : Nat} {pool : Nat → Tx} {proposer : Nat → Node}

/-- Algorithm 2, its quorum threshold instantiated with the structural validator count.
    The paper's "·" — the blank finality fields — is nondeterministic in the protocol
    itself: each tick fills it with any value. -/
local notation "Pr2" => protocol2 Q (Fintype.card Node) kappa pool proposer

/-- Algorithm 5, its quorum threshold instantiated with the structural validator count. -/
local notation "Pr5" =>
  protocol (components (Fintype.card Node) kappa pool proposer) Q

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
    ActiveVotesExtend2 x (t + 1) ch :=
  Analysis2.lemma2 H ht hvotes

/-- **Lemma 3** (`Lemma 3, arXiv:2601.03862v1 p.15`, for Algorithm 2). If a validator
    fast confirms a chain `ch` in slot `t` — its `fconf(t)` view holds a `2n/3` quorum
    for `ch`, so `fastconfirmsimple` returns `(ch, Q)` with `Q ≠ ∅` — then, for any slot
    `t' > t`, all validators in `H_vote(t')` send vote messages for chains extending
    `ch`.

    Stated without the paper's honesty of the confirmer: views are sound in this model
    (everything in any view is in the log), so the hypothesis is only *stronger* without
    it. Induction on `t'`: the base case is
    `Provenance2.activeVotesExtend_of_fastconfirm` — the quorum reaches every active's
    `merge(t)` view by synchrony, and the frozen chain rides through `processProposals2`
    (monotone) into the fork-choice's base — and the inductive step is `lemma2`. -/
theorem lemma3 {x : Exec Pr2 S} (H : SettingGA Q S x)
    {t : Nat} (ht : 1 ≤ t) {ch : Chain Tx}
    (hconf : ∃ (i : Nat) (w : Node) (cert : QCert Node Tx),
      x[i].time = Q.slotLength * t + 2 * Q.delta ∧
      fastConfirmSimple (Fintype.card Node) (x[i][w].view) t = (ch, some cert))
    {t' : Nat} (ht' : t < t') :
    ActiveVotesExtend2 x t' ch :=
  Analysis2.lemma3 H ht hconf ht'

/-- **Lemma 4** (`Lemma 4, arXiv:2601.03862v1 p.15`, for Algorithm 2). Let `t` be a slot
    with an honest proposer `vp`, and assume `vp` sends a
    `[propose, chp, chC, QC, ·, t]` message. Then, for any slot `t' ≥ t`, all validators
    in `H_vote(t')` send a vote message for a chain extending `chp`.

    Honesty is taken at the message's log index and at `voting(t)` — what the base case
    consumes; `vp = proposer t` is *derived* (provenance), not assumed. Induction: the
    base case is `Provenance2.activeVotesExtend_of_propose` — every slot-`t` active's
    fork-choice is bounded by `chp` (the frozen chain is the merge value or, by the
    proposer-identity check, `vp`'s own `chC`; a majority transfers into `vp`'s views by
    synchrony and `Relay`), so the proposal branch fires and the vote *is* `chp` — and
    the step is `lemma2`. -/
theorem lemma4 {x : Exec Pr2 S} (H : SettingGA Q S x) {t : Nat} (ht : 1 ≤ t)
    {vp : Node} {chp chC : Chain Tx} {qc : Option (QCert Node Tx)}
    {ck : Checkpoint (Chain Tx)} {i : Nat}
    (hsent : (⟨vp, Msg.propose chp chC qc ck t⟩ :
      SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ x[i].sent)
    (hhon_i : vp ∉ S.adv ((x[i].time : Int)))
    (hhon_t : vp ∉ S.adv (Q.voting (t : Int)))
    {t' : Nat} (ht' : t ≤ t') :
    ActiveVotesExtend2 x t' chp :=
  Analysis2.lemma4 H ht hsent hhon_i hhon_t ht'

/-- **Lemma 5** (`Lemma 5, arXiv:2601.03862v1 p.16`, for Algorithm 2). Let `ri` be any
    round and `rj ≥ ri` a propose or vote round. Then, for any validator `vi` honest in
    `ri` and any `vj ∈ H_rj`, `Ch^{ri}_i ⪯ MFC^{rj}_j`.

    Two hypotheses beyond `SettingGA`, and two strengthenings:

    * **`HonestProposalWindow`** is Lemma 1's conclusion, de-probabilized: every slot
      `t ≥ κ` has an honestly proposed slot `tp ≥ 1` in `[t−κ, t)`. The paper's proof
      invokes Lemma 1 ("with overwhelming probability") exactly here; this model takes
      the conclusion as a hypothesis wherever the paper says w.o.p. (See the definition
      for the `t = κ` boundary and the `1 ≤ tp` strengthening.)
    * **`1 ≤ κ`**: with `κ = 0` the κ-deep rule confirms the fork-choice tip itself and
      the paper's own window `[t−κ, t)` is empty — its proof, too, needs `κ ≥ 1`.
    * `vi`'s honesty is **not assumed**: every validator's state follows the handler
      (the adversary acts by injecting messages), so the bound holds for corrupt `vi`
      too. Nor is a round bound on `ri` beyond `ri ≤ rj` — `x[a].time ≤ rj` renders it.
    * The conclusion covers both of the paper's round shapes as a conjunction: the
      propose round needs only the time (any index at `propose(sj)`), the vote round
      `vj`'s tick, whose state the fork choice reads.

    The proof is `Provenance2.chi_le_mfc`, a strong induction on the index of the last
    `chi` write in place of the paper's minimality contradiction — Case 1 (κ-deep write:
    absorption through the window's proposal) and Case 2 (fast-confirm write: Lemma 3's
    propagation, quorum-direct at the very next slot) are its step cases. -/
theorem lemma5 {x : Exec Pr2 S} (H : SettingGA Q S x) (hκ : 1 ≤ kappa)
    (hwin : HonestProposalWindow x)
    {a : Nat} {vi : Node} {b : Nat} {vj : Node} {sj : Nat} (hsj : 1 ≤ sj)
    (hact : vj ∈ Active Q S (sj : Int)) :
    (x[b].time = Q.slotLength * sj → x[a].time ≤ Q.slotLength * sj →
      x[a][vi].st.chi ⪯ mfc (x[b][vj].view) (x[b][vj].view)
        (fastConfirmSimple (Fintype.card Node) (x[b][vj].view) (sj - 1)).1 sj) ∧
    (x.lbl b = .tick vj (Q.slotLength * sj + Q.delta) →
      x[a].time ≤ Q.slotLength * sj + Q.delta →
      x[a][vi].st.chi ⪯
        mfc (processProposals2 (Fintype.card Node) proposer (x[b][vj].view) sj
            (x[b][vj].st)).vFrozen (x[b][vj].view)
          (processProposals2 (Fintype.card Node) proposer (x[b][vj].view) sj
            (x[b][vj].st)).chFrozen sj) :=
  Analysis2.lemma5 H hκ hwin hsj hact

/-- **Lemma 6** (`Lemma 6, arXiv:2601.03862v1 p.16`, for Algorithm 2). For any slot `t`
    and validator `vi ∈ H_propose(t)`, `MFC^{propose(t)}_i.p < t` — the propose-round
    fork-choice output was proposed *before* the current slot.

    Two deliberate strengthenings/divergences from the paper's statement:

    * **Any awake validator**, not only `H_propose(t)`: activity implies awakeness and the
      proof needs no more, so the hypothesis is the weaker one.
    * **Stated for `1 ≤ t`.** The paper has `B_genesis.p < 0` (a sentinel), so its claim
      holds at `t = 0` too; here `proposedAt [] = 0`, which makes the `t = 0` instance
      read `0 < 0`. The content of the lemma — the fork choice never returns a chain from
      the current or a future slot — starts at slot 1 either way.

    The proof is `Provenance2.mfc_propose_ok`: the fork-choice output is genesis or a
    prefix of some slot-`t−1` honest vote's chain (its quorum case has an honest
    supporter by `f < n/3`; its majority case by Constraint (1)), and the honest-chain
    invariant `honest_vote_chain` bounds every such chain's `proposedAt` by `t−1`. -/
theorem lemma6 {x : Exec Pr2 S} (H : SettingGA Q S x) {t : Nat} (ht : 1 ≤ t)
    {a : Nat} {w : Node} (hta : x[a].time = Q.slotLength * t) (hAwa : x.Awake a w) :
    proposedAt (mfc (x[a][w].view) (x[a][w].view)
      (fastConfirmSimple (Fintype.card Node) (x[a][w].view) (t - 1)).1 t) < t :=
  Analysis2.lemma6 H ht hta hAwa

/-- **Lemma 7** (`Lemma 7, arXiv:2601.03862v1 p.17`, Liveness of fast confirmations, for
    Algorithm 2). Take a slot `t` in which `|H_vote(t)| ≥ 2n/3`. If in slot `t` an honest
    validator sends a propose message for chain `chp`, then any validator's fast-confirm
    tick of slot `t` leaves its confirmed chain `Ch` extending `chp`.

    Stated for *any* validator ticking at `fconf(t)`, not only `H_fconf(t)`: the tick's
    own enabling supplies awakeness, so the activity window adds nothing. -/
theorem lemma7 {x : Exec Pr2 S} (H : SettingGA Q S x) {t : Nat} (ht : 1 ≤ t)
    (hbig : 2 * Fintype.card Node ≤ 3 * (Active Q S (t : Int)).card)
    {vp : Node} {chp chC : Chain Tx} {qc : Option (QCert Node Tx)}
    {ck : Checkpoint (Chain Tx)} {i : Nat}
    (hsent : (⟨vp, Msg.propose chp chC qc ck t⟩ :
      SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ x[i].sent)
    (hhon_i : vp ∉ S.adv ((x[i].time : Int)))
    (hhon_t : vp ∉ S.adv (Q.voting (t : Int)))
    {vi : Node} {j : Nat}
    (hj : x.lbl j = .tick vi (Q.slotLength * t + 2 * Q.delta)) :
    chp ⪯ x[j + 1][vi].st.chi :=
  Analysis2.lemma7 H ht hbig hsent hhon_i hhon_t hj

/-! ### Appendix B: the finality component

Lemmas 8 and 9 are **assumption-free**: no schedule, no synchrony, no corruption bound —
the `f ∈ [0, n]` regime. They are view-local counting over the justification machinery,
with `n` the structural validator count as everywhere in this directory. -/

/-- **Lemma 8** (`Lemma 8, arXiv:2601.03862v1 p.17`). Assume `f ∈ [0, n]` and let
    `C_f = (ch_f, c_f)` be a finalized checkpoint and `C_j = (ch_j, c_j)` a justified
    checkpoint with `c_j ≥ c_f`, according to any two views. Either `ch_j ⪰ ch_f`, or at
    least `n/3` validators can be detected to have violated E1 or E2 — the detection
    evidence lies in the two views' union (`SlashableIn`).

    "`f ∈ [0, n]`" is rendered by assuming **nothing**: no hypothesis mentions the
    adversary at all. The paper's minimality contradiction becomes a strong induction
    on `c_j`, unwinding the justification chain one supermajority link at a time; the
    three evidence sites (double justification at one slot, the `c_j = c_f + 1` double
    vote, the surround) each close by quorum intersection — two `2n/3` link quorums
    over at most `n` validators share `n/3`, and every shared voter signed both
    fin-votes. Fin-vote *validity* (`C.c < C'.c ∧ C.ch ⪯ C'.ch`, part of `link`) is
    what the induction reads: the source chain sits below the target, and no link
    enters checkpoint slot `0`. -/
theorem lemma8 {V1 V2 : View Node (Msg (Chain Tx) (QCert Node Tx))}
    {chf chj : Chain Tx} {cf cj : Nat}
    (hfin : FinalizedIn (Fintype.card Node) V1 ⟨chf, cf⟩)
    (hjust : JustifiedIn (Fintype.card Node) V2 ⟨chj, cj⟩)
    (hcle : cf ≤ cj) :
    chf ⪯ chj ∨ ∃ W : Finset Node, Fintype.card Node ≤ 3 * W.card ∧
      ∀ w ∈ W, SlashableIn (V1 ∪ V2) w :=
  Finality.lemma8 (le_refl _) hfin hjust hcle

/-- **Lemma 9** (`Lemma 9, arXiv:2601.03862v1 p.17`). Assume `f ∈ [0, n]`. If two
    conflicting chains are finalized according to any two respective views, then at
    least `n/3` validators can be detected to have violated E1 or E2.

    The paper's "chain finalized according to `V`" is rendered as the hypothesis pair
    the paper's own proof extracts: a finalized checkpoint whose chain the finalized
    chain prefixes. Finalization implies justification, Lemma 8 nests the checkpoint
    chains, and two prefixes of one chain cannot conflict. -/
theorem lemma9 {V1 V2 : View Node (Msg (Chain Tx) (QCert Node Tx))}
    {ch1 ch2 ch1' ch2' : Chain Tx} {c1 c2 : Nat}
    (h1 : FinalizedIn (Fintype.card Node) V1 ⟨ch1', c1⟩) (h1le : ch1 ⪯ ch1')
    (h2 : FinalizedIn (Fintype.card Node) V2 ⟨ch2', c2⟩) (h2le : ch2 ⪯ ch2')
    (hc12 : ¬ (ch1 ⪯ ch2 : Bool)) (hc21 : ¬ (ch2 ⪯ ch1 : Bool)) :
    ∃ W : Finset Node, Fintype.card Node ≤ 3 * W.card ∧
      ∀ w ∈ W, SlashableIn (V1 ∪ V2) w :=
  Finality.lemma9 (le_refl _) h1 h1le h2 h2le hc12 hc21

/-- **Lemma 10** (`Lemma 10, arXiv:2601.03862v1 p.18`). For every compliant Algorithm-5
    run there is a compliant Algorithm-2 run that is *MFC-equivalent* to it
    (Definition 9): the two agree on ticks, on emissions up to dynamic equivalence
    (Definition 8), on both rounds' fork-choice outputs, and the Algorithm-5 available
    chains are dominated by the Algorithm-2 confirmed chains.

    The witness is `simulate x5` — the original's own schedule replayed against Algorithm
    2, with a table pairing each message with its counterpart. The paper argues the
    equivalence "by construction"; here the construction is a definition and the
    equivalence a mutual induction over the step index (`MfcEquiv.table_and_dominance`),
    since conditions 2.1/2.2 at a tick need the table invariant *and* the dominance
    invariant at earlier steps, and the dominance invariant's own step needs conditions
    2.1/2.2. -/
theorem lemma10 {x5 : Exec Pr5 S} (H : SettingGA Q S x5) (hκ : 1 ≤ kappa)
    (hwin : MfcEquiv.HonestProposalWindow5 (kappa := kappa) x5) :
    ∃ x2 : Exec Pr2 S, SettingGA Q S x2 ∧ MfcEquiv.MfcEquivalent x5 x2 :=
  ⟨simulate x5, MfcEquiv.lemma10 rfl H hκ hwin⟩

/-- **Lemma 11** (`Lemma 11, arXiv:2601.03862v1 p.20`, the analogue of Lemma 2, for
    Algorithm 5). If every slot-`t` active votes for a chain extending `ch`, then the fork
    choice extends `ch` at every slot-`t+1` active's propose and vote ticks, and every
    slot-`t+1` active votes for a chain extending `ch`.

    Proved through Lemma 10: the votes transfer to the equivalent Algorithm-2 run, Lemma
    2's engines run there, and the fork-choice bounds come back through conditions
    2.1/2.2. -/
theorem lemma11 {x5 : Exec Pr5 S} (H : SettingGA Q S x5) (hκ : 1 ≤ kappa)
    (hwin : MfcEquiv.HonestProposalWindow5 (kappa := kappa) x5)
    {t : Nat} (ht : 1 ≤ t) {ch : Chain Tx}
    (h : MfcEquiv.ActiveVotesExtend5 (kappa := kappa) (pool := pool) x5 t ch) :
    (∀ (k : Nat) (vi : Node), vi ∈ Active Q S ((t : Int) + 1) →
      x5.lbl k = .tick vi (Q.slotLength * (t + 1)) →
      ch ⪯ (components (Fintype.card Node) kappa pool proposer).mfc
        x5[k][vi].view x5[k][vi].view
        ((components (Fintype.card Node) kappa pool proposer).fastConfirm
          x5[k][vi].view t).1 (t + 1)) ∧
    (∀ (k : Nat) (vi : Node), vi ∈ Active Q S ((t : Int) + 1) →
      x5.lbl k = .tick vi (Q.slotLength * (t + 1) + Q.delta) →
      ch ⪯ (components (Fintype.card Node) kappa pool proposer).mfc
        (processProposals (components (Fintype.card Node) kappa pool proposer)
          x5[k][vi].view (t + 1) x5[k][vi].st).vFrozen
        x5[k][vi].view
        (processProposals (components (Fintype.card Node) kappa pool proposer)
          x5[k][vi].view (t + 1) x5[k][vi].st).chFrozen (t + 1)) ∧
    MfcEquiv.ActiveVotesExtend5 (kappa := kappa) (pool := pool) x5 (t + 1) ch :=
  let hpair := MfcEquiv.lemma10 rfl H hκ hwin
  MfcEquiv.lemma11 rfl hpair.2 H hpair.1 ht h

/-- **Lemma 12** (`Lemma 12, arXiv:2601.03862v1 p.20`, the analogue of Lemma 4, for
    Algorithm 5). An honest proposer's slot-`t` proposal is voted for by every active from
    slot `t` on, and both rounds' fork choices extend it from slot `t+1` on.

    Proved through Lemma 10: the proposal crosses to the equivalent run at its emitting
    tick (condition 1 preserves the proposed chain and slot), Lemma 4 runs there, and the
    votes and fork-choice bounds come back through the transfers. -/
theorem lemma12 {x5 : Exec Pr5 S} (H : SettingGA Q S x5) (hκ : 1 ≤ kappa)
    (hwin : MfcEquiv.HonestProposalWindow5 (kappa := kappa) x5)
    {t : Nat} (ht : 1 ≤ t)
    {vp : Node} {chp chC : Chain Tx} {qc : Option (QCert Node Tx)}
    {ck : Checkpoint (Chain Tx)} {i : Nat}
    (hsent : (⟨vp, Msg.propose chp chC qc ck t⟩ :
      SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ x5[i].sent)
    (hhon_i : vp ∉ S.adv ((x5[i].time : Int)))
    (hhon_t : vp ∉ S.adv (Q.voting (t : Int))) :
    (∀ t', t ≤ t' →
      MfcEquiv.ActiveVotesExtend5 (kappa := kappa) (pool := pool) x5 t' chp) ∧
    (∀ t₀, t ≤ t₀ →
      (∀ (k : Nat) (vi : Node), vi ∈ Active Q S ((t₀ : Int) + 1) →
        x5.lbl k = .tick vi (Q.slotLength * (t₀ + 1)) →
        chp ⪯ (components (Fintype.card Node) kappa pool proposer).mfc
          x5[k][vi].view x5[k][vi].view
          ((components (Fintype.card Node) kappa pool proposer).fastConfirm
            x5[k][vi].view t₀).1 (t₀ + 1)) ∧
      (∀ (k : Nat) (vi : Node), vi ∈ Active Q S ((t₀ : Int) + 1) →
        x5.lbl k = .tick vi (Q.slotLength * (t₀ + 1) + Q.delta) →
        chp ⪯ (components (Fintype.card Node) kappa pool proposer).mfc
          (processProposals (components (Fintype.card Node) kappa pool proposer)
            x5[k][vi].view (t₀ + 1) x5[k][vi].st).vFrozen
          x5[k][vi].view
          (processProposals (components (Fintype.card Node) kappa pool proposer)
            x5[k][vi].view (t₀ + 1) x5[k][vi].st).chFrozen (t₀ + 1))) :=
  let hpair := MfcEquiv.lemma10 rfl H hκ hwin
  MfcEquiv.lemma12 rfl hpair.2 H hpair.1 ht hsent hhon_i hhon_t

/-- **Lemma 13** (`Lemma 13, arXiv:2601.03862v1 p.20`, the analogue of Lemma 5, for
    Algorithm 5). Any validator's available chain at any round sits below every later
    fork-choice output, in both rounds of every slot whose actives include the tick's
    owner.

    Proved through Lemma 10: the available chain is dominated by a confirmed chain of the
    equivalent run (condition 2.3/2.4), Lemma 5 bounds that by the equivalent run's fork
    choice, and conditions 2.1/2.2 carry the bound back. -/
theorem lemma13 {x5 : Exec Pr5 S} (H : SettingGA Q S x5) (hκ : 1 ≤ kappa)
    (hwin : MfcEquiv.HonestProposalWindow5 (kappa := kappa) x5)
    (a : Nat) (vi : Node) (k : Nat) (vj : Node) (s0 : Nat)
    (hv : vj ∈ Active Q S ((s0 : Int) + 1)) :
    (x5.lbl k = .tick vj (Q.slotLength * (s0 + 1)) →
      x5[a].time ≤ Q.slotLength * (s0 + 1) →
      x5[a][vi].st.chAva ⪯
        (components (Fintype.card Node) kappa pool proposer).mfc
          x5[k][vj].view x5[k][vj].view
          ((components (Fintype.card Node) kappa pool proposer).fastConfirm
            x5[k][vj].view s0).1 (s0 + 1)) ∧
    (x5.lbl k = .tick vj (Q.slotLength * (s0 + 1) + Q.delta) →
      x5[a].time ≤ Q.slotLength * (s0 + 1) + Q.delta →
      x5[a][vi].st.chAva ⪯
        (components (Fintype.card Node) kappa pool proposer).mfc
          (processProposals (components (Fintype.card Node) kappa pool proposer)
            x5[k][vj].view (s0 + 1) x5[k][vj].st).vFrozen
          x5[k][vj].view
          (processProposals (components (Fintype.card Node) kappa pool proposer)
            x5[k][vj].view (s0 + 1) x5[k][vj].st).chFrozen (s0 + 1)) :=
  let hpair := MfcEquiv.lemma10 rfl H hκ hwin
  MfcEquiv.lemma13 rfl hpair.2 H hpair.1 hκ
    (MfcEquiv.window_transfer H hwin) a vi k vj s0 hv

end Majorum
