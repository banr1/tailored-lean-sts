import Examples.StsMultisetLog.majorum.Provenance2

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
  exact activeVotesExtend_of_le_mfc hsync hstepw hdiv hdil fun p hp j hj =>
    le_mfc_at_vote2 hsync hstepw hdil hwpt hone hmc hsyn hslp hcb hfn hgst ht hvotes hp hj

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
    ActiveVotesExtend2 x t' ch := by
  obtain ⟨iw, w, cert, htiw, hfc⟩ := hconf
  induction t', ht' using Nat.le_induction with
  | base =>
      obtain ⟨⟨hmc, -, hsync, -, -, hdiv, hdil⟩, hstepw, hwpt, hone, ⟨hsyn, -⟩, hslp,
        ⟨hcb, hfn⟩, hgst⟩ := H
      exact activeVotesExtend_of_fastconfirm hsync hstepw hdiv hdil hone hmc hsyn hcb hfn
        (le_refl _) htiw hfc
  | succ m hm ih => exact lemma2 H (by omega) ih

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
    ActiveVotesExtend2 x t' chp := by
  induction t', ht' using Nat.le_induction with
  | base =>
      obtain ⟨⟨hmc, -, hsync, -, -, hdiv, hdil⟩, hstepw, hwpt, hone, ⟨hsyn, hrel⟩, hslp,
        ⟨hcb, hfn⟩, hgst⟩ := H
      exact activeVotesExtend_of_propose hsync hstepw hdiv hdil hone hwpt hmc hsyn hrel
        hslp hcb hfn (le_refl _) hgst ht hsent hhon_i hhon_t
  | succ m hm ih => exact lemma2 H (by omega) ih

/-- **Lemma 5** (`Lemma 5, arXiv:2601.03862v1 p.16`, for Algorithm 2). Let `ri` be any
    round and `rj ≥ ri` a propose or vote round. Then, for any validator `vi` honest in
    `ri` and any `vj ∈ H_rj`, `Ch^{ri}_i ⪯ MFC^{rj}_j`.

    Two hypotheses beyond `SettingGA`, and two strengthenings:

    * **`HonestProposalWindow`** is Lemma 1's conclusion, de-probabilized: every slot
      `t > κ` has an honestly proposed slot in `[t−κ, t)`. The paper's proof invokes
      Lemma 1 ("with overwhelming probability") exactly here; this model takes the
      conclusion as a hypothesis wherever the paper says w.o.p.
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
      chainLe (x[a][vi].st.chi) (mfc (x[b][vj].view) (x[b][vj].view)
        (fastConfirmSimple (Fintype.card Node) (x[b][vj].view) (sj - 1)).1 sj)) ∧
    (x.lbl b = .tick vj (Q.slotLength * sj + Q.delta) →
      x[a].time ≤ Q.slotLength * sj + Q.delta →
      chainLe (x[a][vi].st.chi)
        (mfc (processProposals2 (Fintype.card Node) proposer (x[b][vj].view) sj
            (x[b][vj].st)).vFrozen (x[b][vj].view)
          (processProposals2 (Fintype.card Node) proposer (x[b][vj].view) sj
            (x[b][vj].st)).chFrozen sj)) := by
  obtain ⟨⟨hmc, -, hsync, -, -, hdiv, hdil⟩, hstepw, hwpt, hone, ⟨hsyn, hrel⟩, hslp,
    ⟨hcb, hfn⟩, hgst⟩ := H
  obtain ⟨s0, rfl⟩ : ∃ s0, sj = s0 + 1 := ⟨sj - 1, by omega⟩
  have hact' : vj ∈ Active Q S ((s0 : Int) + 1) := by
    have hcast : (((s0 + 1 : Nat)) : Int) = (s0 : Int) + 1 := by push_cast; omega
    rw [← hcast]
    exact hact
  simpa using chi_le_mfc hsync hstepw hdiv hdil hone hwpt hmc hsyn hrel hslp hcb hfn
    (le_refl _) hgst hκ hwin a vi b vj s0 hact'

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
      (fastConfirmSimple (Fintype.card Node) (x[a][w].view) (t - 1)).1 t) < t := by
  obtain ⟨⟨hmc, -, hsync, -, -, hdiv, hdil⟩, hstepw, hwpt, hone, ⟨hsyn, -⟩, hslp,
    ⟨hcb, hfn⟩, hgst⟩ := H
  obtain ⟨t0, rfl⟩ : ∃ t0, t = t0 + 1 := ⟨t - 1, by omega⟩
  have h := (mfc_propose_ok hsync hstepw hdiv hdil hone hwpt hmc hsyn hslp hcb hfn
    (le_refl _) hgst hta hAwa).2
  simpa using Nat.lt_succ_of_le h

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
    chainLe chp (x[j + 1][vi].st.chi) := by
  have hvotes := lemma4 H ht hsent hhon_i hhon_t (le_refl t)
  obtain ⟨⟨hmc, -, hsync, -, -, hdiv, hdil⟩, hstepw, hwpt, hone, ⟨hsyn, hrel⟩, hslp,
    ⟨hcb, hfn⟩, hgst⟩ := H
  exact le_chi_at_fconf hsync hstepw hone hmc hsyn hcb hfn (le_refl _) hvotes hbig hj

end Majorum
