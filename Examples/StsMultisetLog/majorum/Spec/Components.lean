import Examples.StsMultisetLog.majorum.Spec.Algorithm5

/-!
# The functions Algorithm 5 relies on

`Algorithm5.lean` takes them as a `Components` record; here they are defined. Sources in
arXiv:2601.03862v1: chains and the fork-choice in §2 and Algorithm 1 (`MFC`),
fast confirmation in Algorithm 2, and justification, finalization, `GJ` and `GF` in §4.

## The chain model

A chain is a list of blocks, oldest first, each block carrying the slot it was proposed in.
`B_genesis` is the empty list and `⪯` is list prefix. The paper says only that chains are
ordered by `⪯`, have a genesis, and that `ch.p` is the slot a chain was proposed in, so this
is the smallest structure that supports what Algorithm 5 does with them.

## Four places this is a model rather than a transcription

* **Candidate chains are the prefixes of voted chains.** `MFC` returns "the longest chain
  `ch ⪰ chC` such that …", quantifying over all chains — an infinite set. A chain can pass
  the majority test only if some vote's chain extends it, making it a prefix of a chain
  the view carries; so the prefix closure of the voted chains, plus the base, is a
  complete finite search space. See `candidates` for why anything smaller is not.
* **Support is counted in validators, not messages** — see `Majority`.
* **Justification is an inductive `Prop`, not a `Bool`.** "Reachable from `(B_genesis, 0)` by
  a chain of supermajority links" is a least fixed point, so it is an `inductive`. Deciding
  it is done classically, which is why everything here is `noncomputable` — as
  `Algorithm5.lean` already was.
* **Ties are broken by list order.** `GJ` and `GF` take the justified or finalized checkpoint
  of largest slot, and the paper says "ties break arbitrarily". Folding over `Finset.toList`
  is one arbitrary choice; two checkpoints of the same slot with different chains means a
  safety violation is already under way, which is the situation Theorem 5 is about.
-/

set_option autoImplicit false

namespace Majorum

open the framework's flat multiset-log flavour Classical

variable {Node Tx QC : Type}

/-! ### Chains and certificates -/

/-- A block: the slot it was proposed in, and its payload. -/
structure Block (Tx : Type) where
  /-- The slot this block was proposed in. -/
  slot : Nat
  /-- Its transactions. -/
  txs : Tx
  deriving DecidableEq

/-- A chain, oldest block first. `B_genesis` is `[]`. -/
abbrev Chain (Tx : Type) := List (Block Tx)

/-- A quorum certificate: who voted, for which chain, in which slot.

    The paper says a `QC` "consist[s] of the corresponding vote messages", which is
    circular — a vote message carries a `QC`. Recording the content of those votes instead
    breaks the recursion and keeps everything a certificate is used for: checking that
    enough distinct validators supported a chain in a slot. -/
abbrev QCert (Node Tx : Type) := Finset (Node × Chain Tx × Nat)

variable [DecidableEq Tx]

/-- `ch ⪯ ch'`, chain prefix. -/
def chainLe (a b : Chain Tx) : Bool := a.isPrefixOf b

@[inherit_doc] scoped infix:50 " ⪯ " => chainLe

/-- `ch ≺ ch'`, strict prefix — a prefix of a longer chain. On prefixes,
    `¬ (b ⪯ a)` is exactly `a ≠ b`, spelled without `DecidableEq`. -/
def chainLt (a b : Chain Tx) : Bool := chainLe a b && !chainLe b a

@[inherit_doc] scoped infix:50 " ≺ " => chainLt

/-- `ch.p`, the slot the chain was proposed in — the slot of its last block, and `0` for
    genesis. -/
def proposedAt (ch : Chain Tx) : Nat := (ch.getLast?).elim 0 Block.slot

/-- Structural chain validity: block slots strictly increase along the chain. The
    paper's chain model has this built in (chains grow one block per slot, so `⪯`,
    lengths and `ch.p` all track slots); with chains as free block lists it must be
    *checked* where the protocol accepts a foreign chain — the vote phase's proposal
    check — or Lemma 5's `κ`-deep arithmetic and Lemma 6 are false (a corrupt proposer
    could smuggle a slot-garbled chain into honest votes). Decision of 2026-08-04,
    fourth authors'-note finding: proposal validity is undefined in the paper and needs
    both the proposer identity and this structural check. -/
def slotsIncreasing : Chain Tx → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => a.slot < b.slot && slotsIncreasing (b :: rest)

/-- The `κ`-deep prefix `(ch)⌈κ,t` (`arXiv:2601.03862v1 p.4`): the longest prefix whose
    blocks sit at least `κ` slots before `t` — on the slot-sorted chains the fork choice
    produces, a `takeWhile`. The test is spelled `b.slot + κ ≤ t` so that `Nat`
    subtraction cannot truncate: for `t < κ` nothing qualifies, matching the paper's
    `p ≤ t − κ < 0`.

    Slot-indexed, not count-based (2026-08-04, replacing `ch.take (ch.length − κ)`):
    the two are equally strong for Lemma 5's absorption, but not for Theorem 2's
    liveness — an honest proposal from `κ` slots back survives *this* prefix no matter
    how few blocks sit above it, which is exactly the paper's `chp ⪯ (MFC)⌈κ,ti` step;
    the count-based prefix would need a chain-growth argument the paper never makes. -/
def kappaPrefix (kappa t : Nat) (ch : Chain Tx) : Chain Tx :=
  ch.takeWhile (fun b => b.slot + kappa ≤ t)

/-- The greatest common prefix, which is `max {ch : ch ⪯ a ∧ ch ⪯ b}` for a prefix order. -/
def commonPrefix : Chain Tx → Chain Tx → Chain Tx
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys => if x = y then x :: commonPrefix xs ys else []

/-- `Extend(ch, t)`: extend `ch` with a block for slot `t` carrying the pool's transactions.

    The paper says "produces a chain of length `t` that extends `ch`", measuring length in
    slots; what the protocol then checks of the result is `chp.p = t`, which appending one
    block gives. A model in which chains have a block per slot would need the intermediate
    slots filled with something, and the paper does not say with what.

    `pool t` is the block body an honest slot-`t` proposer packs. The paper's `Extend`
    contract — the "Property 1" its Theorem 2 cites but never states (sixth finding,
    `CONTEXT.md` 2026-08-04) — says that body is all of `txpool^{propose(t)}`; since the
    paper's `txpool` is global and read-uniform, the honest body is a function of the
    slot alone, which is exactly this signature (instantiate `Tx` at a transaction-set
    type). The paper leaves `Extend` unspecified for `ch.p ≥ t`; here `Lemma 6` supplies
    `ch.p < t` wherever the protocol calls it, and `slotsIncreasing_extend` consumes
    precisely that bound. -/
def extend (pool : Nat → Tx) (ch : Chain Tx) (t : Nat) : Chain Tx :=
  ch ++ [⟨t, pool t⟩]

/-! ### Reading votes out of a view -/

/-- The vote messages in a view. -/
noncomputable def votes (V : View Node (Msg (Chain Tx) QC)) :
    Finset (SignedMsg Node (Msg (Chain Tx) QC)) :=
  V.filter (fun sm => match sm.msg with | .vote .. => True | .propose .. => False)

/-- The slot a vote was cast in, and `0` for anything else. -/
def msgSlot (m : Msg (Chain Tx) QC) : Nat :=
  match m with | .vote _ _ _ t => t | .propose _ _ _ _ t => t

/-- The chain a vote is for, and genesis for anything else. -/
def msgChain (m : Msg (Chain Tx) QC) : Chain Tx :=
  match m with | .vote ch _ _ _ => ch | .propose _ _ _ _ _ => []

variable [DecidableEq Node] [DecidableEq QC]

/-- `FIL_eq`: drop every validator that equivocated — sent two votes in the same slot for
    different chains. -/
noncomputable def filEq (V : View Node (Msg (Chain Tx) QC)) :
    Finset (SignedMsg Node (Msg (Chain Tx) QC)) :=
  (votes V).filter (fun sm => ¬ ∃ sm' ∈ votes V,
    sm'.sender = sm.sender ∧ msgSlot sm'.msg = msgSlot sm.msg ∧
      msgChain sm'.msg ≠ msgChain sm.msg)

/-- `FIL_1-exp`: keep exactly the previous slot's votes.

    Deliberately stricter than the paper's letter ("discards … votes older than one slot",
    which also keeps current-slot votes): under the paper's lock-step rounds the two
    readings coincide at every `MFC` call site — a slot-`t` vote cannot be *seen* at
    `vote(t)` or earlier — but under this model's free adversarial scheduling the looser
    reading lets same-slot votes into `S(V, t)`'s count and breaks Lemma 2 (a mass wake-up
    of validators active in slot `t` but not `t−1` inflates the majority test's
    denominator with votes its numerator can never contain, since `V_frozen` predates
    them). Equality makes the voter counting structural instead of timing-based.
    Decision of 2026-08-03, replacing a proposed `DeliveryLags` network assumption. -/
def fil1Exp (V : Finset (SignedMsg Node (Msg (Chain Tx) QC))) (t : Nat) :
    Finset (SignedMsg Node (Msg (Chain Tx) QC)) :=
  V.filter (fun sm => t = msgSlot sm.msg + 1)

/-- `FIL_lmd`: keep only each validator's latest vote. -/
noncomputable def filLmd (V : Finset (SignedMsg Node (Msg (Chain Tx) QC))) :
    Finset (SignedMsg Node (Msg (Chain Tx) QC)) :=
  V.filter (fun sm => ¬ ∃ sm' ∈ V,
    sm'.sender = sm.sender ∧ msgSlot sm.msg < msgSlot sm'.msg)

/-- `V^{ch,t}`: the latest, non-expired, non-equivocating votes for chains extending `ch`. -/
noncomputable def votesFor (V : View Node (Msg (Chain Tx) QC)) (ch : Chain Tx) (t : Nat) :
    Finset (SignedMsg Node (Msg (Chain Tx) QC)) :=
  (filLmd (fil1Exp (filEq V) t)).filter (fun sm => ch ⪯ msgChain sm.msg)

/-- `S(V, t)`: the validators with non-expired votes in `V` at slot `t`. -/
noncomputable def voters (V : View Node (Msg (Chain Tx) QC)) (t : Nat) : Finset Node :=
  (fil1Exp (votes V) t).image SignedMsg.sender

/-- The chains `MFC`'s "longest chain such that …" ranges over: the base, plus every
    prefix of every voted chain.

    The paper quantifies over all chains, but a chain passes the majority test only if some
    vote's chain *extends* it — support flows down from extensions — and a chain that some
    vote extends is a prefix of that vote's chain, hence reconstructible from the view. So
    this set is complete, and minimal among complete ones: chains the view mentions only in
    proposals or checkpoints can never pass, having no supporters.

    An earlier version kept only the voted chains themselves, missing the common prefix —
    which is exactly what wins when honest support splits across siblings, and what made
    Lemma 2 false for the model; see `CONTEXT.md` (2026-08-03). -/
noncomputable def candidates (V : View Node (Msg (Chain Tx) QC)) (chC : Chain Tx) :
    Finset (Chain Tx) :=
  insert chC ((votes V).biUnion fun sm => (msgChain sm.msg).inits.toFinset)

/-- The strict-majority test of Algorithm 1: more than half of `S(V', t)` supports `ch`,
    counting **validators, not messages**. Algorithm 2's `fastcands` writes the sender
    counting out explicitly, and message counting is wrong here: two votes differing only
    in their fin-vote parts share sender, chain and slot, survive every filter, and would
    let one sender manufacture a majority.

    An `abbrev`, so `Decidable` sees through it — a plain `def` fails every decidability
    search at the use sites (`CONTEXT.md`, 2026-08-03). -/
abbrev Majority (V V' : View Node (Msg (Chain Tx) QC)) (t : Nat) (ch : Chain Tx) : Prop :=
  (voters V' t).card <
    2 * (((votesFor V ch t) ∩ (votesFor V' ch t)).image SignedMsg.sender).card

/-- **`MFC(V, V', chC, t)`** (Algorithm 1): the longest `ch ⪰ chC` supported by a strict
    majority of `S(V', t)`, or `chC` if there is none. -/
noncomputable def mfc (V V' : View Node (Msg (Chain Tx) QC)) (chC : Chain Tx) (t : Nat) :
    Chain Tx :=
  (candidates V chC).toList.foldl
    (fun best ch =>
      if chC ⪯ ch ∧ Majority V V' t ch ∧ best.length < ch.length then ch else best)
    chC

/-- **`fastconfirmsimple(V, t)`** (Algorithm 2): the greatest chain supported by more than
    `2n/3` of the validators voting in slot `t`, with the votes that support it. -/
noncomputable def fastConfirmSimple (n : Nat) (V : View Node (Msg (Chain Tx) QC)) (t : Nat) :
    Chain Tx × Option (QCert Node Tx) :=
  let support : Chain Tx → Finset (SignedMsg Node (Msg (Chain Tx) QC)) := fun ch =>
    (votes V).filter (fun sm => msgSlot sm.msg = t ∧ ch ⪯ msgChain sm.msg)
  let cands := (candidates V []).filter
    (fun ch => 2 * n ≤ 3 * ((support ch).image SignedMsg.sender).card)
  let best := cands.toList.foldl (fun best ch => if best.length < ch.length then ch else best) []
  if best.isEmpty ∧ ¬ ([] ∈ cands) then ([], none)
  else (best, some ((support best).image (fun sm => (sm.sender, msgChain sm.msg, msgSlot sm.msg))))

/-! ### Justification and finalization (§4) -/

/-- The validators fin-voting `C → C'` in `V`. Fin-votes ride in vote messages, so this
    reads them out of the view; senders are counted, not messages. -/
noncomputable def linkVoters (V : View Node (Msg (Chain Tx) QC))
    (C C' : Checkpoint (Chain Tx)) : Finset Node :=
  ((votes V).filter (fun sm => match sm.msg with
    | .vote _ src tgt _ => src = C ∧ tgt = C'
    | .propose .. => False)).image SignedMsg.sender

/-- A **supermajority link** `C → C'`: a *valid* fin-vote step — the paper's fin-vote
    validity, `C.c < C'.c ∧ C.ch ⪯ C'.ch` (p. 9) — cast by at least `2n/3` validators.

    Appendix B's proofs rest on the validity conjuncts (2026-08-04): an earlier
    rendering omitted them, and justification then admits links *into* checkpoint slot
    `0` and chain-incoherent links, making Lemma 8 false — its proof reads the source
    chain's prefix bound (`Ai ⪯ ch'ⱼ`) and the counter ordering from validity. -/
noncomputable def link (n : Nat) (V : View Node (Msg (Chain Tx) QC))
    (C C' : Checkpoint (Chain Tx)) : Prop :=
  C.c < C'.c ∧ C.ch ⪯ C'.ch ∧ 2 * n ≤ 3 * (linkVoters V C C').card

/-- **E1 (double voting)**: two *distinct* fin-votes `C1 → C2` and `C3 → C4` with the
    same target checkpoint slot — "a validator must not send distinct fin-votes for the
    same checkpoint slot". -/
def E1 (C1 C2 C3 C4 : Checkpoint (Chain Tx)) : Prop :=
  (C1, C2) ≠ (C3, C4) ∧ C2.c = C4.c

/-- **E2 (surround voting)**: the first fin-vote is surrounded by the second,
    `C3.c < C1.c < C2.c < C4.c`. -/
def E2 (C1 C2 C3 C4 : Checkpoint (Chain Tx)) : Prop :=
  C3.c < C1.c ∧ C1.c < C2.c ∧ C2.c < C4.c

/-- A validator is **slashable on evidence `V`**: `V` holds two of its fin-votes that
    together violate E1 or E2. Fin-vote *validity* is deliberately not required —
    misbehaviour is evidence regardless of whether the votes could ever justify. -/
def SlashableIn (V : View Node (Msg (Chain Tx) QC)) (w : Node) : Prop :=
  ∃ sm1 ∈ V, ∃ sm2 ∈ V, sm1.sender = w ∧ sm2.sender = w ∧
    ∃ (e1 e2 : Chain Tx) (C1 C2 C3 C4 : Checkpoint (Chain Tx)) (t1 t2 : Nat),
      sm1.msg = .vote e1 C1 C2 t1 ∧ sm2.msg = .vote e2 C3 C4 t2 ∧
      (E1 C1 C2 C3 C4 ∨ E2 C1 C2 C3 C4)

/-- **Justified**: genesis, or reachable from it by supermajority links. A least fixed
    point, hence an inductive rather than a `Bool`. -/
inductive JustifiedIn (n : Nat) (V : View Node (Msg (Chain Tx) QC)) :
    Checkpoint (Chain Tx) → Prop
  /-- `(B_genesis, 0)` is justified. -/
  | genesis : JustifiedIn n V ⟨[], 0⟩
  /-- A supermajority link from a justified checkpoint justifies its target. -/
  | link {C C' : Checkpoint (Chain Tx)} :
      JustifiedIn n V C → link n V C C' → JustifiedIn n V C'

/-- **Finalized**: justified, with a supermajority link to the next checkpoint slot. -/
def FinalizedIn (n : Nat) (V : View Node (Msg (Chain Tx) QC))
    (C : Checkpoint (Chain Tx)) : Prop :=
  JustifiedIn n V C ∧ ∃ C', C'.c = C.c + 1 ∧ link n V C C'

/-- The checkpoints a view mentions, plus genesis — the search space for `GJ` and `GF`. -/
noncomputable def checkpoints (V : View Node (Msg (Chain Tx) QC)) :
    Finset (Checkpoint (Chain Tx)) :=
  insert ⟨[], 0⟩ ((votes V).biUnion (fun sm => match sm.msg with
    | .vote _ src tgt _ => {src, tgt}
    | .propose .. => ∅))

/-- The one of largest slot, ties broken by list order — the paper's "ties break
    arbitrarily". -/
noncomputable def greatestBySlot (S : Finset (Checkpoint (Chain Tx))) :
    Checkpoint (Chain Tx) :=
  S.toList.foldl (fun best C => if best.c ≤ C.c then C else best) ⟨[], 0⟩

/-- **`GJ(V)`**, the greatest justified checkpoint. -/
noncomputable def gj (n : Nat) (V : View Node (Msg (Chain Tx) QC)) : Checkpoint (Chain Tx) :=
  greatestBySlot ((checkpoints V).filter (fun C => JustifiedIn n V C))

/-- **`GF(V)`**, the greatest finalized checkpoint. -/
noncomputable def gf (n : Nat) (V : View Node (Msg (Chain Tx) QC)) : Checkpoint (Chain Tx) :=
  greatestBySlot ((checkpoints V).filter (fun C => FinalizedIn n V C))

/-! ### Validity -/

/-- Proposal validity, certificate included: the proposed chain belongs to the proposal's
    slot and extends the carried fast-confirmed chain, and the certificate's votes — held
    in the receiver's own view — give `chC` at least `2n/3` distinct supporters from the
    previous slot. A certified vote counts **with any filler** in its blank fields,
    matching the sender side's nondeterministic choice. See the module docstring for why
    the check runs against the view.

    **The proposal must be signed by its slot's proposer** (`sm.sender = proposer t'`).
    The paper's `valid([propose, …])` is never defined; Lemma 4 is false without this
    conjunct (a corrupt validator could have a certificate-backed `chC` processed, or —
    at line 23 — its fabricated slot-`t` chain voted for), and the paper's own base-case
    equalities need it. Structural signing makes it enforceable: nobody can forge the
    proposer's sender field. Decision of 2026-08-04; third authors'-note finding. -/
def ValidProposal2 (n : Nat) (proposer : Nat → Node)
    (V : View Node (Msg (Chain Tx) (QCert Node Tx)))
    (sm : SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) : Prop :=
  match sm.msg with
  | .propose chp chC qc _ t' =>
      sm.sender = proposer t' ∧ proposedAt chp = t' ∧ chC ⪯ chp ∧
        (chC = [] ∨ ∃ cert : QCert Node Tx, qc = some cert ∧
          2 * n ≤ 3 * (cert.image Prod.fst).card ∧
          ∀ e ∈ cert, chC ⪯ e.2.1 ∧ e.2.2 = t' - 1 ∧
            ∃ src tgt : Checkpoint (Chain Tx),
              (⟨e.1, Msg.vote e.2.1 src tgt e.2.2⟩ :
                SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ V)
  | .vote .. => False

/-- **Algorithm 5's proposal validity**: `ValidProposal2`'s checks with the certificate
    clause widened by one rung — `fastconfirm`'s GJ-branch substitutes the greatest
    justified checkpoint's chain with **no** certificate, so an uncertified `chC` is
    valid when it is the carried checkpoint's chain and that checkpoint is justified in
    the receiver's own view: *justification certifies*. The rungs are evidence
    proportional to the claim — genesis claims nothing, a fast-confirmed chain shows
    its quorum, a justified chain shows its justification.

    Deliberately **not** shared with Algorithm 2 (ninth authors'-note finding,
    `CONTEXT.md` 2026-08-05): there the checkpoint field is the nondeterministic
    blank and justification over Algorithm-2 views is adversary-steerable — honest
    fin-vote fields are unconstrained — so the widened clause would revive the
    chain-smuggling attack the certificate check exists to stop. The paper defines
    neither predicate; its Algorithm-5 validity sentence covers only the `GJ_p` field,
    leaving the `chC` clause it inherits from Algorithm 2 unsatisfiable on the
    GJ-branch — Algorithm 5 would reject its own honest proposals in every slot
    without a fast-confirm quorum. -/
def ValidProposal5 (n : Nat) (proposer : Nat → Node)
    (V : View Node (Msg (Chain Tx) (QCert Node Tx)))
    (sm : SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) : Prop :=
  match sm.msg with
  | .propose chp chC qc gjp t' =>
      sm.sender = proposer t' ∧ proposedAt chp = t' ∧ chC ⪯ chp ∧
        (chC = [] ∨
          (∃ cert : QCert Node Tx, qc = some cert ∧
            2 * n ≤ 3 * (cert.image Prod.fst).card ∧
            ∀ e ∈ cert, chC ⪯ e.2.1 ∧ e.2.2 = t' - 1 ∧
              ∃ src tgt : Checkpoint (Chain Tx),
                (⟨e.1, Msg.vote e.2.1 src tgt e.2.2⟩ :
                  SignedMsg Node (Msg (Chain Tx) (QCert Node Tx))) ∈ V) ∨
          (qc = none ∧ chC = gjp.ch ∧ JustifiedIn n V gjp))
  | .vote .. => False

/-! ### Assembling them -/

/-- All of Algorithm 5's components, defined. `n` is the validator count, `κ` the
    confirmation depth, `pool` the transaction pool, and `proposer` the idealized election.

    Deciding `JustifiedIn` and `FinalizedIn` is classical, so this is noncomputable — as
    `Algorithm5.lean` already was for an unrelated reason. -/
noncomputable def components (n kappa : Nat) (pool : Nat → Tx) (proposer : Nat → Node) :
    Components Node (Chain Tx) (QCert Node Tx) where
  genesis := []
  prefixLe := chainLe
  proposedAt := proposedAt
  kappaPrefix := kappaPrefix kappa
  commonPrefix := commonPrefix
  mfc := mfc
  extend := extend pool
  fastConfirmSimple := fastConfirmSimple n
  gj := gj n
  gf := gf n
  justified := fun C V => decide (JustifiedIn n V C)
  validProposal := ValidProposal5 n proposer
  sortedChain := slotsIncreasing
  proposer := proposer

/-- Majorum, Algorithm 5, with everything it calls defined. Named for the algorithm
    rather than the protocol, since the namespace is already `majorum`. -/
noncomputable def algorithm5 (Q : Params) (n kappa : Nat) (pool : Nat → Tx)
    (proposer : Nat → Node) :
    Protocol Node (Msg (Chain Tx) (QCert Node Tx))
      (NodeState Node (Chain Tx) (QCert Node Tx)) Empty :=
  protocol (components n kappa pool proposer) Q

end Majorum
