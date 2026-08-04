import Examples.StsMultisetLog.majorum.Spec.Assumptions

/-!
# Majorum, Algorithm 5

The protocol itself, as a `the framework's flat multiset-log flavour.Protocol`. Source: arXiv:2601.03862v1,
Algorithm 5 (state and outputs in Algorithm 4), which is Algorithm 2 — the dynamically
available component — with the finality component of Section 4 integrated.

## What is specified and what is abstracted

Specified: the state, the four phase actions and the round at which each happens, the
message formats, and how every variable is updated. That is the content of Algorithm 5, and
it is what the paper writes out.

Abstracted, into `Components`: the fork-choice `MFC`, `Extend`, `fastconfirmsimple`, the
justification predicate `J` and the greatest justified and finalized checkpoints `GJ`, `GF`,
proposal validity, the `κ`-deep prefix, and the prefix order on chains. The paper treats
these as given when it presents Algorithm 5 — Section 4 and Algorithm 2 define them — and a
specification of Algorithm 5 that inlined them would be specifying those instead. Making
them a parameter also means the algorithm can be read against the pseudocode line by line.

`Chain`, `QC` and the proposer election are likewise parameters. `Chain` carries no
structure beyond what `Components` gives it, which keeps blocks and transactions out, as the
framework requires.

## How it maps onto the framework

* **Phases are clock-driven.** Algorithm 5's actions happen at rounds `4Δt`, `4Δt+Δ`,
  `4Δt+2Δ`, `4Δt+3Δ`, so `handler` dispatches on `r % 4Δ` and there are no protocol-specific
  events at all: `Ev := Empty`.
* **Delivery is not a reaction.** Lines 29–38 handle propose messages received in
  `[4Δt, 4Δt+Δ]`, but "validators delay processing such proposals until `vote(t)`" — so
  `recv` does nothing and the vote handler reads them out of the view, which the framework
  maintains. This is the one place the framework's design does real work for us.
* **Waking starts the joining protocol.** The wake handler computes the activation round
  from the paper's window — waking at `r ∈ (voting(t-2)+Δ, voting(t-1)+Δ]` means active at
  `voting(t)` — and stores it in `NodeState.activeAt`; the propose and vote branches send
  nothing while `r < activeAt`, still updating state ("executes the protocol, but without
  sending any message"). Computing it from the clock is sound because under
  `SynchronizedClocks` even a just-woken validator's clock reads real time. An earlier
  version had the wake *event* send nothing but let the very next tick vote, which
  falsified Lemma 2 — see `CONTEXT.md` (2026-08-03).
* **Noncomputable**, because reading the view in a fixed order needs `Finset.toList`. See
  `processProposals`: the order is a choice the paper does not make, and resolving it
  properly would make `step` relational and computable at once.
-/

set_option autoImplicit false

namespace Majorum

open the framework's flat multiset-log flavour

variable {Node Chain QC : Type}

/-- A checkpoint `(ch, c)`: a chain and the slot at which it is proposed for justification. -/
structure Checkpoint (Chain : Type) where
  /-- The chain. -/
  ch : Chain
  /-- The checkpoint slot. -/
  c : Nat
  deriving DecidableEq

/-- Majorum's messages, Algorithm 5 lines 9 and 20. The signer is the framework's, so
    neither carries `v_i`. -/
inductive Msg (Chain QC : Type) where
  /-- `[propose, chp, chC, QC, GJ_p, t]`. -/
  | propose (chp chC : Chain) (qc : Option QC) (gj : Checkpoint Chain) (t : Nat)
  /-- `[vote, ch, source → target, t]`. The fin-vote travels in the vote message. -/
  | vote (ch : Chain) (source target : Checkpoint Chain) (t : Nat)
  deriving DecidableEq

/-- The paper's `[vote, ch, src → tgt, t, vᵢ]`, as notation for the signed message —
    the last component is the signer, as in the paper, where it stands for the
    signature. Purely sugar: elaborates to `⟨p, Msg.vote e src tgt t⟩` and prints back
    the same way. -/
scoped notation "⟪vote, " e ", " src ", " tgt ", " t ", " p "⟫" =>
  the framework's flat multiset-log flavour.SignedMsg.mk p (Msg.vote e src tgt t)

/-- Everything a validator keeps: Algorithm 4's outputs and state.

    `V_i`, the view, is *not* here — the framework maintains it and hands it to `step`. -/
structure NodeState (Node Chain QC : Type) where
  /-- Available chain, Algorithm 2's confirmed chain `Ch_i`. -/
  chAva : Chain
  /-- Finalized chain. -/
  chFin : Chain
  /-- Snapshot of the view at `4Δt + 3Δ`. -/
  vFrozen : View Node (Msg Chain QC)
  /-- Snapshot of the fast-confirmed chain at `4Δt + 3Δ`. -/
  chFrozen : Chain
  /-- Latest frozen greatest justified checkpoint. -/
  gjFrozen : Checkpoint Chain
  /-- The first round from which this validator may send — `voting(t)` for the slot `t`
      its joining protocol targets (`activationRound`). `0` at initialization: validators
      awake from the start are active from the start, the genesis convention the paper
      leaves implicit. -/
  activeAt : Time

/-- The pieces Algorithm 5 calls, defined elsewhere in the paper. -/
structure Components (Node Chain QC : Type) where
  /-- `B_genesis`. -/
  genesis : Chain
  /-- The prefix order `⪯`, decidable so the algorithm can branch on it. -/
  prefixLe : Chain → Chain → Bool
  /-- `ch.p`, the slot a chain was proposed in. -/
  proposedAt : Chain → Nat
  /-- The `κ`-deep prefix `(·)⌈κ,t`, slot-indexed as on p. 4. -/
  kappaPrefix : Nat → Chain → Chain
  /-- The greatest common prefix, for `max {ch : ch ⪯ a ∧ ch ⪯ b}` at line 15. -/
  commonPrefix : Chain → Chain → Chain
  /-- `MFC(V₁, V₂, ch, t)`, the majority fork-choice (Algorithm 3). -/
  mfc : View Node (Msg Chain QC) → View Node (Msg Chain QC) → Chain → Nat → Chain
  /-- `Extend(ch, t)`: a chain of length `t` extending `ch` with the pool's transactions. -/
  extend : Chain → Nat → Chain
  /-- `fastconfirmsimple(V, t)` (Algorithm 2): the chain supported by more than `2n/3`
      voters in slot `t`, with its quorum certificate, or `(genesis, none)`. -/
  fastConfirmSimple : View Node (Msg Chain QC) → Nat → Chain × Option QC
  /-- `GJ(V)`, the greatest justified checkpoint. -/
  gj : View Node (Msg Chain QC) → Checkpoint Chain
  /-- `GF(V)`, the greatest finalized checkpoint. -/
  gf : View Node (Msg Chain QC) → Checkpoint Chain
  /-- `J(C, V)`, "checkpoint `C` is justified in view `V`". -/
  justified : Checkpoint Chain → View Node (Msg Chain QC) → Bool
  /-- `valid(·)` on a propose message. -/
  validProposal : SignedMsg Node (Msg Chain QC) → Bool
  /-- Which validator proposes in a slot. Idealized: the paper's VRF election is
      unpredictable and fair with overwhelming probability, which is out of reach here. -/
  proposer : Nat → Node

namespace Components

variable (C : Components Node Chain QC)

/-- The greater of two chains under `⪯`, used for the `max` at lines 14 and 15. -/
def maxCh (a b : Chain) : Chain := if C.prefixLe a b then b else a

/-- `fastconfirm(V, t)` (Algorithm 5 lines 1–4): `fastconfirmsimple`, unless the result does
    not extend `GJ(V).ch`, in which case that checkpoint's chain with no certificate. -/
def fastConfirm (V : View Node (Msg Chain QC)) (t : Nat) : Chain × Option QC :=
  let r := C.fastConfirmSimple V t
  if C.prefixLe (C.gj V).ch r.1 then r else ((C.gj V).ch, none)

end Components

variable [DecidableEq Node] [DecidableEq Chain] [DecidableEq QC]

/-- The round at which a validator waking at round `r` becomes active.

    "Joining Protocol" (§2): a validator waking at `r ∈ (voting(t-2)+Δ, voting(t-1)+Δ]`
    becomes active at `voting(t)`. Solving the window for `t` gives `t = ⌈(r+2Δ)/4Δ⌉`, so
    this is `voting` of that ceiling, computed in `Nat` (`⌈x/n⌉ = (x+n-1)/n`). -/
def activationRound (Q : Params) (r : Time) : Time :=
  Q.slotLength * ((r + 2 * Q.delta + (Q.slotLength - 1)) / Q.slotLength) + Q.delta

/-- Algorithm 5 lines 29–38: fold every propose message for slot `t` in the view into
    `gjFrozen` and `chFrozen`.

    The paper receives these during `[4Δt, 4Δt+Δ]` and processes them *at* `4Δt+Δ`, so this
    runs at the start of the vote phase over whatever the view holds.

    **Ordering is a choice the paper does not make.** It processes each message as an `upon`,
    so a view holding several valid proposals for the same slot leaves the outcome to the
    arrival order. Folding over `V.toList` picks one order; the alternative would be to make
    `step` genuinely nondeterministic here, which the framework supports and which would be
    more faithful. Only a slot with two valid proposals — an equivocating proposer — can tell
    the difference.

    `Finset.toList` is noncomputable in Mathlib, so this and everything downstream of it are
    too. Nothing here is `decide`d, unlike the framework's examples, so the cost is only that
    the model cannot be executed. Making the choice explicit — a relational `step` — would
    recover computability *and* be more faithful, and is the obvious next change if execution
    is ever wanted. -/
noncomputable def processProposals (C : Components Node Chain QC)
    (V : View Node (Msg Chain QC)) (t : Nat) (s : NodeState Node Chain QC) :
    NodeState Node Chain QC :=
  V.toList.foldl (fun acc sm =>
    match sm.msg with
    | .propose _ chC _ gjp t' =>
        if t' == t && C.validProposal sm && C.justified gjp V && acc.gjFrozen.c ≤ gjp.c then
          let acc := { acc with gjFrozen := gjp }
          let acc := if C.prefixLe gjp.ch acc.chFrozen then acc
                     else { acc with chFrozen := gjp.ch }
          if C.prefixLe acc.chFrozen chC then { acc with chFrozen := chC } else acc
        else acc
    | .vote .. => acc) s

/-- Algorithm 5's four phase actions, dispatched on the round within the slot. -/
noncomputable def handler (C : Components Node Chain QC) (Q : Params) (p : Node) (r : Time)
    (V : View Node (Msg Chain QC)) (s : NodeState Node Chain QC) :
    NodeStepResult (NodeState Node Chain QC) (Msg Chain QC) :=
  let slot : Nat := r / Q.slotLength
  let phase : Nat := r % Q.slotLength
  if phase = 0 then
    -- Propose, `4Δt`, lines 5–9 — only once active: "if v_i is elected leader for slot t
    -- but is inactive at proposal time, it does not propose in that slot".
    if p = C.proposer slot ∧ s.activeAt ≤ r then
      let cq := C.fastConfirm V (slot - 1)
      let chMFC := C.mfc V V cq.1 slot
      let chp := C.extend chMFC slot
      { state := s, send := {.propose chp cq.1 cq.2 (C.gj V) slot} }
    else { state := s, send := 0 }
  else if phase = Q.delta then
    -- Vote, `4Δt + Δ`, lines 10–20, after lines 29–38.
    let s' := processProposals C V slot s
    let chMFC := C.mfc s'.vFrozen V s'.chFrozen slot
    let chAva :=
      [s'.chAva, C.kappaPrefix slot chMFC, s'.gjFrozen.ch].foldl
        (fun acc ch => if C.prefixLe ch chMFC then C.maxCh acc ch else acc) s'.chAva
    let chFin := C.commonPrefix chAva (C.gf V).ch
    let target : Checkpoint Chain :=
      if s'.gjFrozen.c = slot - 1 then ⟨chAva, slot⟩ else ⟨s'.gjFrozen.ch, slot⟩
    let proposedNow : Option Chain :=
      V.toList.findSome? (fun sm => match sm.msg with
        | .propose chp _ _ _ t' =>
            if t' == slot && C.proposedAt chp == slot && C.prefixLe chMFC chp then some chp
            else none
        | .vote .. => none)
    let ch := proposedNow.getD chMFC
    -- the gate reads the *pre*-state's `activeAt`; `processProposals` never writes it,
    -- so the two agree, and the un-shadowed spelling is the one proofs can see through
    { state := { s' with chAva := chAva, chFin := chFin },
      -- a joining validator "executes the protocol, but without sending any message"
      send := if s.activeAt ≤ r then {.vote ch s'.gjFrozen target slot} else 0 }
  else if phase = 2 * Q.delta then
    -- Fast Confirm, `4Δt + 2Δ`, lines 21–24.
    let fastcand := (C.fastConfirm V slot).1
    let chAva := if C.prefixLe fastcand s.chAva then s.chAva else fastcand
    { state := { s with chAva := chAva, chFin := (C.gf V).ch }, send := 0 }
  else if phase = 3 * Q.delta then
    -- Merge, `4Δt + 3Δ`, lines 25–28.
    { state := { s with vFrozen := V, chFrozen := (C.fastConfirm V slot).1,
                        gjFrozen := C.gj V },
      send := 0 }
  else
    { state := s, send := 0 }

/-- Majorum as a framework protocol.

    Deterministic, so the relational `step` is the graph of `handler` — the idiom the
    framework's examples use, which keeps the model computable. `Ev := Empty`: every action
    is at a fixed round, so `tick` drives all of them and there is nothing for `custom` to
    carry. -/
noncomputable def protocol (C : Components Node Chain QC) (Q : Params) :
    Protocol Node (Msg Chain QC) (NodeState Node Chain QC) Empty where
  init _ := { chAva := C.genesis, chFin := C.genesis, vFrozen := ∅,
              chFrozen := C.genesis, gjFrozen := ⟨C.genesis, 0⟩, activeAt := 0 }
  step p r V s e res := res = match e with
    | .tick => handler C Q p r V s
    | .recv _ => { state := s, send := 0 }   -- filed into the view; processed at `vote(t)`
    | .wake => -- the joining protocol starts: silent until the activation round
        { state := { s with activeAt := activationRound Q r }, send := 0 }
    | .custom ev => ev.elim
  total _ _ _ _ _ := ⟨_, rfl⟩
  enabled _ _ ev := ev.elim

end Majorum
