import Examples.StsMultisetLog.majorum.Security

/-!
# Majorum's theorems, as statements

All seven `\begin{theorem}` environments of the paper's own source, rendered in the
vocabulary of `Security.lean`. **Statements only** — nothing here is proved, and nothing
here is a `theorem`.

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
within it. Those are `the framework's flat multiset-log flavour.Models.Majorum.Params` fields; here they are plain
parameters so this file does not depend on that bundle.
-/

set_option autoImplicit false

namespace Majorum

open the framework's flat multiset-log flavour

variable {Node Msg NodeState Ev Out Tx : Type} [DecidableEq Node] [DecidableEq Msg]
  {Pr : Protocol Node Msg NodeState Ev} {S : Schedule Node}

/-! ### The dynamically available component — Algorithm `prob-ga-fast` (§ GA-based) -/

/-- **Theorem `thm:reorg-res-prop-tob`** (Reorg Resilience). "Algorithm `prob-ga-fast` is
    reorg-resilient." Unqualified, so after slot 0 and time 0. -/
def ThmReorgResilienceGA (out : Node → Config Node Msg NodeState → Out)
    (Pre : Out → Out → Prop) (proposedBy : Time → Out → Prop) (proposing : Time → Time)
    (honestAt : Time → Prop) (x : Exec Pr S) : Prop :=
  ReorgResilient out Pre proposedBy proposing honestAt 0 0 x

/-- **Theorem `thm:dyn-avail-fast-conf-tob`.** "Algorithm `prob-ga-fast` is
    dynamically-available `\wop`."

    The `\wop` is dropped — see the module docstring. Dynamic availability unqualified is
    "always secure when `GST = 0`", so `tdyn = 0` and the synchronous network is the
    caller's obligation. -/
def ThmDynamicAvailabilityGA (out : Node → Config Node Msg NodeState → Out)
    (Pre : Out → Out → Prop) (mem : Tx → Out → Prop) (pool : Time → Set Tx) (tconf : Time)
    (x : Exec Pr S) : Prop :=
  DynamicallyAvailable out Pre mem pool 0 tconf x

/-! ### The full protocol — Algorithm `3sf-tob-noga` (§ FFG) -/

/-- **Theorem `thm:reorg-res-prop-tob-ffg`** (Reorg Resilience, analogous of
    `thm:reorg-res-prop-tob`). "Algorithm `3sf-tob-noga` is reorg-resilient."

    Identical in shape to `ThmReorgResilienceGA`; they differ in the algorithm, which is
    not modelled, so the two propositions coincide. Kept separate because the paper does,
    and because they will diverge as soon as `Alg` is more than a comment. -/
def ThmReorgResilienceFFG (out : Node → Config Node Msg NodeState → Out)
    (Pre : Out → Out → Prop) (proposedBy : Time → Out → Prop) (proposing : Time → Time)
    (honestAt : Time → Prop) (x : Exec Pr S) : Prop :=
  ReorgResilient out Pre proposedBy proposing honestAt 0 0 x

/-- **Theorem `thm:dyn-avail-fast-conf-tob-ffg`** (dynamic availability, analogous of
    `thm:dyn-avail-fast-conf-tob`). "Algorithm `3sf-tob-noga` is dynamically-available
    `\wop`." -/
def ThmDynamicAvailabilityFFG (out : Node → Config Node Msg NodeState → Out)
    (Pre : Out → Out → Prop) (mem : Tx → Out → Prop) (pool : Time → Set Tx) (tconf : Time)
    (x : Exec Pr S) : Prop :=
  DynamicallyAvailable out Pre mem pool 0 tconf x

/-- **Theorem `thm:accountable-safety`** (Accountable Safety). "Let `f ∈ [0, n]`. The
    finalized chain `chainfin` is `n/3`-accountable."

    `n / 3` is `Nat` division, which truncates; the paper's `n/3` is exact and the
    resilience is the largest integer below it. For `n` not divisible by 3 these agree; at
    `n = 3k` the paper's reading is `k`, and so is this. Left as `n / 3` rather than
    parameterised, because the constant is the content of the theorem. -/
def ThmAccountableSafety (finalized : Node → Config Node Msg NodeState → Out)
    (Pre : Out → Out → Prop) (culprits : Multiset (SignedMsg Node Msg) → Finset Node)
    (n : Nat) (x : Exec Pr S) : Prop :=
  AccountableSafety finalized Pre culprits (n / 3) x

/-- **Theorem `thm:liveness-chfin`** (Liveness). "Assume `f < n/3`, and let `t` and `t+1`
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

/-- **Theorem `thm:ga-ebb-and-flow`.** "Algorithm `3sf-tob-noga` is a secure ebb-and-flow
    protocol `\wop`." -/
def ThmEbbAndFlow (available finalized : Node → Config Node Msg NodeState → Out)
    (Pre : Out → Out → Prop) (mem : Tx → Out → Prop) (pool : Time → Set Tx)
    (gst gat slack tconf : Time) (x : Exec Pr S) : Prop :=
  SecureEbbAndFlow available finalized Pre mem pool gst gat slack tconf x

end Majorum
