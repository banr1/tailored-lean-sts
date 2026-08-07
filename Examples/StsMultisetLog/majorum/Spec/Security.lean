import the framework's flat multiset-log flavour

/-!
# Majorum's security definitions

The vocabulary its theorems are stated in. Source: arXiv:2601.03862v1,
Definitions 1–7 — Safe, Live, Secure, Dynamic Availability, Reorg Resilience, Accountable
Safety, and Secure ebb-and-flow protocol.

`Safe`, `Live` and `Secure` are Definitions 1–3 and already live in
`the framework's flat multiset-log flavour.Execution`, since they are protocol-independent. What is here is the four
notions specific to this paper's claims.

## What cannot be said yet, and is therefore absent

* **`\wop` and `negl(λ)`, `negl(κ)`.** Several theorems hold *with overwhelming
  probability*; there is no probability layer, so the definitions below state the
  deterministic core and the qualifier is dropped. A theorem rendered here is therefore
  **weaker than nothing** if read as the paper's claim — it is the shape of the claim, not
  the claim.
* **`O(κ)` and `O(Δ)`.** Asymptotic confirmation times become explicit parameters
  (`tconf`, `slack`). A statement quantified over those parameters is not the same as one
  asserting a bound exists in the right order.
* **Cryptographic proof.** Accountable safety's "generate a cryptographic proof" is
  rendered as a *function from the message log to a set of validators*, which is what the
  proof would be evidence for. Unforgeability is idealized away, as a sibling formalization does for signatures.

Everything is parameterised: the protocol's outputs, the prefix order, the transaction
pool. Nothing here commits to blocks or chains, per the framework's own boundary.
-/

set_option autoImplicit false

namespace Majorum

open the framework's flat multiset-log flavour

variable {Node Msg NodeState Ev Out Tx : Type} [DecidableEq Node] [DecidableEq Msg]
  {Pr : Protocol Node Msg NodeState Ev} {S : Schedule Node}

/-- Two outputs conflict when neither is a prefix of the other. The paper writes this of
    chains; `Pre` is the prefix order, supplied by the model. -/
def Conflicts (Pre : Out → Out → Prop) (a b : Out) : Prop :=
  ¬ Pre a b ∧ ¬ Pre b a

/-- **Definition 2 (Live protocol), over the paper's `H_r`.** "…any rounds `r ≥ Tsec` and
    `r_i ≥ r + Tconf`, any transaction `tx` in the transaction pool at time `r`, and any
    validator `v_i` **active** in round `r_i`, `tx ∈ Ch^{r_i}_i`."

    The framework's `Live` quantifies over validators *awake* at the later round, which is a
    larger set than the paper's `H_r` and makes the definition false of this model: a
    validator that has just woken has stepped nowhere, so its output is still genesis, and
    the vote-round write is behind the joining condition `activeAt ≤ r` in any case. `H_r` is
    the paper's own notion — "`H_r` … the set of active validators at round `r`" — so this,
    not the framework's, is Majorum's Definition 2.

    `active` is model-supplied, as `proposedBy`/`proposing` are below: `ActiveAtRound Q S`
    for Algorithms 2 and 5. Honesty need not be conjoined — the paper notes that "awake,
    asleep, and active apply only to honest validators", and the model says the same by
    keeping `S.awake` disjoint from `S.adv`. -/
def LiveActive (out : Node → Config Node Msg NodeState → Out) (mem : Tx → Out → Prop)
    (pool : Time → Set Tx) (active : Node → Time → Prop) (tafter tconf : Time)
    (x : Exec Pr S) : Prop :=
  ∀ (i j : Nat) (p : Node) (tx : Tx), tafter ≤ x[i].time → tx ∈ pool x[i].time →
    x[i].time + tconf ≤ x[j].time → active p x[j].time → mem tx (out p x[j])

/-- **Definition 3 (Secure protocol)** over `LiveActive`: safe after `tafter`, and live after
    it with confirmation time `tconf`. The safety half is the framework's, which quantifies
    over *honest* validators and does match the paper's Definition 1. -/
def SecureActive (out : Node → Config Node Msg NodeState → Out) (Pre : Out → Out → Prop)
    (mem : Tx → Out → Prop) (pool : Time → Set Tx) (active : Node → Time → Prop)
    (tafter tconf : Time) (x : Exec Pr S) : Prop :=
  Safe out Pre tafter x ∧ LiveActive out mem pool active tafter tconf x

/-- **Definition 4 (Dynamic Availability).** "A protocol is dynamically available after time
    `Tdyn` if and only if it is secure after `Tdyn` with confirmation time `Tconf = O(κ)`."

    The `O(κ)` is a parameter here, so this says "secure after `tdyn` with *this*
    confirmation time". The paper's second sentence — "dynamically available if it is always
    secure when `GST = 0`" — is the instance `tdyn = 0` under a synchronous model, which the
    model bundle supplies rather than this definition. -/
def DynamicallyAvailable (out : Node → Config Node Msg NodeState → Out)
    (Pre : Out → Out → Prop) (mem : Tx → Out → Prop) (pool : Time → Set Tx)
    (active : Node → Time → Prop) (tdyn tconf : Time) (x : Exec Pr S) : Prop :=
  SecureActive out Pre mem pool active tdyn tconf x

/-- **Definition 5 (Reorg Resilience).** "A protocol is reorg-resilient after slot
    `treorg` and time `Treorg` in executions `E` if, for any `E`-execution, round
    `r ≥ Treorg`, and validator `v_i` honest in `r`, any chain proposed in slot `t ≥ treorg`
    by a validator honest in `proposing(t)` does not conflict with `Chain^r_i`."

    `proposedBy t q o` reads "in slot `t`, validator `q` proposed `o`" — model-supplied,
    since the framework has no notion of a proposer. Honesty of that proposer is *not* a
    parameter: it is `q ∉ S.adv (proposing t)`, the same notion `Execution.Honest` uses, at
    the round the paper names. An earlier version took an opaque `honestAt : Time → Prop`
    connected to neither the proposer nor the schedule, which `fun _ => True` discharges.

    "Reorg-resilient" unqualified is this at `treorg = 0`, `Treorg = 0`. The execution class
    `E` is not here: it is the hypothesis each theorem in `Theorems.lean` supplies. -/
def ReorgResilient (out : Node → Config Node Msg NodeState → Out) (Pre : Out → Out → Prop)
    (proposedBy : Int → Node → Out → Prop) (proposing : Int → Int)
    (treorg : Int) (tReorg : Time) (x : Exec Pr S) : Prop :=
  ∀ (i : Nat) (p q : Node) (t : Int) (o : Out),
    tReorg ≤ x[i].time → x.Honest i p →
    treorg ≤ t → proposedBy t q o → q ∉ S.adv (proposing t) →
    ¬ Conflicts Pre o (out p x[i])

/-- **Definition 6 (Accountable Safety), with resilience `facc`.** "Upon a safety
    violation, and given access to all messages sent, it is possible to identify at least
    `facc` responsible validators… Such a proof cannot falsely accuse any honest
    participant."

    Two conjuncts, matching the two sentences. `culprits` is the identification procedure,
    reading only the message log — which is what "given access to all messages sent" means,
    and why it is a function of `Config.sent` alone.

    Note what the second conjunct quantifies over: a validator that `culprits` names must
    be adversarial *at the time it is named*, so an honest validator that is corrupted
    later is not retroactively accused. -/
def AccountableSafety (out : Node → Config Node Msg NodeState → Out) (Pre : Out → Out → Prop)
    (culprits : Multiset (SignedMsg Node Msg) → Finset Node) (facc : Nat) (x : Exec Pr S) :
    Prop :=
  (∀ (i j : Nat) (p q : Node), x.Honest i p → x.Honest j q →
      Conflicts Pre (out p x[i]) (out q x[j]) →
      ∀ k : Nat, max i j ≤ k → facc ≤ (culprits x[k].sent).card) ∧
    (∀ (k : Nat) (p : Node), p ∈ culprits x[k].sent → p ∈ S.adv (x[k].time : Int))

/-- **Definition 7 (Secure ebb-and-flow protocol).** Three conjuncts, in the paper's order:
    the available chain is dynamically available; the finalized chain is "always safe and
    live after `max(GST, GAT) + O(Δ)`"; and the finalized chain is a prefix of the available
    one at every honest validator and round.

    `slack` stands for the `O(Δ)`. "Always" is *safe from time 0* across all partially
    synchronous executions, so the safety and liveness halves of the middle conjunct carry
    **different** time bounds — `0` and `max gst gat + slack` — rather than the one bound a
    single `SecureActive` would impose. The execution quantifier is left to the caller. -/
def SecureEbbAndFlow (available finalized : Node → Config Node Msg NodeState → Out)
    (Pre : Out → Out → Prop) (mem : Tx → Out → Prop) (pool : Time → Set Tx)
    (active : Node → Time → Prop) (gst gat slack tconf : Time) (x : Exec Pr S) : Prop :=
  DynamicallyAvailable available Pre mem pool active 0 tconf x ∧
    (Safe finalized Pre 0 x ∧
      LiveActive finalized mem pool active (max gst gat + slack) tconf x) ∧
    (∀ (i : Nat) (p : Node), x.Honest i p → Pre (finalized p x[i]) (available p x[i]))

end Majorum
