import the framework's flat multiset-log flavour

/-!
# Majorum's security definitions

The vocabulary its theorems are stated in. Source: the paper's own source,
Definitions 1–7 (`def:safety`, `def:liveness`, `def:security`, `def:dyn-ava`,
`def:reorg-resilience`, `def:acc-safety`, and the unlabelled *Secure ebb-and-flow
protocol*). The protocol was renamed: the paper says 3SF, the paper's macro file binds
`\protocol` to *Majorum*.

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

/-- **Definition 4 (Dynamic Availability).** "A protocol is dynamically-available after
    time `Tdyn` if and only if it is secure after `Tdyn` with confirmation time
    `Tconf = O(κ)`."

    The `O(κ)` is a parameter here, so this says "secure after `tdyn` with *this*
    confirmation time". The paper's second sentence — "dynamically-available if it is
    always secure when `GST = 0`" — is the instance `tdyn = 0` under a synchronous model,
    which the model bundle supplies rather than this definition. -/
def DynamicallyAvailable (out : Node → Config Node Msg NodeState → Out)
    (Pre : Out → Out → Prop) (mem : Tx → Out → Prop) (pool : Time → Set Tx)
    (tdyn tconf : Time) (x : Exec Pr S) : Prop :=
  Secure out Pre mem pool tdyn tconf x

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
    (proposedBy : Time → Node → Out → Prop) (proposing : Time → Time)
    (treorg tReorg : Time) (x : Exec Pr S) : Prop :=
  ∀ (i : Nat) (p q : Node) (t : Time) (o : Out),
    tReorg ≤ x[i].time → x.Honest i p →
    treorg ≤ t → proposedBy t q o → q ∉ S.adv ((proposing t : Int)) →
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
    the available chain is dynamically available; the finalized chain is safe always and
    live after `max(GST, GAT) + O(Δ)`; and the finalized chain is a prefix of the available
    one at every honest validator and round.

    `slack` stands for the `O(Δ)`. The paper's "always safe" means safe from time 0 across
    all partially synchronous executions, hence `tafter = 0` here with the execution
    quantifier left to the caller. -/
def SecureEbbAndFlow (available finalized : Node → Config Node Msg NodeState → Out)
    (Pre : Out → Out → Prop) (mem : Tx → Out → Prop) (pool : Time → Set Tx)
    (gst gat slack tconf : Time) (x : Exec Pr S) : Prop :=
  DynamicallyAvailable available Pre mem pool 0 tconf x ∧
    Secure finalized Pre mem pool (max gst gat + slack) tconf x ∧
    (∀ (i : Nat) (p : Node), x.Honest i p → Pre (finalized p x[i]) (available p x[i]))

end Majorum
