import Framework.Sts2.Protocol

/-!
# Executions, network assumptions, security properties

Liveness is a property of executions, not of reachable states, so
`Common.System`'s state-based `Invariant` machinery cannot express it. Hence
`Execution`, and hence why every network and participation assumption in this
framework is a **predicate on executions** rather than a guard on `Step`: the
two models we care about impose different ones over the same step relation.

Each predicate here is à la carte. A "model" is whichever conjunction of them a
paper assumes — see `Framework.Sts2.Models`.
-/

set_option autoImplicit false

namespace Framework.Sts2

open Common (System)

/-- An infinite execution.

    Labels are *not* recorded: every assumption in this framework is phrased over
    observable state rather than over which transition was taken — `Synchrony`
    says "the message is in that validator's view", not "a delivery step
    occurred". That composes better with state invariants, and it makes exhibiting
    an execution cheaper, since only the existence of a suitable step is needed.

    Re-add a `lbl : Nat → Lbl` field if a genuinely scheduler-level statement
    turns up: "this message is delivered at most once", or a bound on how many
    adversarial steps an execution contains. -/
structure Execution {St Lbl : Type} (Sys : System St Lbl) where
  /-- The configuration after `i` steps. -/
  cfg : Nat → St
  /-- It starts initial. -/
  init : Sys.Init (cfg 0)
  /-- Consecutive configurations are related by some step. -/
  step : ∀ i, ∃ l, Sys.Step l (cfg i) (cfg (i + 1))

/-- `x[i]` is the configuration after `i` steps. Indexing is total, so the
    validity side-condition is trivial. -/
instance {St Lbl : Type} {Sys : System St Lbl} :
    GetElem (Execution Sys) Nat St (fun _ _ => True) where
  getElem x i _ := x.cfg i

variable {V Msg State Ev : Type} [DecidableEq V] [DecidableEq Msg]

/-- Executions of a protocol under a participation rule and a schedule. -/
abbrev Exec (Pr : Protocol V Msg State Ev) (S : Schedule V) :=
  Execution (system V Msg State Ev Pr S)

variable {Pr : Protocol V Msg State Ev} {S : Schedule V}

/-! ### Reading an execution

`x[i]` is the configuration after `i` steps, so `x[i].time` is *real* time there
and `x[i].clock p` is what `p` believes it to be. `x.Awake i p` and `x.Honest i p`
exist only to keep the `Int` coercion on `time` out of every statement.

There is deliberately no `Active`: whether a validator is *participating* — as
opposed to merely awake — is decided by its own program, so no framework-level
predicate can express it. Statements that need it take it as a parameter. -/

/-- Is `p` awake after `i` steps? -/
def Execution.Awake (x : Exec Pr S) (i : Nat) (p : V) : Prop :=
  p ∈ S.awake (x[i].time : Int)

/-- Is `p` still honest after `i` steps? Corruption is time-dependent, so this is
    relative to the round. -/
def Execution.Honest (x : Exec Pr S) (i : Nat) (p : V) : Prop :=
  p ∉ S.adv (x[i].time : Int)

/-! ### Clocks

Nothing about clocks is assumed by the step relation beyond monotonicity, which is
free: `Step.tick` only increments, and never past real time. A property is
therefore in one of three classes, and should assume no more than it needs.

* **Timeless** — mentions neither `time` nor `clock`, so it holds under arbitrary
  asynchrony and arbitrary clock behaviour. Accountable safety belongs here: it is
  a statement about the signed message history alone.
* **Monotone-clock** — uses only that each validator's clock never goes backwards.
  Free from the step relation; no assumption to add.
* **Synchronized** — assumes `Synchronized` below, as both Majorum and TOB-SVD do
  ("validators have synchronized clocks"). Liveness needs this. -/

/-- Every awake validator's clock reads real time.

    Restricted to the awake, because a validator asleep across several rounds wakes
    with a stale clock and can only catch up one `tick` at a time. A model that
    wants waking validators to know the time immediately needs a stronger version,
    or a `tick` that jumps rather than increments. -/
def Synchronized (x : Exec Pr S) : Prop :=
  ∀ (i : Nat) p, x.Awake i p → x[i].clock p = x[i].time

/-! ### Progress -/

/-- Real time does not stop advancing. The mild fairness assumption liveness
    needs; `Step.advance` is always enabled, so this rules out only executions that
    stop using it. -/
def TimeDiverges (x : Exec Pr S) : Prop :=
  ∀ r : Round, ∃ i : Nat, r ≤ x[i].time

/-! `Diligent` used to live here — "every active validator is ticked in every
round". It is gone: `Step.clock` now ticks every active validator as part of
advancing the round, so the property holds by construction and `TimeDiverges` is
the only progress assumption left. It was also the sole consumer of the
execution's step labels, which is why `Execution` no longer records them. -/

/-! ### Network

Every sent message is covered by the guarantee below. Majorum will eventually
want that qualified — "a proposal for slot `t` is gossiped only during the first
Δ rounds of slot `t`", so a proposal sent outside its window is owed nothing —
which means adding a `gossiped : SignedMsg V Msg → Round → Prop` filter as an
extra hypothesis of `Synchrony`. Left out until a model actually restricts it. -/

/-- Δ-synchrony after GST.

    Quantified over **awake** validators — receiving is a function of being
    awake, not of being allowed to send, so a validator still completing a joining
    protocol is owed its backlog. This is what makes sleep work with no extra
    machinery: a sleeping validator incurs no obligation, and the moment it wakes
    the bound already applies to everything sent Δ ago — TOB-SVD's "upon waking up, validators immediately
    receive all messages they should have received while asleep", and Majorum's
    queue-until-wake. Setting `gst = 0` gives TOB-SVD's synchronous network. -/
def Synchrony (gst delta : Round) (x : Exec Pr S) : Prop :=
  ∀ (i j : Nat) p m, m ∈ x[i].sent →
    max x[i].time gst + delta ≤ x[j].time → x.Awake j p → m ∈ x[j].view p

/-- Honest relay: whatever an active validator has seen reaches every active
    validator within Δ (after GST). Majorum makes gossip part of the model —
    "once an adversarial message is received by an honest validator, it is also
    gossiped by it" — so this is a model assumption, not protocol behaviour. -/
def Relay (gst delta : Round) (x : Exec Pr S) : Prop :=
  ∀ (i j : Nat) p q m, x.Awake i p → m ∈ x[i].view p →
    max x[i].time gst + delta ≤ x[j].time → x.Awake j q → m ∈ x[j].view q

/-- Nothing appears in a view unless it was signed and sent. -/
def ViewsSound (x : Exec Pr S) : Prop :=
  ∀ (i : Nat) p m, m ∈ x[i].view p → m ∈ x[i].sent

/-! ### Security properties

Abstract over the protocol's output and its prefix order, so that blocks, chains
and the transaction pool stay out of the framework. `out p c` is what validator
`p` outputs in configuration `c`; `Pre` is "is a prefix of". -/

variable {Out : Type}

/-- Majorum Def. 1 (Safe protocol), after `tafter`: the outputs of validators
    that are honest at the time are always prefix-comparable. -/
def Safe (out : V → Config V Msg State → Out) (Pre : Out → Out → Prop)
    (tafter : Round) (x : Exec Pr S) : Prop :=
  ∀ (i j : Nat) p q, tafter ≤ x[i].time → tafter ≤ x[j].time →
    x.Honest i p → x.Honest j q →
    Pre (out p x[i]) (out q x[j]) ∨ Pre (out q x[j]) (out p x[i])

/-- Majorum Def. 2 (Live protocol), after `tafter` with confirmation time
    `tconf`: a transaction in the pool is output by every awake validator within
    `tconf`. The pool is a parameter, not framework state.

    The paper quantifies over validators *active* in the round, which is a
    protocol-specific notion; stating it over the awake ones is stronger, so a
    protocol whose joining delay matters will want to weaken this with its own
    participation predicate. -/
def Live {Tx : Type} (out : V → Config V Msg State → Out) (mem : Tx → Out → Prop)
    (pool : Round → Set Tx) (tafter tconf : Round) (x : Exec Pr S) : Prop :=
  ∀ (i j : Nat) p tx, tafter ≤ x[i].time → tx ∈ pool x[i].time →
    x[i].time + tconf ≤ x[j].time → x.Awake j p → mem tx (out p x[j])

/-- Majorum Def. 3 (Secure protocol). -/
def Secure {Tx : Type} (out : V → Config V Msg State → Out)
    (Pre : Out → Out → Prop) (mem : Tx → Out → Prop) (pool : Round → Set Tx)
    (tafter tconf : Round) (x : Exec Pr S) : Prop :=
  Safe out Pre tafter x ∧ Live out mem pool tafter tconf x

end Framework.Sts2
