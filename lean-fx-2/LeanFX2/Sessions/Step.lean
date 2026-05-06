import LeanFX2.Sessions.Duality

/-! # Sessions/Step - protocol-level session transitions

This module gives the previously empty session-step scaffold a real,
zero-axiom protocol transition layer.  It is deliberately **not** a
term-level beta rule for `Term.sessionSend` / `Term.sessionRecv`: the
current typed-term constructors still return the same `Ty.session`
index and therefore cannot express linear protocol advancement.

What ships here is the honest precursor needed for that integration:

* endpoint actions for send, receive, branch offer, and branch select;
* a typed relation `SessionProtocol.Step source action target`;
* preservation of structural finiteness across a protocol step;
* duality of steps, matching send with receive and select with offer.

This follows the minimal binary-session slice already present in
`Sessions/Foundation.lean`.  Multiparty sessions, asynchronous queues,
permission threading, and recursive protocol variables remain outside
this kernel slice until the term-level session index can carry a real
protocol position.
-/

namespace LeanFX2

universe payloadLevel

namespace SessionProtocol

variable {PayloadType : Type payloadLevel}

/-- A local endpoint action observed at the head of a session protocol.

The branch/select cases are separated intentionally.  `select*` is the
active endpoint choosing a branch; `offer*` is the passive endpoint
accepting the peer's choice.  Duality swaps those roles. -/
inductive Action (PayloadType : Type payloadLevel) : Type payloadLevel where
  /-- Send a payload whose carrier is described by the protocol head. -/
  | sendPayload (payloadCarrier : PayloadType) : Action PayloadType
  /-- Receive a payload whose carrier is described by the protocol head. -/
  | receivePayload (payloadCarrier : PayloadType) : Action PayloadType
  /-- Actively choose the left continuation of a `selectProtocol`. -/
  | selectLeftBranch : Action PayloadType
  /-- Actively choose the right continuation of a `selectProtocol`. -/
  | selectRightBranch : Action PayloadType
  /-- Passively accept the peer selecting the left branch of a `branchProtocol`. -/
  | offerLeftBranch : Action PayloadType
  /-- Passively accept the peer selecting the right branch of a `branchProtocol`. -/
  | offerRightBranch : Action PayloadType

namespace Action

/-- Swap a local endpoint action to the corresponding peer action. -/
def dual : Action PayloadType → Action PayloadType
  | .sendPayload payloadCarrier => .receivePayload payloadCarrier
  | .receivePayload payloadCarrier => .sendPayload payloadCarrier
  | .selectLeftBranch => .offerLeftBranch
  | .selectRightBranch => .offerRightBranch
  | .offerLeftBranch => .selectLeftBranch
  | .offerRightBranch => .selectRightBranch

/-- Endpoint-action duality is an involution. -/
theorem dual_involutive (someAction : Action PayloadType) :
    someAction.dual.dual = someAction := by
  cases someAction <;> rfl

end Action

/-- One protocol transition at the head of a binary session tree.

The relation is intentionally payload-parametric and does not require
`DecidableEq PayloadType`; a send step carries the exact payload carrier
from the protocol head into the action. -/
inductive Step :
    SessionProtocol PayloadType →
    Action PayloadType →
    SessionProtocol PayloadType →
    Prop where
  /-- Sending advances to the send continuation. -/
  | sendStep (payloadCarrier : PayloadType)
      (continuation : SessionProtocol PayloadType) :
      Step (.sendStep payloadCarrier continuation)
        (.sendPayload payloadCarrier)
        continuation
  /-- Receiving advances to the receive continuation. -/
  | receiveStep (payloadCarrier : PayloadType)
      (continuation : SessionProtocol PayloadType) :
      Step (.receiveStep payloadCarrier continuation)
        (.receivePayload payloadCarrier)
        continuation
  /-- Choosing the left select branch advances to the left continuation. -/
  | selectLeft (leftOption rightOption : SessionProtocol PayloadType) :
      Step (.selectProtocol leftOption rightOption)
        .selectLeftBranch
        leftOption
  /-- Choosing the right select branch advances to the right continuation. -/
  | selectRight (leftOption rightOption : SessionProtocol PayloadType) :
      Step (.selectProtocol leftOption rightOption)
        .selectRightBranch
        rightOption
  /-- Accepting the peer's left branch choice advances to the left continuation. -/
  | offerLeft (leftOption rightOption : SessionProtocol PayloadType) :
      Step (.branchProtocol leftOption rightOption)
        .offerLeftBranch
        leftOption
  /-- Accepting the peer's right branch choice advances to the right continuation. -/
  | offerRight (leftOption rightOption : SessionProtocol PayloadType) :
      Step (.branchProtocol leftOption rightOption)
        .offerRightBranch
        rightOption

namespace Step

/-- A protocol step preserves structural finiteness of the protocol tree. -/
theorem preserves_isFinite
    {source target : SessionProtocol PayloadType}
    {observedAction : Action PayloadType}
    (stepTransition : Step source observedAction target) :
    source.isFinite → target.isFinite := by
  intro sourceIsFinite
  cases stepTransition with
  | sendStep _ _ => exact sourceIsFinite
  | receiveStep _ _ => exact sourceIsFinite
  | selectLeft _ _ => exact sourceIsFinite.left
  | selectRight _ _ => exact sourceIsFinite.right
  | offerLeft _ _ => exact sourceIsFinite.left
  | offerRight _ _ => exact sourceIsFinite.right

/-- A protocol step dualizes to the matching peer-side step. -/
theorem dual
    {source target : SessionProtocol PayloadType}
    {observedAction : Action PayloadType}
    (stepTransition : Step source observedAction target) :
    Step source.dual observedAction.dual target.dual := by
  cases stepTransition with
  | sendStep =>
      exact Step.receiveStep _ _
  | receiveStep =>
      exact Step.sendStep _ _
  | selectLeft =>
      exact Step.offerLeft _ _
  | selectRight =>
      exact Step.offerRight _ _
  | offerLeft =>
      exact Step.selectLeft _ _
  | offerRight =>
      exact Step.selectRight _ _

end Step

/-! ## Smoke examples -/

example :
    Step
      (sendStep "request" (receiveStep "response" endProtocol)
        : SessionProtocol String)
      (Action.sendPayload "request")
      (receiveStep "response" endProtocol) :=
  Step.sendStep _ _

example :
    Step
      (dual (sendStep "request" endProtocol : SessionProtocol String))
      (Action.dual (Action.sendPayload "request"))
      (dual (endProtocol : SessionProtocol String)) :=
  Step.dual (Step.sendStep "request" endProtocol)

end SessionProtocol

end LeanFX2
