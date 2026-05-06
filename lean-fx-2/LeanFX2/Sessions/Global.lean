import LeanFX2.Sessions.Step

/-! # Sessions/Global - binary-choice global projection

This module imports one narrow idea from Crucible's session stack:
a global protocol can be projected to a local endpoint protocol for a
chosen role.

The shipped slice is deliberately small.  It supports terminal global
protocols, point-to-point transmissions, and binary choices.  Projection
is a relation rather than an executable partial function, so plain
third-party merge is represented by an equality proof between branch
projections.

What remains outside this slice: asynchronous queue types, context
association, subtyping, crash-stop `Stop`, higher-order delegation,
permission flow, vendor grades, and term-level linear protocol
advancement.
-/

namespace LeanFX2

universe roleLevel payloadLevel

/-- A top-down global protocol over role and payload carriers.

`transmit fromRole toRole payload continuation` records one
communication event.  `choice fromRole toRole ...` records a binary
choice made by `fromRole` and observed by `toRole`; the branch label is
positional, following the existing binary `selectProtocol` /
`branchProtocol` local encoding. -/
inductive SessionGlobal
    (Role : Type roleLevel)
    (PayloadType : Type payloadLevel) :
    Type (max roleLevel payloadLevel) where
  /-- No remaining global communication. -/
  | endGlobal : SessionGlobal Role PayloadType
  /-- One role sends one payload to another role, then continues. -/
  | transmit
      (fromRole toRole : Role)
      (payloadCarrier : PayloadType)
      (continuation : SessionGlobal Role PayloadType) :
      SessionGlobal Role PayloadType
  /-- One role chooses one of two payload-labeled branches for another role. -/
  | choice
      (fromRole toRole : Role)
      (leftPayload : PayloadType)
      (leftContinuation : SessionGlobal Role PayloadType)
      (rightPayload : PayloadType)
      (rightContinuation : SessionGlobal Role PayloadType) :
      SessionGlobal Role PayloadType

namespace SessionGlobal

variable {Role : Type roleLevel}
variable {PayloadType : Type payloadLevel}

/-- Structural well-formedness for the shipped global fragment.

The only non-recursive condition is the MPST sanity check that a global
communication event does not send from a role to itself. -/
def isWellFormed : SessionGlobal Role PayloadType → Prop
  | .endGlobal => True
  | .transmit fromRole toRole _ continuation =>
      fromRole ≠ toRole ∧ continuation.isWellFormed
  | .choice fromRole toRole _ leftContinuation _ rightContinuation =>
      fromRole ≠ toRole ∧
        leftContinuation.isWellFormed ∧
        rightContinuation.isWellFormed

/-- A self-transmission is rejected by global well-formedness. -/
theorem transmit_self_not_isWellFormed
    (someRole : Role)
    (payloadCarrier : PayloadType)
    (continuation : SessionGlobal Role PayloadType) :
    ¬ isWellFormed
      (.transmit someRole someRole payloadCarrier continuation) := by
  intro globalWellFormed
  exact globalWellFormed.left rfl

/-- A self-choice is rejected by global well-formedness. -/
theorem choice_self_not_isWellFormed
    (someRole : Role)
    (leftPayload rightPayload : PayloadType)
    (leftContinuation rightContinuation : SessionGlobal Role PayloadType) :
    ¬ isWellFormed
      (.choice someRole someRole
        leftPayload leftContinuation
        rightPayload rightContinuation) := by
  intro globalWellFormed
  exact globalWellFormed.left rfl

/-- Relational projection of a global protocol to one role's local
`SessionProtocol`.

For a transmission, the sender sees `sendStep`, the receiver sees
`receiveStep`, and a third-party role skips the event.  For a choice,
the sender sees `selectProtocol`, the receiver sees `branchProtocol`,
and a third-party role may project only when the two branch projections
plain-merge, represented by `leftProjection = rightProjection`. -/
inductive Projects (observedRole : Role) :
    SessionGlobal Role PayloadType →
    SessionProtocol PayloadType →
    Prop where
  /-- Terminal global protocols project to terminal local protocols. -/
  | endGlobal :
      Projects observedRole .endGlobal .endProtocol
  /-- The sender projection of one global transmission is a local send. -/
  | transmitSender
      {fromRole toRole : Role}
      {payloadCarrier : PayloadType}
      {continuation : SessionGlobal Role PayloadType}
      {projectedContinuation : SessionProtocol PayloadType}
      (roleIsSender : observedRole = fromRole)
      (continuationProjects :
        Projects observedRole continuation projectedContinuation) :
      Projects observedRole
        (.transmit fromRole toRole payloadCarrier continuation)
        (.sendStep payloadCarrier projectedContinuation)
  /-- The receiver projection of one global transmission is a local receive. -/
  | transmitReceiver
      {fromRole toRole : Role}
      {payloadCarrier : PayloadType}
      {continuation : SessionGlobal Role PayloadType}
      {projectedContinuation : SessionProtocol PayloadType}
      (roleIsReceiver : observedRole = toRole)
      (continuationProjects :
        Projects observedRole continuation projectedContinuation) :
      Projects observedRole
        (.transmit fromRole toRole payloadCarrier continuation)
        (.receiveStep payloadCarrier projectedContinuation)
  /-- A third-party role skips a transmission that does not involve it. -/
  | transmitThirdParty
      {fromRole toRole : Role}
      {payloadCarrier : PayloadType}
      {continuation : SessionGlobal Role PayloadType}
      {projectedContinuation : SessionProtocol PayloadType}
      (roleIsNotSender : observedRole ≠ fromRole)
      (roleIsNotReceiver : observedRole ≠ toRole)
      (continuationProjects :
        Projects observedRole continuation projectedContinuation) :
      Projects observedRole
        (.transmit fromRole toRole payloadCarrier continuation)
        projectedContinuation
  /-- The sender projection of a global choice is a local select. -/
  | choiceSender
      {fromRole toRole : Role}
      {leftPayload rightPayload : PayloadType}
      {leftContinuation rightContinuation : SessionGlobal Role PayloadType}
      {leftProjection rightProjection : SessionProtocol PayloadType}
      (roleIsSender : observedRole = fromRole)
      (leftProjects :
        Projects observedRole leftContinuation leftProjection)
      (rightProjects :
        Projects observedRole rightContinuation rightProjection) :
      Projects observedRole
        (.choice fromRole toRole
          leftPayload leftContinuation
          rightPayload rightContinuation)
        (.selectProtocol
          (.sendStep leftPayload leftProjection)
          (.sendStep rightPayload rightProjection))
  /-- The receiver projection of a global choice is a local branch. -/
  | choiceReceiver
      {fromRole toRole : Role}
      {leftPayload rightPayload : PayloadType}
      {leftContinuation rightContinuation : SessionGlobal Role PayloadType}
      {leftProjection rightProjection : SessionProtocol PayloadType}
      (roleIsReceiver : observedRole = toRole)
      (leftProjects :
        Projects observedRole leftContinuation leftProjection)
      (rightProjects :
        Projects observedRole rightContinuation rightProjection) :
      Projects observedRole
        (.choice fromRole toRole
          leftPayload leftContinuation
          rightPayload rightContinuation)
        (.branchProtocol
          (.receiveStep leftPayload leftProjection)
          (.receiveStep rightPayload rightProjection))
  /-- A third-party choice projection exists only when branch
  projections are equal, i.e. the plain-merge fragment. -/
  | choiceThirdParty
      {fromRole toRole : Role}
      {leftPayload rightPayload : PayloadType}
      {leftContinuation rightContinuation : SessionGlobal Role PayloadType}
      {leftProjection rightProjection : SessionProtocol PayloadType}
      (roleIsNotSender : observedRole ≠ fromRole)
      (roleIsNotReceiver : observedRole ≠ toRole)
      (leftProjects :
        Projects observedRole leftContinuation leftProjection)
      (rightProjects :
        Projects observedRole rightContinuation rightProjection)
      (branchProjectionsPlainMerge : leftProjection = rightProjection) :
      Projects observedRole
        (.choice fromRole toRole
          leftPayload leftContinuation
          rightPayload rightContinuation)
        leftProjection

namespace Projects

/-- Every projected local protocol in the finite global fragment is
structurally finite. -/
theorem local_isFinite
    {observedRole : Role}
    {globalProtocol : SessionGlobal Role PayloadType}
    {localProtocol : SessionProtocol PayloadType}
    (projection : Projects observedRole globalProtocol localProtocol) :
    localProtocol.isFinite := by
  induction projection with
  | endGlobal =>
      exact trivial
  | transmitSender _ _ continuationFinite =>
      exact continuationFinite
  | transmitReceiver _ _ continuationFinite =>
      exact continuationFinite
  | transmitThirdParty _ _ _ continuationFinite =>
      exact continuationFinite
  | choiceSender _ _ _ leftFinite rightFinite =>
      exact ⟨leftFinite, rightFinite⟩
  | choiceReceiver _ _ _ leftFinite rightFinite =>
      exact ⟨leftFinite, rightFinite⟩
  | choiceThirdParty _ _ _ _ _ leftFinite _ =>
      exact leftFinite

end Projects

/-! ## Smoke examples -/

namespace Examples

/-- Three roles for projection smoke tests. -/
inductive ExampleRole where
  | client
  | server
  | observer

open ExampleRole

/-- Client-side projection of one request transmission. -/
example :
    Projects client
      (SessionGlobal.transmit client server "request" endGlobal)
      (SessionProtocol.sendStep "request" .endProtocol) :=
  Projects.transmitSender rfl Projects.endGlobal

/-- Server-side projection of one request transmission. -/
example :
    Projects server
      (SessionGlobal.transmit client server "request" endGlobal)
      (SessionProtocol.receiveStep "request" .endProtocol) :=
  Projects.transmitReceiver rfl Projects.endGlobal

/-- Third-party projection skips unrelated point-to-point transmission. -/
example :
    Projects observer
      (SessionGlobal.transmit client server "request" endGlobal)
      (SessionProtocol.endProtocol : SessionProtocol String) :=
  Projects.transmitThirdParty
    (by intro roleEquality; cases roleEquality)
    (by intro roleEquality; cases roleEquality)
    Projects.endGlobal

/-- Sender-side projection of a binary global choice. -/
example :
    Projects client
      (SessionGlobal.choice client server
        "ok" endGlobal
        "error" endGlobal)
      (SessionProtocol.selectProtocol
        (SessionProtocol.sendStep "ok" .endProtocol)
        (SessionProtocol.sendStep "error" .endProtocol)) :=
  Projects.choiceSender rfl Projects.endGlobal Projects.endGlobal

/-- Receiver-side projection of a binary global choice. -/
example :
    Projects server
      (SessionGlobal.choice client server
        "ok" endGlobal
        "error" endGlobal)
      (SessionProtocol.branchProtocol
        (SessionProtocol.receiveStep "ok" .endProtocol)
        (SessionProtocol.receiveStep "error" .endProtocol)) :=
  Projects.choiceReceiver rfl Projects.endGlobal Projects.endGlobal

/-- Third-party projection of a choice succeeds when both branches
project to the same local protocol. -/
example :
    Projects observer
      (SessionGlobal.choice client server
        "ok" endGlobal
        "error" endGlobal)
      (SessionProtocol.endProtocol : SessionProtocol String) :=
  Projects.choiceThirdParty
    (by intro roleEquality; cases roleEquality)
    (by intro roleEquality; cases roleEquality)
    Projects.endGlobal
    Projects.endGlobal
    rfl

end Examples

end SessionGlobal
end LeanFX2
