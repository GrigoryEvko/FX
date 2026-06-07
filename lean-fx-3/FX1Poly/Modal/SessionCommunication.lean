import FX1Poly.Modal.SessionDualityDimension

/-! # FX1Poly/Modal/SessionCommunication
    — the session-type OPERATIONAL semantics (§11.3) over the duality algebra: communication preserves
      duality (session fidelity) and a dual channel never deadlocks except at completion

`SessionDualityDimension.lean` built the session-type ALGEBRA — the protocol structure and its duality
involution.  This file adds the dynamics: a single COMMUNICATION step between two channel endpoints, and the
two safety properties that make session types worth having.

A channel is created as a pair of DUAL endpoint types (§11.2): one endpoint follows `S`, the other follows
`dual S`.  `CommStep` is one synchronized communication: a matched `send`/`receive` payload exchange, or a
`selectChoice`/`branchOffer` resolution where the selecting endpoint picks a branch and the offering endpoint
follows.  Both endpoints advance to their continuations.

## The two safety properties

  * **Session fidelity** (`CommStep.preservesDuality`): if a channel's two endpoints are DUAL and a
    communication step fires, the residual endpoints are STILL dual.  This is the essence of session-type
    safety — a well-formed channel can never reach a mismatched state (a `send` meeting a `send`, or a payload
    type mismatch): duality, the invariant that the endpoints are compatible, is preserved by every step.  The
    dual hypothesis is exactly what forces the continuations to match (the `send p . S` / `receive p . dual S`
    shape pins `dual S` as the receiver's continuation).
  * **Progress / deadlock-freedom** (`dualChannelProgressesOrIsDone`): a dual channel is either at the terminal
    state `(endSession, endSession)` (the protocol completed) or it CAN take a communication step.  There are no
    stuck states except completion — the §11.11 deadlock-freedom guarantee for a single channel.

## What lands here (all zero-axiom)

  * `CommStep` (6-arm inductive relation on pairs of endpoints) + `concreteChannelStep` (a non-vacuity witness:
    `send 0 . end` / `receive 0 . end` actually steps to `(end, end)`).
  * **`CommStep.preservesDuality`** — session fidelity (the headline): `dual` pair → step → `dual` pair.
  * `dualPairProgresses` — a non-`end` dual channel can always step; `dualChannelProgressesOrIsDone` — the
    progress dichotomy (step or terminal); `endChannelIsTerminal` — the completed channel `(end, end)` has no
    step.

## Zero-axiom verification

`CommStep` is an inductive `Prop` relation.  `preservesDuality` is `cases step` + `injection` (the dual
hypothesis, after the constructor flips it through `dual`, injects to the residual duality and auto-substitutes
the residual endpoint, closing each arm by `rfl`).  `dualPairProgresses` / `dualChannelProgressesOrIsDone`
exhibit the step constructor per case; `endChannelIsTerminal` is `cases step` over an `endSession`-headed pair
(no arm applies).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-- One COMMUNICATION step between two channel endpoints (§11.3).  A matched `send`/`receive` exchanges a
payload of the same type and both advance; a `selectChoice`/`branchOffer` is resolved by the selecting endpoint
picking the left or the right branch, the offering endpoint following.  The relation steps a PAIR of endpoint
protocols to their pair of continuations. -/
inductive CommStep : SessionType × SessionType → SessionType × SessionType → Prop
  | exchangeSendReceive (payload : Nat) (sender receiver : SessionType) :
      CommStep (SessionType.send payload sender, SessionType.receive payload receiver) (sender, receiver)
  | exchangeReceiveSend (payload : Nat) (receiver sender : SessionType) :
      CommStep (SessionType.receive payload receiver, SessionType.send payload sender) (receiver, sender)
  | selectLeft (leftA rightA leftB rightB : SessionType) :
      CommStep (SessionType.selectChoice leftA rightA, SessionType.branchOffer leftB rightB) (leftA, leftB)
  | selectRight (leftA rightA leftB rightB : SessionType) :
      CommStep (SessionType.selectChoice leftA rightA, SessionType.branchOffer leftB rightB) (rightA, rightB)
  | offerLeft (leftA rightA leftB rightB : SessionType) :
      CommStep (SessionType.branchOffer leftA rightA, SessionType.selectChoice leftB rightB) (leftA, leftB)
  | offerRight (leftA rightA leftB rightB : SessionType) :
      CommStep (SessionType.branchOffer leftA rightA, SessionType.selectChoice leftB rightB) (rightA, rightB)

/-- ★ **Session fidelity** (§11.3) — communication preserves duality.  If a channel's two endpoints are DUAL
(`secondEndpoint = dual firstEndpoint`) and a communication step fires, the residual endpoints are STILL dual.
A well-formed channel can never reach a mismatched state: the duality invariant (the endpoints are compatible)
is maintained by every step.  Per arm, the dual hypothesis — after the constructor exposes `dual` on the
first endpoint — injects to exactly the residual duality. -/
theorem CommStep.preservesDuality {firstEndpoint secondEndpoint firstResidual secondResidual : SessionType}
    (dualEq : secondEndpoint = firstEndpoint.dual)
    (step : CommStep (firstEndpoint, secondEndpoint) (firstResidual, secondResidual)) :
    secondResidual = firstResidual.dual := by
  cases step with
  | exchangeSendReceive payload sender receiver => injection dualEq
  | exchangeReceiveSend payload receiver sender => injection dualEq
  | selectLeft leftA rightA leftB rightB => injection dualEq
  | selectRight leftA rightA leftB rightB => injection dualEq
  | offerLeft leftA rightA leftB rightB => injection dualEq
  | offerRight leftA rightA leftB rightB => injection dualEq

/-- A non-`end` dual channel can always take a communication step — every protocol that has not yet completed
offers a matched action to its dual partner. -/
theorem dualPairProgresses (session : SessionType) (notEnd : session ≠ SessionType.endSession) :
    ∃ result, CommStep (session, session.dual) result := by
  cases session with
  | endSession => exact absurd rfl notEnd
  | send payload rest => exact ⟨(rest, rest.dual), CommStep.exchangeSendReceive payload rest rest.dual⟩
  | receive payload rest => exact ⟨(rest, rest.dual), CommStep.exchangeReceiveSend payload rest rest.dual⟩
  | selectChoice left right =>
      exact ⟨(left, left.dual), CommStep.selectLeft left right left.dual right.dual⟩
  | branchOffer left right =>
      exact ⟨(left, left.dual), CommStep.offerLeft left right left.dual right.dual⟩

/-- **Progress / deadlock-freedom** (§11.11) — a dual channel is either at the terminal state `(end, end)` (the
protocol completed) or it CAN communicate.  No stuck states except completion: a dual channel never deadlocks
mid-protocol. -/
theorem dualChannelProgressesOrIsDone (session : SessionType) :
    (∃ result, CommStep (session, session.dual) result) ∨
    (session, session.dual) = (SessionType.endSession, SessionType.endSession) := by
  cases session with
  | endSession => exact Or.inr rfl
  | send payload rest =>
      exact Or.inl ⟨(rest, rest.dual), CommStep.exchangeSendReceive payload rest rest.dual⟩
  | receive payload rest =>
      exact Or.inl ⟨(rest, rest.dual), CommStep.exchangeReceiveSend payload rest rest.dual⟩
  | selectChoice left right =>
      exact Or.inl ⟨(left, left.dual), CommStep.selectLeft left right left.dual right.dual⟩
  | branchOffer left right =>
      exact Or.inl ⟨(left, left.dual), CommStep.offerLeft left right left.dual right.dual⟩

/-- The completed channel `(endSession, endSession)` is TERMINAL — no communication step applies (every
`CommStep` arm requires a `send` / `receive` / choice head, none an `endSession`). -/
theorem endChannelIsTerminal :
    ¬ ∃ result, CommStep (SessionType.endSession, SessionType.endSession) result := by
  rintro ⟨result, step⟩; cases step

/-- A concrete dual channel actually communicates: `send 0 . end` paired with its dual `receive 0 . end`
exchanges the payload and both reach `endSession`.  Non-vacuity witness for `CommStep`. -/
theorem concreteChannelStep :
    CommStep (SessionType.send 0 SessionType.endSession, SessionType.receive 0 SessionType.endSession)
      (SessionType.endSession, SessionType.endSession) :=
  CommStep.exchangeSendReceive 0 SessionType.endSession SessionType.endSession

/-! ## Why duality is NECESSARY — a non-dual channel can deadlock (§27.2-flavored necessity)

`dualChannelProgressesOrIsDone` shows a DUAL channel never deadlocks (it steps or is done).  This section is
the complementary NECESSITY: drop the duality hypothesis and deadlock returns.  A mismatched channel where both
endpoints try to `send` — `(send 0 . end, send 0 . end)` — has NO communication step (no arm matches two
senders) yet is NOT terminal: a genuine stuck state.  And it is exactly NON-dual (`send 0 . end ≠ dual (send 0 .
end) = receive 0 . end`).  So the duality hypothesis in the progress theorem is ESSENTIAL — without it channels
can deadlock mid-protocol.  This is the session analogue of "untyped Ω is not SN" (`SN-NECESSITY`): the
discipline is what rules out the bad behavior. -/

/-- A mismatched `send`/`send` channel is STUCK — no `CommStep` applies (the exchange arm needs one sender and
one receiver; two senders never match). -/
theorem sendSendStuck :
    ¬ ∃ result, CommStep (SessionType.send 0 SessionType.endSession,
      SessionType.send 0 SessionType.endSession) result := by
  rintro ⟨result, step⟩; cases step

/-- The mismatched `send`/`send` channel is NOT dual — its second endpoint differs from the dual of its first
(`send 0 . end ≠ receive 0 . end`).  This is exactly the channel that deadlocks. -/
theorem sendSendIsNotDual :
    SessionType.send 0 SessionType.endSession ≠ (SessionType.send 0 SessionType.endSession).dual := by
  decide

/-- ★ A non-dual channel can DEADLOCK — there is a configuration that is non-dual, stuck (no step), and not the
terminal `(end, end)`.  The bad behavior the duality discipline rules out. -/
theorem nonDualChannelDeadlocks :
    ∃ first second : SessionType,
      second ≠ first.dual ∧
      (¬ ∃ result, CommStep (first, second) result) ∧
      (first, second) ≠ (SessionType.endSession, SessionType.endSession) :=
  ⟨SessionType.send 0 SessionType.endSession, SessionType.send 0 SessionType.endSession,
   sendSendIsNotDual, sendSendStuck, by decide⟩

/-- The duality discipline is precisely the FIX: the SAME first endpoint `send 0 . end` DEADLOCKS with a
mismatched partner `send 0 . end`, but COMMUNICATES with its dual partner `receive 0 . end` (`concreteChannel
Step`).  Duality is exactly the condition that turns a stuck channel into a progressing one. -/
theorem dualPartnerFixesTheMismatchedDeadlock :
    (¬ ∃ result, CommStep (SessionType.send 0 SessionType.endSession,
      SessionType.send 0 SessionType.endSession) result) ∧
    (∃ result, CommStep (SessionType.send 0 SessionType.endSession,
      SessionType.receive 0 SessionType.endSession) result) :=
  ⟨sendSendStuck, ⟨_, concreteChannelStep⟩⟩

/-- ★ **Duality is necessary for deadlock-freedom.**  A DUAL channel always progresses or is done
(`dualChannelProgressesOrIsDone`), but a NON-dual channel can deadlock (`nonDualChannelDeadlocks`).  So the
duality hypothesis is essential to the §11.11 deadlock-freedom guarantee — it is exactly what session typing
enforces, and exactly what rules out stuck channels. -/
theorem dualityIsNecessaryForDeadlockFreedom :
    (∀ session : SessionType,
      (∃ result, CommStep (session, session.dual) result) ∨
      (session, session.dual) = (SessionType.endSession, SessionType.endSession)) ∧
    (∃ first second : SessionType,
      second ≠ first.dual ∧
      (¬ ∃ result, CommStep (first, second) result) ∧
      (first, second) ≠ (SessionType.endSession, SessionType.endSession)) :=
  ⟨dualChannelProgressesOrIsDone, nonDualChannelDeadlocks⟩

end FX1Poly.Modal
