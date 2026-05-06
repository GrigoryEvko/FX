/-! # Sessions/Foundation — session protocol inductive

Session types describe communication protocols at the type
level.  A `SessionProtocol payloadType` is a finite tree of
send / receive / branch / select / end nodes parameterized by
a payload-type carrier.

For v1.0 we ship the **structural** protocol grammar — enough
to express bidirectional protocols, branch/select choice, and
recursion via finite unfolding.  Full higher-order session
types (sessions parameterized by sessions, polymorphic carrier
types) defer to v1.1.

## Grammar (per fx_design.md §11.1)

```
S ::= send T . S       -- send payload of type T, continue with S
    | receive T . S    -- receive payload of type T, continue with S
    | branch [ S_1 ; ...; S_n ]  -- offer choice between branches
    | select [ S_1 ; ...; S_n ]  -- choose one branch
    | end              -- terminal: protocol complete
```

Branch and select are dual: branch offers (passive), select
chooses (active).  Duality is the involution of swapping
send <-> receive, branch <-> select, with end fixed.

## Why parameterize by payload type?

The session protocol is "abstract" — it describes the SHAPE of
communication without committing to specific payload types.
Concrete instantiations replace the carrier with `Ty level
scope` for kernel-internal sessions, or with `String` /
`Nat` for surface-level examples.

For v1.0 we ship `SessionProtocol payloadType` as a
type-parameterized inductive.  Instantiation at FX kernel's
`Ty` happens at the bridge (D5.11 → D9.x bridge tasks).

## Zero-axiom

Inductive declaration with finite ctors + structural recursion
on its data.  All theorems propext-free.

## What ships in this file

* `SessionProtocol payloadType` inductive (5 ctors)
* `SessionProtocol.depth` — structural recursion measuring
  protocol nesting depth
* `SessionProtocol.isFinite` — Decidable structural predicate
  certifying that every continuation branch is finite
* Smoke samples: a request-response protocol, a branching
  protocol

## Dependencies

None.  Self-contained at meta-level.

## Downstream consumers

* `Sessions/Duality.lean` — dual involution theorem
* `Sessions/Step.lean` (v1.1) — session-step reduction
* Bridge to FX kernel `Ty.session` (deferred to D5.11 bridge)
-/

namespace LeanFX2

universe payloadLevel

/-- A session protocol over a payload-type carrier.  Five
constructors covering send / receive / branch / select / end.

For v1.0 branch/select are BINARY (two options).  N-ary
branch/select via `List (SessionProtocol _)` would require
Lean's nested-inductive induction tactic, which has limited
support; n-ary form lands in v1.1 alongside a custom recursor. -/
inductive SessionProtocol (PayloadType : Type payloadLevel) :
    Type payloadLevel where
  /-- Terminate the protocol — no further communication. -/
  | endProtocol : SessionProtocol PayloadType
  /-- Send a payload value, then continue with the inner protocol. -/
  | sendStep   (payloadCarrier : PayloadType)
                (continuation : SessionProtocol PayloadType) :
                SessionProtocol PayloadType
  /-- Receive a payload value, then continue with the inner protocol. -/
  | receiveStep (payloadCarrier : PayloadType)
                 (continuation : SessionProtocol PayloadType) :
                 SessionProtocol PayloadType
  /-- Offer a binary choice — the OTHER party picks which branch. -/
  | branchProtocol (leftOption rightOption : SessionProtocol PayloadType) :
                   SessionProtocol PayloadType
  /-- Choose a binary branch — THIS party picks. -/
  | selectProtocol (leftOption rightOption : SessionProtocol PayloadType) :
                   SessionProtocol PayloadType

namespace SessionProtocol

variable {PayloadType : Type payloadLevel}

/-- Compute the structural nesting depth of a protocol.  Useful
for termination measures + bisimulation bounds. -/
def depth : SessionProtocol PayloadType → Nat
  | .endProtocol                      => 0
  | .sendStep    _ continuation        => 1 + continuation.depth
  | .receiveStep _ continuation        => 1 + continuation.depth
  | .branchProtocol leftOption rightOption =>
      1 + Nat.max leftOption.depth rightOption.depth
  | .selectProtocol leftOption rightOption =>
      1 + Nat.max leftOption.depth rightOption.depth

/-- Whether every protocol continuation is finite.  For v1.0's finite
protocol tree this is always provable, but the definition follows the
tree instead of collapsing to `True`; this keeps the interface ready for
recursive protocol nodes without teaching downstream code a vacuous
predicate. -/
def isFinite : SessionProtocol PayloadType → Prop
  | .endProtocol => True
  | .sendStep _ continuation => continuation.isFinite
  | .receiveStep _ continuation => continuation.isFinite
  | .branchProtocol leftOption rightOption =>
      leftOption.isFinite ∧ rightOption.isFinite
  | .selectProtocol leftOption rightOption =>
      leftOption.isFinite ∧ rightOption.isFinite

/-- Every v1.0 session protocol is finite by structural induction. -/
theorem isFinite_of_tree (someProtocol : SessionProtocol PayloadType) :
    someProtocol.isFinite := by
  induction someProtocol with
  | endProtocol => exact trivial
  | sendStep _ _ continuationIH => exact continuationIH
  | receiveStep _ _ continuationIH => exact continuationIH
  | branchProtocol _ _ leftIH rightIH => exact ⟨leftIH, rightIH⟩
  | selectProtocol _ _ leftIH rightIH => exact ⟨leftIH, rightIH⟩

/-- Structural decidability for protocol finiteness. -/
def isFiniteDecidable (someProtocol : SessionProtocol PayloadType) :
    Decidable (someProtocol.isFinite) :=
  match someProtocol with
  | .endProtocol => .isTrue trivial
  | .sendStep _ continuation => isFiniteDecidable continuation
  | .receiveStep _ continuation => isFiniteDecidable continuation
  | .branchProtocol leftOption rightOption =>
      match isFiniteDecidable leftOption, isFiniteDecidable rightOption with
      | .isTrue leftProof, .isTrue rightProof =>
          .isTrue ⟨leftProof, rightProof⟩
      | .isFalse leftRefutation, _ =>
          .isFalse (fun bothFinite => leftRefutation bothFinite.left)
      | _, .isFalse rightRefutation =>
          .isFalse (fun bothFinite => rightRefutation bothFinite.right)
  | .selectProtocol leftOption rightOption =>
      match isFiniteDecidable leftOption, isFiniteDecidable rightOption with
      | .isTrue leftProof, .isTrue rightProof =>
          .isTrue ⟨leftProof, rightProof⟩
      | .isFalse leftRefutation, _ =>
          .isFalse (fun bothFinite => leftRefutation bothFinite.left)
      | _, .isFalse rightRefutation =>
          .isFalse (fun bothFinite => rightRefutation bothFinite.right)

/-- Decidable instance for structural finiteness. -/
instance isFinite.decidable (someProtocol : SessionProtocol PayloadType) :
    Decidable (someProtocol.isFinite) :=
  isFiniteDecidable someProtocol

/-! ## Smoke samples — concrete protocols -/

/-- Request-response over a String payload: send a request,
receive a response, terminate. -/
example : SessionProtocol String :=
  .sendStep "GET /index.html"
    (.receiveStep "<html>...</html>"
      .endProtocol)

/-- Binary branching protocol: offer two completion paths. -/
example : SessionProtocol String :=
  .branchProtocol .endProtocol (.sendStep "ack" .endProtocol)

/-- Depth of `endProtocol` is zero. -/
example :
    (SessionProtocol.endProtocol : SessionProtocol String).depth = 0 := rfl

/-- Depth of `sendStep + endProtocol` is one. -/
example :
    (SessionProtocol.sendStep "msg" .endProtocol
        : SessionProtocol String).depth = 1 := rfl

end SessionProtocol

end LeanFX2
