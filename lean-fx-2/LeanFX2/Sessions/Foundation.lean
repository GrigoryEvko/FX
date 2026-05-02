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
* `SessionProtocol.isFinite` — Decidable predicate (every finite
  protocol is finite — trivially `True`; included for
  completeness with v1.1's recursive protocols)
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

/-- Whether the protocol terminates — for v1.0's finite
protocol tree, always `True`.  Included as a placeholder for
v1.1's recursive protocols where termination becomes
non-trivial (productivity check). -/
def isFinite (_someProtocol : SessionProtocol PayloadType) : Prop := True

/-- Decidable instance for finiteness — trivially `isTrue`. -/
instance isFinite.decidable (someProtocol : SessionProtocol PayloadType) :
    Decidable (someProtocol.isFinite) :=
  .isTrue trivial

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
