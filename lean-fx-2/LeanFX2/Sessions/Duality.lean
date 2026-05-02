import LeanFX2.Sessions.Foundation

/-! # Sessions/Duality — session protocol duality + involution

Duality of session protocols: `dual P` swaps the roles of the
two participants — every send becomes a receive and vice versa,
every branch becomes a select and vice versa, with `end` fixed.

## Definition

```
dual end                    = end
dual (send T . S)           = receive T . dual S
dual (recv T . S)           = send T . dual S
dual (branch L R)           = select (dual L) (dual R)
dual (select L R)           = branch (dual L) (dual R)
```

## Why duality matters

Every well-typed session connection has TWO endpoints with dual
protocols — one party SENDS what the other RECEIVES, etc.  The
`dual_involutive` theorem (`dual (dual P) = P`) confirms duality
is its own inverse, ensuring symmetric protocol design.

## What ships

* `SessionProtocol.dual` — the involution function
* `SessionProtocol.dual_involutive` — `dual (dual P) = P`
* `SessionProtocol.dual_end` — endProtocol is self-dual
* Smoke samples on concrete protocols

## Zero-axiom

Structural recursion + finite case analysis on the binary
branch/select form (v1.0 simplification).  N-ary branch/select
with full involution proof lands in v1.1 alongside a custom
recursor for the nested-inductive form.

## Dependencies

* `Sessions/Foundation.lean` — SessionProtocol inductive

## Downstream consumers

* `Sessions/Step.lean` (v1.1) — session step + dual progress
* Bridge to FX kernel `Ty.session` (D5.11 bridge — v1.1)
-/

namespace LeanFX2

universe payloadLevel

namespace SessionProtocol

variable {PayloadType : Type payloadLevel}

/-- Compute the dual session: swap send/receive, swap
branch/select, fix end.  Recursive on every continuation. -/
def dual : SessionProtocol PayloadType → SessionProtocol PayloadType
  | .endProtocol => .endProtocol
  | .sendStep    payloadCarrier continuation =>
      .receiveStep payloadCarrier continuation.dual
  | .receiveStep payloadCarrier continuation =>
      .sendStep    payloadCarrier continuation.dual
  | .branchProtocol leftOption rightOption =>
      .selectProtocol leftOption.dual rightOption.dual
  | .selectProtocol leftOption rightOption =>
      .branchProtocol leftOption.dual rightOption.dual

/-! ## Foundational lemmas -/

/-- `endProtocol` is self-dual.  Definitional. -/
theorem dual_end :
    dual (endProtocol : SessionProtocol PayloadType) = endProtocol :=
  rfl

/-- The headline: `dual` is involutive — applying it twice
returns the original protocol.  Discharged by structural
induction on the (non-nested) binary protocol via Lean's
`induction` tactic.  Each non-leaf case rewrites with the IH
on each continuation; the dual definitional unfolding handles
the structural part. -/
theorem dual_involutive (someProtocol : SessionProtocol PayloadType) :
    dual (dual someProtocol) = someProtocol := by
  induction someProtocol with
  | endProtocol => rfl
  | sendStep payloadCarrier continuation continuationIH =>
      show sendStep payloadCarrier (dual (dual continuation))
             = sendStep payloadCarrier continuation
      rw [continuationIH]
  | receiveStep payloadCarrier continuation continuationIH =>
      show receiveStep payloadCarrier (dual (dual continuation))
             = receiveStep payloadCarrier continuation
      rw [continuationIH]
  | branchProtocol leftOption rightOption leftIH rightIH =>
      show branchProtocol (dual (dual leftOption)) (dual (dual rightOption))
             = branchProtocol leftOption rightOption
      rw [leftIH, rightIH]
  | selectProtocol leftOption rightOption leftIH rightIH =>
      show selectProtocol (dual (dual leftOption)) (dual (dual rightOption))
             = selectProtocol leftOption rightOption
      rw [leftIH, rightIH]

/-! ## Smoke samples -/

/-- Dual of "send + receive" is "receive + send". -/
example :
    dual (sendStep "request" (receiveStep "response" endProtocol)
            : SessionProtocol String)
      = receiveStep "request" (sendStep "response" endProtocol) := rfl

/-- Dual of branch is select with dual'd inner protocols. -/
example :
    dual (branchProtocol endProtocol endProtocol
            : SessionProtocol String)
      = selectProtocol endProtocol endProtocol := rfl

/-- Self-application: dual on endProtocol is endProtocol. -/
example :
    dual (endProtocol : SessionProtocol String) = endProtocol := rfl

/-- Concrete involution: dual (dual (send "x" end)) = send "x" end. -/
example :
    dual (dual (sendStep "x" endProtocol : SessionProtocol String))
      = sendStep "x" endProtocol :=
  dual_involutive _

end SessionProtocol

end LeanFX2
