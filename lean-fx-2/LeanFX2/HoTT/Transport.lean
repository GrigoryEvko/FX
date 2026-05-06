import LeanFX2.HoTT.Identity
import LeanFX2.HoTT.Path.Inverse

/-! # HoTT/Transport — transport along paths (constant motive)

Transport is the operation `transport (P : A → Type) (p : Id A a b) :
P a → P b` — substitution along an identity proof.  In MLTT it's
defined by J with motive `λ y _. P a → P y`.

## Status: meta-level + constant motive

This file ships TWO transport variants:

1. **Lean-meta transport** — the standard MLTT-style transport at
   the meta-level (using Lean's `Eq` directly).  This is the form
   downstream HoTT/HIT theorems use for set-level reasoning.

2. **Constant-motive transport** — the special case where the motive
   doesn't depend on the path endpoint.  Trivially the identity
   function, but composes meaningfully with non-trivial path
   structure (e.g. transporting through path concatenation).

## What defers

Full **dependent transport** through kernel-typed `Term` values
requires the dependent J eliminator at the kernel level.  Per
`HoTT/J.lean`'s docstring, kernel-level dep-J needs Tarski
universe codes (Phase 6+), deferred to v1.1.

## Computation laws

* `transport P (refl _) x = x`  — definitional via `Eq.rec`
* `transport P (p · q) x = transport P q (transport P p x)` —
  composition (provable by path induction)
* `transport (λ _. P) p x = x`  — constant motive (identity)

Zero-axiom verified per declaration. -/

namespace LeanFX2

universe carrierLevel valueLevel

/-! ## Lean-meta transport

The standard MLTT-style transport at meta-level using Lean's `Eq`.
For set-level types (where path = equality), this matches the
HoTT-textbook definition. -/

/-- Transport along a path: substitute via the path's equality.
Given `motive : α → Type _` and `pathProof : a = b`, transport
takes `motive a` to `motive b`.

Implementation: this is just `Eq.rec` (a.k.a. `Eq.subst`),
specialized to the motive-dependent form. -/
def Path.transport
    {Carrier : Sort carrierLevel} {leftEndpoint rightEndpoint : Carrier}
    (motive : Carrier → Sort valueLevel)
    (pathProof : Path leftEndpoint rightEndpoint)
    (sourceValue : motive leftEndpoint) :
    motive rightEndpoint :=
  pathProof ▸ sourceValue

/-! ## Computation laws -/

/-- Transport on `refl` is the identity.  This is the ι rule for
identity types: `transport P (refl _) x = x`.  Definitionally true. -/
theorem Path.transport_refl
    {Carrier : Sort carrierLevel} {someEndpoint : Carrier}
    (motive : Carrier → Sort valueLevel)
    (sourceValue : motive someEndpoint) :
    Path.transport motive (Path.refl someEndpoint) sourceValue = sourceValue :=
  rfl

/-- Transport composes: `transport P (p · q) = transport P q ∘
transport P p`.  Proved by path induction on `firstPath`. -/
theorem Path.transport_trans
    {Carrier : Sort carrierLevel}
    {endpoint0 endpoint1 endpoint2 : Carrier}
    (motive : Carrier → Sort valueLevel)
    (firstPath : Path endpoint0 endpoint1)
    (secondPath : Path endpoint1 endpoint2)
    (sourceValue : motive endpoint0) :
    Path.transport motive (Path.trans firstPath secondPath) sourceValue
      = Path.transport motive secondPath
          (Path.transport motive firstPath sourceValue) := by
  cases firstPath
  rfl

/-- Transport with constant motive is identity.  When `motive` is
`fun _ => SomeType` (doesn't depend on the endpoint), transport is
the identity function.  Proved by path induction. -/
theorem Path.transport_const
    {Carrier : Sort carrierLevel} {leftEndpoint rightEndpoint : Carrier}
    (resultType : Sort valueLevel)
    (pathProof : Path leftEndpoint rightEndpoint)
    (sourceValue : resultType) :
    Path.transport (fun _ => resultType) pathProof sourceValue = sourceValue := by
  cases pathProof
  rfl

/-! ## Inversion: transport's symmetric counterpart -/

/-- Transport along the inverse path is the inverse function:
`transport P (symm p) ∘ transport P p = id`.  Standard groupoid
property of transport. -/
theorem Path.transport_symm_inverse_left
    {Carrier : Sort carrierLevel} {leftEndpoint rightEndpoint : Carrier}
    (motive : Carrier → Sort valueLevel)
    (pathProof : Path leftEndpoint rightEndpoint)
    (sourceValue : motive leftEndpoint) :
    Path.transport motive (Path.symm pathProof)
        (Path.transport motive pathProof sourceValue)
      = sourceValue := by
  cases pathProof
  rfl

/-- The other direction: `transport P p ∘ transport P (symm p) = id`. -/
theorem Path.transport_symm_inverse_right
    {Carrier : Sort carrierLevel} {leftEndpoint rightEndpoint : Carrier}
    (motive : Carrier → Sort valueLevel)
    (pathProof : Path leftEndpoint rightEndpoint)
    (sourceValue : motive rightEndpoint) :
    Path.transport motive pathProof
        (Path.transport motive (Path.symm pathProof) sourceValue)
      = sourceValue := by
  cases pathProof
  rfl

/-! ## Smoke samples -/

/-- Transport along refl-Nat is the identity. -/
example (someValue : Nat) :
    Path.transport (fun _ => Nat) (Path.refl 0) someValue = someValue :=
  Path.transport_const Nat (Path.refl 0) someValue

/-- Symmetric inverse smoke: transport ; transport-symm = identity. -/
example (someValue : Nat) :
    Path.transport (fun _ => Nat) (Path.symm (Path.refl 0))
        (Path.transport (fun _ => Nat) (Path.refl 0) someValue)
      = someValue :=
  Path.transport_symm_inverse_left (fun _ => Nat) (Path.refl 0) someValue

end LeanFX2
