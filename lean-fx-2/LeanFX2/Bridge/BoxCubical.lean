import LeanFX2.Cubical.Path

/-! # Bridge/BoxCubical

Box commutes with cubical paths at the rfl-fragment.

## Deliverable

This module ships the canonical reflexive fragment of the
"`□` commutes with `Path`" coherence statement.

The full theorem
```
□ (Path A x y)  ≃  Path (□ A) (boxIntro x) (boxIntro y)
```
needs Phase 12.A.6+ infrastructure (typed `Ty.modal`-bearing
`Term.boxIntro` / `Term.boxElim` ctors plus the cross-mode
`Modality.box` 1-cell) AND a proper transport-style commutation
mechanism (D2.5.1 typed `transpBeta` cascade — strategically
deferred per `Smoke/AuditPhase12A2Day2.lean`).

What IS shippable today is the **rfl-fragment** translation: a
canonical constant-path inside `Term.modIntro` corresponds to a
canonical constant-path on the `RawTerm.modIntro`-wrapped
endpoint.  The bridge maps the two constant-path shapes,
projects to raw via `rfl`, and round-trips both ways via `rfl`.

This mirrors the design of `Bridge/PathToId.lean` /
`Bridge/IdToPath.lean` (rfl-fragment only, with explicit
`_onCanonical` suffixes marking the scope) and the sibling
`Bridge/BoxObservational.lean` (the `Ty.id` analog).

## What ships (10 declarations)

| Name | Direction | Shape |
|------|-----------|-------|
| `boxCubicalRefl` | LHS → RHS forward bridge |
| `boxCubicalRefl_toRaw` | raw projection of the forward bridge |
| `boxCubicalRefl_onCanonical` | canonical-input simplification |
| `cubicalBoxRefl` | RHS → LHS backward bridge |
| `cubicalBoxRefl_toRaw` | raw projection of the backward bridge |
| `cubicalBoxRefl_onCanonical` | canonical-input simplification |
| `boxCubicalRefl_roundTrip_onConstantPath` | LHS → RHS → LHS = id |
| `cubicalBoxRefl_roundTrip_onConstantPath` | RHS → LHS → RHS = id |
| `boxCubicalRefl_roundTrip_toRaw` | raw smoke for LHS round trip |
| `cubicalBoxRefl_roundTrip_toRaw` | raw smoke for RHS round trip |

## What does NOT ship

* **Arbitrary boxed-path translation**: for `pathTerm` constructed
  via non-constant body (i.e. not a constant-path shape), no
  bridge is shipped.  This requires the typed cubical transport
  infrastructure, which depends on the deferred D2.5.1 typed
  `transpBeta` cascade.
* **Headline `Equiv`**: the full `Equiv (□ (Path A x y))
  (Path (□ A) (boxIntro x) (boxIntro y))` is gated on the
  cross-mode modal Term ctors AND the cubical universe-path
  eliminator (not in this kernel slice).
* **General `Modality.box` parametrization**: the modality tag
  `Nat` carried by `Ty.modal` is opaque at Layer 1.  The
  rfl-fragment bridge does not consume the tag — it operates
  directly on the `RawTerm.modIntro` syntax wrapper around the
  `Cubical.constantPath` constructor.

## Why "rfl-fragment-only" is honest progress

The two canonical translations prove a structural property: the
project's box/path bridge functions are DEFINITIONALLY
identity-equivalent on their canonical inputs.  This is the
load-bearing sanity check for cross-theory coherence on the
closed reflexive fragment.  Extending to arbitrary inputs needs
both Phase 12.A.6+ modal infrastructure AND the deferred D2.5.1
cubical β cascade; until then, the scope-restriction is
contractually clear via the `_onConstantPath` suffix.

## Tracker

* #1391 D9.7: BoxCubical — **PARTIAL** here on
  rfl-fragment; full `Equiv` claim deferred behind both Phase
  12.A.6+ and D2.5.1 typed transport.

## Root status

* Layer: bridge
* Load-bearing for: Smoke/AuditPhase12A9D97BoxCubical
* Axiom budget: zero (verified via `#assert_no_axioms` in
  `Tools/AuditAll/AuditBridge.lean`)
-/

namespace LeanFX2
namespace Bridge

/-- Box-cubical rfl-fragment forward bridge.

Given a canonical constant-path inside `Term.modIntro` — that is,
a path-typed term whose raw is `RawTerm.modIntro (RawTerm.pathLam
pointRaw.weaken)` — produce the canonical constant-path on the
`RawTerm.modIntro`-wrapped endpoint:
`Cubical.constantPath modeIsUnivalent (Term.modIntro pointTerm)`
whose raw is `RawTerm.pathLam (RawTerm.modIntro pointRaw).weaken`.

The two terms inhabit different path types (different endpoints).
This is not the headline `Equiv` — it is the rfl-fragment shape
translation. -/
def boxCubicalRefl {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw)
    (_boxedPathWitness :
      Term context (Ty.path carrierType pointRaw pointRaw)
        (RawTerm.modIntro (RawTerm.pathLam pointRaw.weaken))) :
    Term context
        (Ty.path carrierType (RawTerm.modIntro pointRaw)
          (RawTerm.modIntro pointRaw))
        (RawTerm.pathLam (RawTerm.modIntro pointRaw).weaken) :=
  Cubical.constantPath modeIsUnivalent (Term.modIntro pointTerm)

/-- The box-cubical rfl forward bridge projects to the raw
pathLam-of-modIntro shape. -/
theorem boxCubicalRefl_toRaw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw)
    (boxedPathWitness :
      Term context (Ty.path carrierType pointRaw pointRaw)
        (RawTerm.modIntro (RawTerm.pathLam pointRaw.weaken))) :
    (boxCubicalRefl modeIsUnivalent pointTerm boxedPathWitness).toRaw =
      RawTerm.pathLam (RawTerm.modIntro pointRaw).weaken := rfl

/-- Specialization of `boxCubicalRefl` to the canonical
boxed-constant-path input. -/
theorem boxCubicalRefl_onCanonical
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw)
    (boxedPathWitness :
      Term context (Ty.path carrierType pointRaw pointRaw)
        (RawTerm.modIntro (RawTerm.pathLam pointRaw.weaken))) :
    boxCubicalRefl modeIsUnivalent pointTerm boxedPathWitness =
      Cubical.constantPath modeIsUnivalent (Term.modIntro pointTerm) := rfl

/-- Box-cubical rfl-fragment backward bridge.

Given a canonical constant-path on the `RawTerm.modIntro`-wrapped
endpoint — that is, `Cubical.constantPath modeIsUnivalent (Term.modIntro
pointTerm)` whose raw is `RawTerm.pathLam (RawTerm.modIntro pointRaw).weaken`
— produce the canonical boxed constant-path
`Term.modIntro (Cubical.constantPath modeIsUnivalent pointTerm)` whose raw is
`RawTerm.modIntro (RawTerm.pathLam pointRaw.weaken)`. -/
def cubicalBoxRefl {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw)
    (_pathWitness :
      Term context
        (Ty.path carrierType (RawTerm.modIntro pointRaw)
          (RawTerm.modIntro pointRaw))
        (RawTerm.pathLam (RawTerm.modIntro pointRaw).weaken)) :
    Term context (Ty.path carrierType pointRaw pointRaw)
      (RawTerm.modIntro (RawTerm.pathLam pointRaw.weaken)) :=
  Term.modIntro (Cubical.constantPath modeIsUnivalent pointTerm)

/-- The box-cubical rfl backward bridge projects to the raw
modIntro-of-pathLam shape. -/
theorem cubicalBoxRefl_toRaw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw)
    (pathWitness :
      Term context
        (Ty.path carrierType (RawTerm.modIntro pointRaw)
          (RawTerm.modIntro pointRaw))
        (RawTerm.pathLam (RawTerm.modIntro pointRaw).weaken)) :
    (cubicalBoxRefl modeIsUnivalent pointTerm pathWitness).toRaw =
      RawTerm.modIntro (RawTerm.pathLam pointRaw.weaken) := rfl

/-- Specialization of `cubicalBoxRefl` to the canonical
unboxed-constant-path input. -/
theorem cubicalBoxRefl_onCanonical
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw)
    (pathWitness :
      Term context
        (Ty.path carrierType (RawTerm.modIntro pointRaw)
          (RawTerm.modIntro pointRaw))
        (RawTerm.pathLam (RawTerm.modIntro pointRaw).weaken)) :
    cubicalBoxRefl modeIsUnivalent pointTerm pathWitness =
      Term.modIntro (Cubical.constantPath modeIsUnivalent pointTerm) := rfl

/-- Round-trip `LHS → RHS → LHS` is `Term.modIntro (constantPath ...)`
on the canonical boxed-constant-path input. -/
theorem boxCubicalRefl_roundTrip_onConstantPath
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw) :
    cubicalBoxRefl modeIsUnivalent pointTerm
      (boxCubicalRefl modeIsUnivalent pointTerm
        (Term.modIntro (Cubical.constantPath modeIsUnivalent pointTerm))) =
      Term.modIntro (Cubical.constantPath modeIsUnivalent pointTerm) := rfl

/-- Round-trip `RHS → LHS → RHS` is `constantPath` on `Term.modIntro
pointTerm` on the canonical unboxed-constant-path input. -/
theorem cubicalBoxRefl_roundTrip_onConstantPath
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw) :
    boxCubicalRefl modeIsUnivalent pointTerm
      (cubicalBoxRefl modeIsUnivalent pointTerm
        (Cubical.constantPath modeIsUnivalent (Term.modIntro pointTerm))) =
      Cubical.constantPath modeIsUnivalent (Term.modIntro pointTerm) := rfl

/-- Raw-shape smoke for the canonical `LHS → RHS → LHS` round trip. -/
theorem boxCubicalRefl_roundTrip_toRaw
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw) :
    (cubicalBoxRefl modeIsUnivalent pointTerm
      (boxCubicalRefl modeIsUnivalent pointTerm
        (Term.modIntro
          (Cubical.constantPath modeIsUnivalent pointTerm)))).toRaw =
      RawTerm.modIntro (RawTerm.pathLam pointRaw.weaken) := rfl

/-- Raw-shape smoke for the canonical `RHS → LHS → RHS` round trip. -/
theorem cubicalBoxRefl_roundTrip_toRaw
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw) :
    (boxCubicalRefl modeIsUnivalent pointTerm
      (cubicalBoxRefl modeIsUnivalent pointTerm
        (Cubical.constantPath modeIsUnivalent
          (Term.modIntro pointTerm)))).toRaw =
      RawTerm.pathLam (RawTerm.modIntro pointRaw).weaken := rfl

end Bridge
end LeanFX2
