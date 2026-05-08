import LeanFX2.Term
import LeanFX2.Term.ToRaw

/-! # Bridge/BoxObservational

Box commutes with observational identity at the rfl-fragment.

## Deliverable

This module ships the canonical reflexive fragment of the
"`□` commutes with `Ty.id`" coherence statement.

The full theorem
```
□ (Ty.id A x y)  ≃  Ty.id (□ A) (boxIntro x) (boxIntro y)
```
needs Phase 12.A.6+ infrastructure (typed `Ty.modal`-bearing
`Term.boxIntro` / `Term.boxElim` ctors plus the cross-mode
`Modality.box` 1-cell).  The Layer-1 `Term.modIntro` ctor that
ships today preserves `innerType` rather than promoting it to
`Ty.modal modalityTag innerType`, so the headline `Equiv` between
typed boxed-id and id-of-boxed-endpoint terms is not yet
expressible.

What IS shippable today is the **rfl-fragment** translation: a
canonical refl-witness inside `Term.modIntro` corresponds to a
canonical refl-witness on the `RawTerm.modIntro`-wrapped endpoint.
The bridge maps the two refl-shapes, projects to raw via `rfl`,
and round-trips both ways via `rfl`.

This mirrors the design of `Bridge/PathToId.lean` /
`Bridge/IdToPath.lean` (rfl-fragment only, with explicit
`_onCanonical` / `_onRefl` suffixes marking the scope) and
`Bridge/PathIdInverse.lean` (round-trip on the reflexive input).

## What ships (4 declarations)

| Name | Direction | Shape |
|------|-----------|-------|
| `boxObservationalRefl` | LHS → RHS | `Term.modIntro (Term.refl A x) ↦ Term.refl A (RawTerm.modIntro x)` |
| `boxObservationalRefl_toRaw` | raw projection | `(boxObservationalRefl _).toRaw = RawTerm.refl (RawTerm.modIntro x)` |
| `observationalBoxRefl` | RHS → LHS | `Term.refl A (RawTerm.modIntro x) ↦ Term.modIntro (Term.refl A x)` |
| `observationalBoxRefl_toRaw` | raw projection | `(observationalBoxRefl _).toRaw = RawTerm.modIntro (RawTerm.refl x)` |
| `boxObservationalRefl_roundTrip_onRefl` | LHS → RHS → LHS = id | `rfl` |
| `observationalBoxRefl_roundTrip_onRefl` | RHS → LHS → RHS = id | `rfl` |

## What does NOT ship

* **Arbitrary boxed-id translation**: for `idWitness` constructed via
  `idJ` or transport (i.e. not in canonical refl-shape), no bridge
  is shipped.  This requires the typed identity eliminator
  promoting through modalities, which depends on Phase 12.A.6+
  infrastructure.
* **Headline `Equiv`**: the full `Equiv (□ (Ty.id A x y))
  (Ty.id (□ A) (boxIntro x) (boxIntro y))` is gated on the
  cross-mode modal Term ctors (`Term.boxIntro` /
  `Term.boxElim` producing `Ty.modal Modality.box`-typed values).
  Tracker: see `Modal/Adjunction.lean` for the Phase 12.A.6+
  prerequisite catalogue and `Modal/BoxPath.lean` for the parallel
  observational-side blocker.
* **General `Modality.box` parametrization**: the modality tag
  `Nat` carried by `Ty.modal` is opaque at Layer 1.  The
  rfl-fragment bridge does not consume the tag — it operates
  directly on the `RawTerm.modIntro` syntax wrapper.

## Why "rfl-fragment-only" is honest progress

The two canonical translations prove a structural property: the
project's box/id bridge functions are DEFINITIONALLY
identity-equivalent on their canonical inputs.  This is the
load-bearing sanity check for cross-theory coherence on the
closed reflexive fragment.  Extending to arbitrary inputs needs
Phase 12.A.6+ infrastructure; until then, the scope-restriction
is contractually clear via the `_onRefl` suffix.

## Tracker

* #1390 D9.6: BoxObservational — **PARTIAL** here on
  rfl-fragment; full `Equiv` claim deferred behind Phase 12.A.6+.

## Root status

* Layer: bridge
* Load-bearing for: Smoke/AuditPhase12A9D96BoxObservational
* Axiom budget: zero (verified via `#assert_no_axioms` in
  `Tools/AuditAll/AuditBridge.lean`)
-/

namespace LeanFX2
namespace Bridge

/-- Box-observational rfl-fragment forward bridge.

Given a canonical refl witness inside `Term.modIntro` — that is,
`Term.modIntro (Term.refl A x)` whose typed indices are
`(Ty.id A x x, RawTerm.modIntro (RawTerm.refl x))` — produce the
canonical refl witness on the `RawTerm.modIntro`-wrapped endpoint:
`Term.refl A (RawTerm.modIntro x)` whose typed indices are
`(Ty.id A (RawTerm.modIntro x) (RawTerm.modIntro x),
RawTerm.refl (RawTerm.modIntro x))`.

The two terms inhabit different identity types (different
endpoints).  This is not the headline `Equiv` — it is the
rfl-fragment shape translation. -/
def boxObservationalRefl {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (_pointTerm : Term context carrierType pointRaw)
    (_boxedIdWitness :
      Term context (Ty.id carrierType pointRaw pointRaw)
        (RawTerm.modIntro (RawTerm.refl pointRaw))) :
    Term context
        (Ty.id carrierType (RawTerm.modIntro pointRaw)
          (RawTerm.modIntro pointRaw))
        (RawTerm.refl (RawTerm.modIntro pointRaw)) :=
  Term.refl carrierType (RawTerm.modIntro pointRaw)

/-- The box-observational rfl forward bridge projects to the raw
refl-of-modIntro shape. -/
theorem boxObservationalRefl_toRaw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw)
    (boxedIdWitness :
      Term context (Ty.id carrierType pointRaw pointRaw)
        (RawTerm.modIntro (RawTerm.refl pointRaw))) :
    (boxObservationalRefl pointTerm boxedIdWitness).toRaw =
      RawTerm.refl (RawTerm.modIntro pointRaw) := rfl

/-- Specialization of `boxObservationalRefl` to the canonical
boxed-refl input `Term.modIntro (Term.refl carrierType pointRaw)`. -/
theorem boxObservationalRefl_onCanonical
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw) :
    boxObservationalRefl pointTerm
        (Term.modIntro (Term.refl carrierType pointRaw)) =
      Term.refl carrierType (RawTerm.modIntro pointRaw) := rfl

/-- Box-observational rfl-fragment backward bridge.

Given a canonical refl witness on the `RawTerm.modIntro`-wrapped
endpoint — that is, `Term.refl A (RawTerm.modIntro x)` whose
typed indices are
`(Ty.id A (RawTerm.modIntro x) (RawTerm.modIntro x),
RawTerm.refl (RawTerm.modIntro x))` — produce the canonical
boxed refl witness `Term.modIntro (Term.refl A x)` whose typed
indices are `(Ty.id A x x, RawTerm.modIntro (RawTerm.refl x))`.

The endpoint term `pointTerm` is taken explicitly because the
underlying `Term.refl` ctor stores only the raw witness.  Its
typed counterpart is the data we use to build `Term.refl
carrierType pointRaw` on the LHS shape. -/
def observationalBoxRefl {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (_pointTerm : Term context carrierType pointRaw)
    (_idWitness :
      Term context
        (Ty.id carrierType (RawTerm.modIntro pointRaw)
          (RawTerm.modIntro pointRaw))
        (RawTerm.refl (RawTerm.modIntro pointRaw))) :
    Term context (Ty.id carrierType pointRaw pointRaw)
      (RawTerm.modIntro (RawTerm.refl pointRaw)) :=
  Term.modIntro (Term.refl carrierType pointRaw)

/-- The box-observational rfl backward bridge projects to the raw
modIntro-of-refl shape. -/
theorem observationalBoxRefl_toRaw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw)
    (idWitness :
      Term context
        (Ty.id carrierType (RawTerm.modIntro pointRaw)
          (RawTerm.modIntro pointRaw))
        (RawTerm.refl (RawTerm.modIntro pointRaw))) :
    (observationalBoxRefl pointTerm idWitness).toRaw =
      RawTerm.modIntro (RawTerm.refl pointRaw) := rfl

/-- Specialization of `observationalBoxRefl` to the canonical
unboxed-refl input `Term.refl carrierType (RawTerm.modIntro pointRaw)`. -/
theorem observationalBoxRefl_onCanonical
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw) :
    observationalBoxRefl pointTerm
        (Term.refl carrierType (RawTerm.modIntro pointRaw)) =
      Term.modIntro (Term.refl carrierType pointRaw) := rfl

/-- Round-trip `LHS → RHS → LHS` is `Term.modIntro (Term.refl ...)`
on the canonical boxed-refl input. -/
theorem boxObservationalRefl_roundTrip_onRefl
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw) :
    observationalBoxRefl pointTerm
      (boxObservationalRefl pointTerm
        (Term.modIntro (Term.refl carrierType pointRaw))) =
      Term.modIntro (Term.refl carrierType pointRaw) := rfl

/-- Round-trip `RHS → LHS → RHS` is `Term.refl ... (RawTerm.modIntro
pointRaw)` on the canonical unboxed-refl input. -/
theorem observationalBoxRefl_roundTrip_onRefl
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw) :
    boxObservationalRefl pointTerm
      (observationalBoxRefl pointTerm
        (Term.refl carrierType (RawTerm.modIntro pointRaw))) =
      Term.refl carrierType (RawTerm.modIntro pointRaw) := rfl

/-- Raw-shape smoke for the canonical `LHS → RHS → LHS` round trip. -/
theorem boxObservationalRefl_roundTrip_toRaw
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw) :
    (observationalBoxRefl pointTerm
      (boxObservationalRefl pointTerm
        (Term.modIntro (Term.refl carrierType pointRaw)))).toRaw =
      RawTerm.modIntro (RawTerm.refl pointRaw) := rfl

/-- Raw-shape smoke for the canonical `RHS → LHS → RHS` round trip. -/
theorem observationalBoxRefl_roundTrip_toRaw
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw) :
    (boxObservationalRefl pointTerm
      (observationalBoxRefl pointTerm
        (Term.refl carrierType (RawTerm.modIntro pointRaw)))).toRaw =
      RawTerm.refl (RawTerm.modIntro pointRaw) := rfl

end Bridge
end LeanFX2
