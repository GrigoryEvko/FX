import LeanFX2.Bridge.BoxObservational

/-! # Bridge/BoxObservationalInverse — RFL-FRAGMENT ONLY

⚠️  SCOPE ADVISORY: every theorem in this file is restricted to
the **canonical reflexive-fragment input** — `Term.modIntro
(Term.refl A x)` for the LHS direction and `Term.refl A
(RawTerm.modIntro x)` for the RHS direction.  Theorem names carry
explicit `_onRefl` / `_toRaw` suffixes to mark the scope.  The
general claim "any boxed identity round-trips through any
modIntro-endpoint identity" is NOT shipped here.

## What ships (4 thin re-exports + 4 raw smokes)

This module reorganises the round-trip identities already proved
inline in `Bridge/BoxObservational.lean` under the same naming
convention `Bridge/PathIdInverse.lean` uses for the
PathToId/IdToPath inverses.  Each declaration is a thin wrapper
around the corresponding `Bridge.*_roundTrip_*` theorem so the
inverse file is the canonical place to look up
"is this bridge actually invertible?".

| Theorem | Restricted to |
|---------|---------------|
| `boxObservational_roundTrip_onCanonical` | `LHS → RHS → LHS` only on `Term.modIntro (Term.refl ...)` |
| `observationalBox_roundTrip_onCanonical` | `RHS → LHS → RHS` only on `Term.refl ... (RawTerm.modIntro ...)` |
| `boxObservational_roundTrip_toRaw` | raw-shape smoke for the LHS round trip |
| `observationalBox_roundTrip_toRaw` | raw-shape smoke for the RHS round trip |

## What does NOT ship

* **Arbitrary boxed-id round-trip**: for `idWitness` constructed via
  `idJ` or transport (i.e. not in canonical refl-shape), no
  round-trip inverse is shipped.
* **Set-level Equiv**: the headline `Equiv (□ (Ty.id A x y))
  (Ty.id (□ A) (boxIntro x) (boxIntro y))` is gated on Phase
  12.A.6+ infrastructure (typed `Term.boxIntro` /
  `Term.boxElim` ctors).  Until those land, the `Equiv` is
  expressible only at the rfl-fragment shape pair shown above.

## Why "rfl-fragment-only" is honest progress

The four canonical theorems prove a structural property: the
project's box/id bridge functions are DEFINITIONALLY identity-
equivalent on their canonical inputs.  This is the load-bearing
sanity check for the bridge's correctness on the closed reflexive
fragment.  Extending to arbitrary inputs requires Phase 12.A.6+
infrastructure; until then, the scope-restriction is contractually
clear via the suffixes and this advisory.

## Tracker

* #1390 D9.6: BoxObservational round-trip — **PARTIAL** here on
  rfl-fragment; full claim deferred behind Phase 12.A.6+.

## Root status

* Layer: bridge
* Load-bearing for: Smoke/AuditPhase12A9D96BoxObservational
* Axiom budget: zero (verified via `#assert_no_axioms` in
  `Tools/AuditAll/AuditBridge.lean`)
-/

namespace LeanFX2
namespace Bridge

/-- `LHS → RHS → LHS` is `Term.modIntro (Term.refl A x)` on the
canonical boxed-refl input. -/
theorem boxObservational_roundTrip_onCanonical
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw) :
    observationalBoxRefl pointTerm
      (boxObservationalRefl pointTerm
        (Term.modIntro (Term.refl carrierType pointRaw))) =
      Term.modIntro (Term.refl carrierType pointRaw) :=
  boxObservationalRefl_roundTrip_onRefl pointTerm

/-- `RHS → LHS → RHS` is `Term.refl A (RawTerm.modIntro x)` on the
canonical unboxed-refl input. -/
theorem observationalBox_roundTrip_onCanonical
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw) :
    boxObservationalRefl pointTerm
      (observationalBoxRefl pointTerm
        (Term.refl carrierType (RawTerm.modIntro pointRaw))) =
      Term.refl carrierType (RawTerm.modIntro pointRaw) :=
  observationalBoxRefl_roundTrip_onRefl pointTerm

/-- Raw-shape smoke for the canonical `LHS → RHS → LHS` round trip. -/
theorem boxObservational_roundTrip_toRaw
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw) :
    (observationalBoxRefl pointTerm
      (boxObservationalRefl pointTerm
        (Term.modIntro (Term.refl carrierType pointRaw)))).toRaw =
      RawTerm.modIntro (RawTerm.refl pointRaw) :=
  boxObservationalRefl_roundTrip_toRaw pointTerm

/-- Raw-shape smoke for the canonical `RHS → LHS → RHS` round trip. -/
theorem observationalBox_roundTrip_toRaw
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw) :
    (boxObservationalRefl pointTerm
      (observationalBoxRefl pointTerm
        (Term.refl carrierType (RawTerm.modIntro pointRaw)))).toRaw =
      RawTerm.refl (RawTerm.modIntro pointRaw) :=
  observationalBoxRefl_roundTrip_toRaw pointTerm

end Bridge
end LeanFX2
