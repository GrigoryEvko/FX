import LeanFX2.Translation.CubicalToObservational
import LeanFX2.Translation.ObservationalToCubical

/-! # Translation/Inverse

Type-level inverse laws between translation functors.

## Deliverable

This file proves the inverse laws currently justified by the implemented
translation fragments.

The laws are deliberately local.  Cubical-to-observational collapses interval
and Glue types, while observational-to-cubical collapses observational equality
constructors to Path.  Because those choices are lossy on the full `Ty`
language, this file proves round trips for equality/path constructors under an
explicit carrier round-trip hypothesis instead of claiming a global inverse
theorem.
-/

namespace LeanFX2
namespace Translation

/-- `Unit` is fixed by observational-to-cubical followed by
cubical-to-observational. -/
theorem observationalCubicalRoundTripTy_unit {level scope : Nat} :
    cubicalToObservationalTy
      (observationalToCubicalTy (level := level) (scope := scope) Ty.unit) =
        Ty.unit := rfl

/-- `Bool` is fixed by observational-to-cubical followed by
cubical-to-observational. -/
theorem observationalCubicalRoundTripTy_bool {level scope : Nat} :
    cubicalToObservationalTy
      (observationalToCubicalTy (level := level) (scope := scope) Ty.bool) =
        Ty.bool := rfl

/-- `Nat` is fixed by observational-to-cubical followed by
cubical-to-observational. -/
theorem observationalCubicalRoundTripTy_nat {level scope : Nat} :
    cubicalToObservationalTy
      (observationalToCubicalTy (level := level) (scope := scope) Ty.nat) =
        Ty.nat := rfl

/-- `Unit` is fixed by cubical-to-observational followed by
observational-to-cubical. -/
theorem cubicalObservationalRoundTripTy_unit {level scope : Nat} :
    observationalToCubicalTy
      (cubicalToObservationalTy (level := level) (scope := scope) Ty.unit) =
        Ty.unit := rfl

/-- `Bool` is fixed by cubical-to-observational followed by
observational-to-cubical. -/
theorem cubicalObservationalRoundTripTy_bool {level scope : Nat} :
    observationalToCubicalTy
      (cubicalToObservationalTy (level := level) (scope := scope) Ty.bool) =
        Ty.bool := rfl

/-- `Nat` is fixed by cubical-to-observational followed by
observational-to-cubical. -/
theorem cubicalObservationalRoundTripTy_nat {level scope : Nat} :
    observationalToCubicalTy
      (cubicalToObservationalTy (level := level) (scope := scope) Ty.nat) =
        Ty.nat := rfl

/-- Observational identity round-trips through the cubical translation when
its carrier type already round-trips. -/
theorem observationalCubicalRoundTripTy_id {level scope : Nat}
    (carrier : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope)
    (carrierRoundTrip :
      cubicalToObservationalTy (observationalToCubicalTy carrier) = carrier) :
    cubicalToObservationalTy
      (observationalToCubicalTy
        (Ty.id carrier leftEndpoint rightEndpoint)) =
        Ty.id carrier leftEndpoint rightEndpoint := by
  simp only [observationalToCubicalTy, cubicalToObservationalTy]
  rw [carrierRoundTrip]

/-- Cubical paths round-trip through the observational translation when their
carrier type already round-trips. -/
theorem cubicalObservationalRoundTripTy_path {level scope : Nat}
    (carrier : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope)
    (carrierRoundTrip :
      observationalToCubicalTy (cubicalToObservationalTy carrier) = carrier) :
    observationalToCubicalTy
      (cubicalToObservationalTy
        (Ty.path carrier leftEndpoint rightEndpoint)) =
        Ty.path carrier leftEndpoint rightEndpoint := by
  simp only [cubicalToObservationalTy, observationalToCubicalTy]
  rw [carrierRoundTrip]

end Translation
end LeanFX2
