import LeanFX2.Translation.Inverse

/-! # InternalLanguage/Coherence

Cross-theory coherence.

## Deliverable

This module records the coherence facts currently justified by the implemented
translation fragments.

The present slice is intentionally small: it checks the type-level coherence
diamond on the `Unit` carrier for observational identity and cubical path
types.  Full term-level coherence and preservation are blocked on the later
explicit typing judgment.
-/

namespace LeanFX2
namespace InternalLanguage

/-- Type-level cubical/observational coherence on the supported `Unit`
carrier fragment. -/
theorem unitEqualityTranslationCoherence {level scope : Nat}
    (leftEndpoint rightEndpoint : RawTerm scope) :
    And
      (Translation.cubicalToObservationalTy
        (Translation.observationalToCubicalTy
          (Ty.id (Ty.unit (level := level) (scope := scope))
            leftEndpoint rightEndpoint)) =
          Ty.id Ty.unit leftEndpoint rightEndpoint)
      (Translation.observationalToCubicalTy
        (Translation.cubicalToObservationalTy
          (Ty.path (Ty.unit (level := level) (scope := scope))
            leftEndpoint rightEndpoint)) =
          Ty.path Ty.unit leftEndpoint rightEndpoint) :=
  And.intro
    (Translation.observationalCubicalRoundTripTy_id
      Ty.unit leftEndpoint rightEndpoint
      Translation.observationalCubicalRoundTripTy_unit)
    (Translation.cubicalObservationalRoundTripTy_path
      Ty.unit leftEndpoint rightEndpoint
      Translation.cubicalObservationalRoundTripTy_unit)

end InternalLanguage
end LeanFX2
