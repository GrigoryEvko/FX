import FX1Poly.Typed.GrownCanonicalForms
import FX1Poly.Typed.OpenStronglyNormalizingUnconditional
import FX1Poly.Core.WeakNormalization

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe
open StepStar

-- Conditional SN-050 consistency: isolate the EXACT remaining gate as `subjectReductionStar`.
-- SN (OB-5) reaches a normal form; SR carries the EmptyType classifier along the chain; the grown
-- normal-form consistency (noClosedNormalTermAtEmptyType) refutes the normal endpoint.
theorem HasTypeDescPi.consistencyOfSubjectReductionStarToEmptyType {profile : PolyProfile}
    {subject : RawTerm 0}
    (subjectReductionStar : ∀ {start finish : RawTerm 0},
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) start
        (emptyTypeCell (scope := 0)) →
      StepStar start finish →
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) finish
        (emptyTypeCell (scope := 0)))
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
      (emptyTypeCell (scope := 0))) :
    False := by
  have terminates : IsStronglyNormalizing subject :=
    HasTypeDescPi.stronglyNormalizingOfWfContext WfContext.emptyIsWellFormed typed
  obtain ⟨normalForm, reachesNormalForm, normalFormIsNormal⟩ :=
    exists_normalForm_of_isStronglyNormalizing terminates
  exact HasTypeDescPi.noClosedNormalTermAtEmptyType
    (subjectReductionStar typed reachesNormalForm) normalFormIsNormal

#print axioms HasTypeDescPi.consistencyOfSubjectReductionStarToEmptyType

end FX1Poly.Typed
