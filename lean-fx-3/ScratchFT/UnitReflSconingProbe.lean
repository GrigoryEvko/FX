import FX1Poly.Core.DataCanonicityViaSconing
import FX1Poly.Core.UnitCanonicalFormsCandidate
import FX1Poly.Core.ReflCanonicalFormsCandidate

/-! Scratch probe: complete the data-canonicity-via-sconing coverage with Unit + identity(refl) —
    the last two data types (SN-049 lists Unit; SN-059/067 identity), thin one-line specializations
    of the generic dataCanonicityViaSconing at isUnitValue / isReflValue. Extraction is #672-free, so
    these are conditional only on the per-type fundamental, NOT on typed SN. -/

namespace FX1Poly.Core

open FX1Poly.Foundation

theorem unitCanonicityViaSconing {isWellTyped : RawTerm 0 → Prop}
    (fundamental : ∀ term : RawTerm 0,
      isWellTyped term → CanonicalFormsPredicate isUnitValue term)
    (term : RawTerm 0) (typed : isWellTyped term) :
    ∃ value : RawTerm 0, StepStar term value ∧ isUnitValue value :=
  dataCanonicityViaSconing fundamental term typed

theorem identityCanonicityViaSconing {isWellTyped : RawTerm 0 → Prop}
    (fundamental : ∀ term : RawTerm 0,
      isWellTyped term → CanonicalFormsPredicate isReflValue term)
    (term : RawTerm 0) (typed : isWellTyped term) :
    ∃ value : RawTerm 0, StepStar term value ∧ isReflValue value :=
  dataCanonicityViaSconing fundamental term typed

#print axioms unitCanonicityViaSconing
#print axioms identityCanonicityViaSconing

end FX1Poly.Core
