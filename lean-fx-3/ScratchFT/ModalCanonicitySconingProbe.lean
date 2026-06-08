import FX1Poly.Core.DataCanonicityViaSconing
import FX1Poly.Core.ModIntroCanonicalFormsCandidate

/-! Scratch probe: modal box canonicity via sconing — the modal-box former joining the generic sconing
    witness, completing canonicity-via-sconing coverage to ALL formers with a candidate (data + modal box).
    #672-free; conditional only on the per-type fundamental. SN-073 (modIntro). -/

namespace FX1Poly.Core

open FX1Poly.Foundation

theorem modIntroCanonicityViaSconing {isWellTyped : RawTerm 0 → Prop}
    (fundamental : ∀ term : RawTerm 0,
      isWellTyped term → CanonicalFormsPredicate isModIntroValue term)
    (term : RawTerm 0) (typed : isWellTyped term) :
    ∃ value : RawTerm 0, StepStar term value ∧ isModIntroValue value :=
  dataCanonicityViaSconing fundamental term typed

#print axioms modIntroCanonicityViaSconing

end FX1Poly.Core
