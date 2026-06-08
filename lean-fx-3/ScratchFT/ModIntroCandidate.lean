import FX1Poly.Core.CanonicalFormsCandidate
import FX1Poly.Core.StepInversion

namespace FX1Poly.Core

open StepStar

abbrev modIntroCell {scope : Nat} (payload : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_modIntro () (.childCons payload .childNil)

def isModIntroValue {scope : Nat} (term : RawTerm scope) : Prop :=
  ∃ payload : RawTerm scope, term = modIntroCell payload ∧ RawTerm.isStepNormalForm payload

theorem isModIntroValue_impliesStepNormalForm {scope : Nat} {value : RawTerm scope}
    (valueIsModIntro : isModIntroValue value) : RawTerm.isStepNormalForm value := by
  obtain ⟨payload, valueEq, payloadNormal⟩ := valueIsModIntro
  subst valueEq
  show (RawTerm.isStepNormalFormBool payload && true) = true
  rw [Bool.and_true]
  exact payloadNormal

theorem modIntroCanonicalFormsCandidate {scope : Nat} :
    IsReducibilityCandidate (CanonicalFormsPredicate (scope := scope) isModIntroValue) :=
  CanonicalFormsPredicate.isReducibilityCandidateOfValuesNormal isModIntroValue_impliesStepNormalForm

theorem modIntroValue_isMember {scope : Nat} {payload : RawTerm scope}
    (payloadNormal : RawTerm.isStepNormalForm payload) :
    CanonicalFormsPredicate isModIntroValue (modIntroCell payload) :=
  CanonicalFormsPredicate.memberOfValue
    (isModIntroValue_impliesStepNormalForm ⟨payload, rfl, payloadNormal⟩)
    ⟨payload, rfl, payloadNormal⟩

theorem modIntroClosedReducesToValue {term : RawTerm 0}
    (member : CanonicalFormsPredicate isModIntroValue term) :
    ∃ value : RawTerm 0, StepStar term value ∧ isModIntroValue value :=
  CanonicalFormsPredicate.closedReducesToValue member

end FX1Poly.Core

#print axioms FX1Poly.Core.modIntroCanonicalFormsCandidate
#print axioms FX1Poly.Core.modIntroValue_isMember
#print axioms FX1Poly.Core.modIntroClosedReducesToValue
