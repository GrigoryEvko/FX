import FX1Poly.Core.CanonicalFormsCandidate
import FX1Poly.Core.StepInversion

namespace FX1Poly.Core

open StepStar

abbrev unitCell {scope : Nat} : RawTerm scope := .mkGen .gen_unit () .childNil

def isUnitValue {scope : Nat} (term : RawTerm scope) : Prop :=
  term = unitCell

theorem isUnitValue_impliesStepNormalForm {scope : Nat} {value : RawTerm scope}
    (valueIsUnit : isUnitValue value) : RawTerm.isStepNormalForm value := by
  rw [valueIsUnit]; rfl

theorem unitCanonicalFormsCandidate {scope : Nat} :
    IsReducibilityCandidate (CanonicalFormsPredicate (scope := scope) isUnitValue) :=
  CanonicalFormsPredicate.isReducibilityCandidateOfValuesNormal isUnitValue_impliesStepNormalForm

theorem unitCell_isMember {scope : Nat} :
    CanonicalFormsPredicate (scope := scope) isUnitValue unitCell :=
  ⟨Acc.intro unitCell
      (fun _reduct stepFromUnit => absurd stepFromUnit Step.no_step_from_unit),
    Or.inr ⟨unitCell, StepStar.refl unitCell, rfl⟩⟩

theorem unitClosedReducesToValue {term : RawTerm 0}
    (member : CanonicalFormsPredicate isUnitValue term) :
    ∃ value : RawTerm 0, StepStar term value ∧ isUnitValue value :=
  CanonicalFormsPredicate.closedReducesToValue member

theorem unitClosedReducesToUnitCell {term : RawTerm 0}
    (member : CanonicalFormsPredicate isUnitValue term) :
    StepStar term unitCell := by
  obtain ⟨value, reducesToValue, valueIsUnit⟩ := unitClosedReducesToValue member
  rw [valueIsUnit] at reducesToValue
  exact reducesToValue

end FX1Poly.Core

#print axioms FX1Poly.Core.unitCanonicalFormsCandidate
#print axioms FX1Poly.Core.unitCell_isMember
#print axioms FX1Poly.Core.unitClosedReducesToUnitCell
