import FX1Poly.Typed.GrownTypeSafety
import FX1Poly.Typed.GrownOpenTypeSafety
import FX1Poly.Typed.HasTypeDescPiSubjectReductionUnconditional
import FX1Poly.Typed.WfContextDescPiFromWfContextDesc

/-! Probe: discharge the subjectReductionStar hypothesis of the grown type-safety theorems via the unconditional
    SR-U4 (HasTypeDescPi.subjectReductionStar), making CLOSED (#1134) + OPEN (#1135) grown type safety
    unconditional. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

theorem HasTypeDescPi.closedTypeSafetyProbe {profile : PolyProfile} {subject classifier : RawTerm 0}
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject classifier) :
    ∃ value : RawTerm 0,
      StepStar subject value ∧ RawTerm.isStepNormalForm value ∧ RawTerm.IsGrownCanonicalHead value :=
  HasTypeDescPi.closedTypeSafetyOfSubjectReductionStar
    (fun typedStart steps =>
      HasTypeDescPi.subjectReductionStar WfContextDescPi.emptyIsWellFormed typedStart steps)
    typed

theorem HasTypeDescPi.closedTypeSafetyUniqueProbe {profile : PolyProfile} {subject classifier : RawTerm 0}
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject classifier) :
    ∃ value : RawTerm 0,
      (StepStar subject value ∧ RawTerm.isStepNormalForm value ∧ RawTerm.IsGrownCanonicalHead value) ∧
      ∀ otherForm : RawTerm 0,
        StepStar subject otherForm → RawTerm.isStepNormalForm otherForm → otherForm = value :=
  HasTypeDescPi.closedTypeSafetyUniqueOfSubjectReductionStar
    (fun typedStart steps =>
      HasTypeDescPi.subjectReductionStar WfContextDescPi.emptyIsWellFormed typedStart steps)
    typed

theorem HasTypeDescPi.openTypeSafetyProbe {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context subject classifier)
    (wellFormed : WfContextDesc context) :
    ∃ value : RawTerm scope,
      StepStar subject value ∧ RawTerm.isStepNormalForm value ∧
      (RawTerm.IsGrownCanonicalHead value ∨ IsNeutral value) :=
  HasTypeDescPi.openTypeSafetyOfSubjectReductionStar
    (fun typedStart steps =>
      HasTypeDescPi.subjectReductionStar (WfContextDescPi.ofWfContextDesc wellFormed) typedStart steps)
    typed wellFormed

theorem HasTypeDescPi.openTypeSafetyUniqueProbe {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context subject classifier)
    (wellFormed : WfContextDesc context) :
    ∃ value : RawTerm scope,
      (StepStar subject value ∧ RawTerm.isStepNormalForm value ∧
        (RawTerm.IsGrownCanonicalHead value ∨ IsNeutral value)) ∧
      ∀ otherForm : RawTerm scope,
        StepStar subject otherForm → RawTerm.isStepNormalForm otherForm → otherForm = value :=
  HasTypeDescPi.openTypeSafetyUniqueOfSubjectReductionStar
    (fun typedStart steps =>
      HasTypeDescPi.subjectReductionStar (WfContextDescPi.ofWfContextDesc wellFormed) typedStart steps)
    typed wellFormed

end FX1Poly.Typed

#print axioms FX1Poly.Typed.HasTypeDescPi.closedTypeSafetyProbe
#print axioms FX1Poly.Typed.HasTypeDescPi.closedTypeSafetyUniqueProbe
#print axioms FX1Poly.Typed.HasTypeDescPi.openTypeSafetyProbe
#print axioms FX1Poly.Typed.HasTypeDescPi.openTypeSafetyUniqueProbe
