import FX1Poly.Typed.ClosedBoolCanonicity
import FX1Poly.Typed.ConsistencyTargetSignature

/-! Probe: bundle the three now-unconditional Milestone-A value-layer pillars (SN + consistency +
    value-layer canonicity) into one honest capstone record over the grown typed kernel. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

structure MilestoneAValueLayerSpine (profile : PolyProfile) : Prop where
  stronglyNormalizing : ∀ {subject classifier : RawTerm 0},
    HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject classifier →
      StepStar.IsStronglyNormalizing subject
  consistency : ∀ {subject : RawTerm 0},
    HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject emptyTypeCell → False
  boolCanonicity : ∀ {subject : RawTerm 0},
    (HasTypeDescDataIntro profile (TypingContext.empty : TypingContext profile 0) subject boolTypeCell ∨
     HasTypeDescBaseType profile (TypingContext.empty : TypingContext profile 0) subject boolTypeCell ∨
     HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject boolTypeCell) →
      ∃ value : RawTerm 0, StepStar subject value ∧ (value = boolTrueCell ∨ value = boolFalseCell)

theorem milestoneAValueLayerSpineHolds {profile : PolyProfile} :
    MilestoneAValueLayerSpine profile where
  stronglyNormalizing typed :=
    HasTypeDescPi.stronglyNormalizingOfWfContextDesc WfContextDesc.emptyIsWellFormed typed
  consistency typed := emptyConsistencyViaCandidateBridge _ typed
  boolCanonicity typed := closedBoolCanonicalForms typed

#print axioms milestoneAValueLayerSpineHolds

end FX1Poly.Typed
