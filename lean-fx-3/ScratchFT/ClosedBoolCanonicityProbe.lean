import FX1Poly.Typed.CombinedBoolCanonicalForms
import FX1Poly.Typed.HasTypeDescPiSubjectReductionUnconditional
import FX1Poly.Typed.ConsistencyConditionalOnSubjectReduction

/-! Probe: closed bool canonicity via the SYNTACTIC route (SN + SR-U4 + closed-normal), the bool twin of
    consistency. Mirrors `consistencyOfSubjectReductionStarToEmptyType` with the subjectReductionStar
    hypothesis discharged by the unconditional SR-U4 `HasTypeDescPi.subjectReductionStar`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

theorem HasTypeDescPi.noClosedGrownTermAtBoolTypeProbe {profile : PolyProfile} {subject : RawTerm 0}
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
      (boolTypeCell : RawTerm 0)) :
    False := by
  have terminates :=
    HasTypeDescPi.stronglyNormalizingOfWfContextDesc WfContextDesc.emptyIsWellFormed typed
  obtain ⟨normalForm, reachesNormalForm, normalFormIsNormal⟩ :=
    exists_normalForm_of_isStronglyNormalizing terminates
  exact HasTypeDescPi.noClosedNormalTermAtBoolType
    (HasTypeDescPi.subjectReductionStar WfContextDescPi.emptyIsWellFormed typed reachesNormalForm)
    normalFormIsNormal

theorem closedBoolCanonicalFormsProbe {profile : PolyProfile} {subject : RawTerm 0}
    (typed :
      HasTypeDescDataIntro profile (TypingContext.empty : TypingContext profile 0) subject boolTypeCell ∨
      HasTypeDescBaseType profile (TypingContext.empty : TypingContext profile 0) subject boolTypeCell ∨
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject boolTypeCell) :
    ∃ value : RawTerm 0, StepStar subject value ∧
      (value = boolTrueCell ∨ value = boolFalseCell) := by
  rcases typed with dataIntroTyped | baseTypeTyped | grownTyped
  · rcases standaloneBoolCanonicalForms (Or.inl dataIntroTyped) with valueEq | valueEq
    · subst valueEq; exact ⟨_, StepStar.refl _, Or.inl rfl⟩
    · subst valueEq; exact ⟨_, StepStar.refl _, Or.inr rfl⟩
  · rcases standaloneBoolCanonicalForms (Or.inr baseTypeTyped) with valueEq | valueEq
    · subst valueEq; exact ⟨_, StepStar.refl _, Or.inl rfl⟩
    · subst valueEq; exact ⟨_, StepStar.refl _, Or.inr rfl⟩
  · exact (HasTypeDescPi.noClosedGrownTermAtBoolTypeProbe grownTyped).elim

end FX1Poly.Typed

#print axioms FX1Poly.Typed.HasTypeDescPi.noClosedGrownTermAtBoolTypeProbe
#print axioms FX1Poly.Typed.closedBoolCanonicalFormsProbe
