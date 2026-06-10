import FX1Poly.Typed.ClosedBoolCanonicity
import FX1Poly.Typed.GrownClosedNormalClassifierShape
import FX1Poly.Typed.HasTypeDescPiSubjectReductionUnconditional
import FX1Poly.Typed.OpenStronglyNormalizingUnconditional
import FX1Poly.Core.WeakNormalization
import FX1Poly.Typed.ConvBoolCodeRigidity
import FX1Poly.Typed.OptionCanonicalForms

/-! Probe: the GENERIC arbitrary-subject grown vacuity + generic canonicity packaging, generalizing last
    firing's bool-specific noClosedGrownTermAtBoolType / closedBoolCanonicalForms to ANY data classifier. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- Generic arbitrary-subject grown vacuity: a classifier Conv neither a Π-code nor a universe code has no
closed grown inhabitant (any subject, not just normal). SN reaches a NF, SR-U4 preserves the classifier,
noClosedNormalTermAtDataClassifier (#1065) settles it. -/
theorem HasTypeDescPi.noClosedGrownTermAtDataClassifierProbe {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject classifier)
    (notFunction : ∀ (domainCode : RawTerm 0) (codomainCode : RawTerm 1),
      ¬ Conv classifier (piTyCodeCell domainCode codomainCode))
    (notType : ∀ (levelExpr : LevelExpr) (flag : UniverseFlag),
      ¬ Conv classifier (universeCodeCell levelExpr flag)) :
    False := by
  have terminates :=
    HasTypeDescPi.stronglyNormalizingOfWfContextDesc WfContextDesc.emptyIsWellFormed typed
  obtain ⟨normalForm, reachesNormalForm, normalFormIsNormal⟩ :=
    exists_normalForm_of_isStronglyNormalizing terminates
  exact HasTypeDescPi.noClosedNormalTermAtDataClassifier
    (HasTypeDescPi.subjectReductionStar WfContextDescPi.emptyIsWellFormed typed reachesNormalForm)
    normalFormIsNormal notFunction notType

/-- Generic canonicity packaging: abstract standalone-value predicate + grown rigidity ⟹ canonicity. -/
theorem dataCanonicityFromGrownRigidityProbe {profile : PolyProfile} {isValue : RawTerm 0 → Prop}
    {dataTypeCode : RawTerm 0} {StandaloneTyped : RawTerm 0 → Prop}
    (standaloneCanonicity : ∀ subject : RawTerm 0, StandaloneTyped subject →
      ∃ value : RawTerm 0, StepStar subject value ∧ isValue value)
    (notFunction : ∀ (domainCode : RawTerm 0) (codomainCode : RawTerm 1),
      ¬ Conv dataTypeCode (piTyCodeCell domainCode codomainCode))
    (notType : ∀ (levelExpr : LevelExpr) (flag : UniverseFlag),
      ¬ Conv dataTypeCode (universeCodeCell levelExpr flag))
    (subject : RawTerm 0)
    (typed : StandaloneTyped subject ∨
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject dataTypeCode) :
    ∃ value : RawTerm 0, StepStar subject value ∧ isValue value := by
  rcases typed with standaloneTyped | grownTyped
  · exact standaloneCanonicity subject standaloneTyped
  · exact (HasTypeDescPi.noClosedGrownTermAtDataClassifierProbe grownTyped notFunction notType).elim

/-- Bool instance through the generic packaging — non-vacuity witness, subsuming closedBoolCanonicalForms. -/
theorem boolCanonicityViaGrownRigidityProbe {profile : PolyProfile} {subject : RawTerm 0}
    (typed :
      HasTypeDescDataIntro profile (TypingContext.empty : TypingContext profile 0) subject boolTypeCell ∨
      HasTypeDescBaseType profile (TypingContext.empty : TypingContext profile 0) subject boolTypeCell ∨
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject boolTypeCell) :
    ∃ value : RawTerm 0, StepStar subject value ∧
      (value = boolTrueCell ∨ value = boolFalseCell) := by
  refine dataCanonicityFromGrownRigidityProbe
    (profile := profile)
    (isValue := fun value => value = boolTrueCell ∨ value = boolFalseCell)
    (StandaloneTyped := fun standaloneSubject =>
      HasTypeDescDataIntro profile .empty standaloneSubject boolTypeCell ∨
      HasTypeDescBaseType profile .empty standaloneSubject boolTypeCell)
    (fun _standaloneSubject standaloneTyped => by
      rcases standaloneBoolCanonicalForms standaloneTyped with valueEq | valueEq
      · subst valueEq; exact ⟨_, StepStar.refl _, Or.inl rfl⟩
      · subst valueEq; exact ⟨_, StepStar.refl _, Or.inr rfl⟩)
    (fun _domainCode _codomainCode convToPiCode => Conv.boolTypeCell_not_piTyCode convToPiCode)
    (fun _levelExpr _flag convToUniverseCode => Conv.boolTypeCell_not_universeCode convToUniverseCode)
    subject ?_
  rcases typed with dataIntroTyped | baseTypeTyped | grownTyped
  · exact Or.inl (Or.inl dataIntroTyped)
  · exact Or.inl (Or.inr baseTypeTyped)
  · exact Or.inr grownTyped

/-- Σ-type grown vacuity, arbitrary subject — instantiation of the generic engine (the grown half of future
Σ-canonicity; arbitrary-subject twin of #1065's normal-only noClosedNormalTermAtSigmaType). -/
theorem HasTypeDescPi.noClosedGrownTermAtSigmaTypeProbe {profile : PolyProfile} {subject : RawTerm 0}
    {sigmaDomain : RawTerm 0} {sigmaCodomain : RawTerm 1}
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
      (sigmaTyCodeCell sigmaDomain sigmaCodomain)) :
    False :=
  HasTypeDescPi.noClosedGrownTermAtDataClassifierProbe typed
    (fun _domainCode _codomainCode convToPiCode => Conv.piTyCode_not_sigmaTyCode convToPiCode.sym)
    (fun _levelExpr _flag convToUniverseCode => Conv.sigmaTyCode_not_universeCode convToUniverseCode)

end FX1Poly.Typed

#print axioms FX1Poly.Typed.HasTypeDescPi.noClosedGrownTermAtDataClassifierProbe
#print axioms FX1Poly.Typed.dataCanonicityFromGrownRigidityProbe
#print axioms FX1Poly.Typed.boolCanonicityViaGrownRigidityProbe
#print axioms FX1Poly.Typed.HasTypeDescPi.noClosedGrownTermAtSigmaTypeProbe
