import FX1Poly.Typed.GrownCanonicalFormsByClassifier

/-! Probe: closed PROGRESS refined by classifier for the grown engine.
    - at a Π classifier: a closed grown-typed term STEPS or IS a λ (with body extracted)
    - at a universe classifier: a closed grown-typed TYPE STEPS or IS a type FORMER
    Unconditional (no SR), the per-classifier refinement of `closedProgress`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

theorem HasTypeDescPi.closedFunctionStepsOrIsLambda {profile : PolyProfile} {subject : RawTerm 0}
    {outerDomain : RawTerm 0} {outerCodomain : RawTerm 1}
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
      (piTyCodeCell outerDomain outerCodomain)) :
    (∃ reduct : RawTerm 0, Step subject reduct) ∨ (∃ body : RawTerm 1, subject = lamCell body) := by
  by_cases isNormal : RawTerm.isStepNormalForm subject
  · exact Or.inr (HasTypeDescPi.closedNormalFunctionIsLambda typed isNormal)
  · exact Or.inl (exists_step_of_not_isStepNormalForm isNormal)

theorem HasTypeDescPi.closedTypeStepsOrIsFormer {profile : PolyProfile} {subject : RawTerm 0}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
      (universeCodeCell levelExpr flag)) :
    (∃ reduct : RawTerm 0, Step subject reduct) ∨
    (RawTerm.headGenerator subject = Generator.gen_piTyCode ∨
     RawTerm.headGenerator subject = Generator.gen_sigmaTyCode ∨
     RawTerm.headGenerator subject = Generator.gen_universeCode ∨
     RawTerm.headGenerator subject = Generator.gen_listCode ∨
     RawTerm.headGenerator subject = Generator.gen_optionCode) := by
  by_cases isNormal : RawTerm.isStepNormalForm subject
  · exact Or.inr (HasTypeDescPi.closedNormalTypeIsFormer typed isNormal)
  · exact Or.inl (exists_step_of_not_isStepNormalForm isNormal)

end FX1Poly.Typed

#print axioms FX1Poly.Typed.HasTypeDescPi.closedFunctionStepsOrIsLambda
#print axioms FX1Poly.Typed.HasTypeDescPi.closedTypeStepsOrIsFormer
