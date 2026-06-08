import FX1Poly.Typed.GrownOpenCanonicalFormsByClassifier

/-! Probe: OPEN progress refined by classifier — the last empty matrix cell.
    at Π: steps ∨ is-λ ∨ neutral; at universe: steps ∨ is-former ∨ neutral.
    Unconditional (no SR), the open per-classifier progress twin of firing-112. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

theorem HasTypeDescPi.openFunctionStepsOrIsLambdaOrNeutral {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject : RawTerm scope}
    {outerDomain : RawTerm scope} {outerCodomain : RawTerm (scope + 1)}
    (typed : HasTypeDescPi profile context subject (piTyCodeCell outerDomain outerCodomain))
    (wellFormed : WfContextDesc context) :
    (∃ reduct : RawTerm scope, Step subject reduct) ∨
    (∃ body : RawTerm (scope + 1), subject = lamCell body) ∨ IsNeutral subject := by
  by_cases isNormal : RawTerm.isStepNormalForm subject
  · exact Or.inr (HasTypeDescPi.openNormalFunctionIsLambdaOrNeutral typed wellFormed isNormal)
  · exact Or.inl (exists_step_of_not_isStepNormalForm isNormal)

theorem HasTypeDescPi.openTypeStepsOrIsFormerOrNeutral {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject : RawTerm scope}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (typed : HasTypeDescPi profile context subject (universeCodeCell levelExpr flag))
    (wellFormed : WfContextDesc context) :
    (∃ reduct : RawTerm scope, Step subject reduct) ∨
    (RawTerm.headGenerator subject = Generator.gen_piTyCode ∨
     RawTerm.headGenerator subject = Generator.gen_sigmaTyCode ∨
     RawTerm.headGenerator subject = Generator.gen_universeCode ∨
     RawTerm.headGenerator subject = Generator.gen_listCode ∨
     RawTerm.headGenerator subject = Generator.gen_optionCode) ∨ IsNeutral subject := by
  by_cases isNormal : RawTerm.isStepNormalForm subject
  · exact Or.inr (HasTypeDescPi.openNormalTypeIsFormerOrNeutral typed wellFormed isNormal)
  · exact Or.inl (exists_step_of_not_isStepNormalForm isNormal)

end FX1Poly.Typed

#print axioms FX1Poly.Typed.HasTypeDescPi.openFunctionStepsOrIsLambdaOrNeutral
#print axioms FX1Poly.Typed.HasTypeDescPi.openTypeStepsOrIsFormerOrNeutral
