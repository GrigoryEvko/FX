import FX1Poly.Modal.GradedNormalization
import FX1Poly.Modal.GradeErasureGeneric

/-! Probe: PROGRESS / canonical forms for the generic graded engine HasGradeOver R.
A closed well-typed normal form is a λ; a closed well-typed term reduces or is a λ. -/

namespace FX1Poly.Modal

/-- Canonical forms: a CLOSED (typed in `[]`) normal form is a `.lam`. -/
theorem closedNormalFormIsLam {R : OrderedGradeSemiring} (term : GradedLambda) :
    ∀ {grades : GradeVectorOver R} {resultType : GTypeOver R},
      HasGradeOver R [] grades term resultType → GradedLambda.IsNormalForm term →
        ∃ body, term = .lam body := by
  induction term with
  | var index =>
      intro grades resultType typed _
      obtain ⟨lookupOk, _⟩ := HasGradeOver.invertVar typed
      cases lookupOk
  | lam body _ =>
      intro grades resultType _ _
      exact ⟨body, rfl⟩
  | app function argument functionIH _ =>
      intro grades resultType typed normal
      obtain ⟨fnBinderGrade, fnDomain, fnGrades, argGrades, functionTyped, _, _⟩ :=
        HasGradeOver.invertApp typed
      have functionNF : GradedLambda.IsNormalForm function := by
        intro reduct step
        exact normal (GradedLambda.Reduces.congAppLeft function reduct argument step)
      obtain ⟨fnBody, fnEq⟩ := functionIH functionTyped functionNF
      subst fnEq
      exact (normal (GradedLambda.Reduces.beta fnBody argument)).elim

/-- Progress: a CLOSED well-typed term either β-reduces or is a `.lam` value. -/
theorem closedWellTypedProgress {R : OrderedGradeSemiring} {grades : GradeVectorOver R}
    {term : GradedLambda} {resultType : GTypeOver R}
    (typed : HasGradeOver R [] grades term resultType) :
    (∃ reduct, GradedLambda.Reduces term reduct) ∨ (∃ body, term = .lam body) := by
  cases GradedLambda.stepOrNormal term with
  | inl stepWitness => exact Or.inl ⟨stepWitness.1, stepWitness.2⟩
  | inr normal => exact Or.inr (closedNormalFormIsLam term typed normal)

/-- A closed well-typed term of BASE type always β-reduces — base has no closed values, because
the only closed values are `.lam`s and a `.lam` is typed at an arrow, never at base. -/
theorem closedBaseTypeAlwaysSteps {R : OrderedGradeSemiring} {grades : GradeVectorOver R}
    {term : GradedLambda} (typed : HasGradeOver R [] grades term GTypeOver.base) :
    ∃ reduct, GradedLambda.Reduces term reduct := by
  cases closedWellTypedProgress typed with
  | inl steps => exact steps
  | inr isLam =>
      obtain ⟨body, termEq⟩ := isLam
      subst termEq
      obtain ⟨binderGrade, domain, codomain, baseEq, _⟩ := HasGradeOver.invertLam typed
      cases baseEq

/-- Usage-dimension smoke: the linear identity is already a value (the right disjunct). -/
theorem usageLinearIdentity_isValue :
    (∃ reduct, GradedLambda.Reduces (.lam (.var 0)) reduct) ∨
      (∃ body, (GradedLambda.lam (.var 0)) = .lam body) :=
  closedWellTypedProgress (usageLinearIdentity_typedViaGeneric)

end FX1Poly.Modal

#print axioms FX1Poly.Modal.closedNormalFormIsLam
#print axioms FX1Poly.Modal.closedWellTypedProgress
#print axioms FX1Poly.Modal.closedBaseTypeAlwaysSteps
#print axioms FX1Poly.Modal.usageLinearIdentity_isValue
