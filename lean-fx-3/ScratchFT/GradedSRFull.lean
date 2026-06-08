import FX1Poly.Modal.GradedProgress
import FX1Poly.Modal.GradedSubjectReductionGeneric

/-! Probe: congruence-closed (full-β) SR over GradedLambda.Reduces (grades-exact), its star closure,
and the capstone — every closed well-typed term EVALUATES to a .lam value. -/

namespace FX1Poly.Modal

open FX1Poly.Core (ReflTransClosure)

/-- Full-β subject reduction (grades-exact): typing is preserved under ANY single `Reduces` step
(β at any position), with the grade vector and type literally unchanged. -/
theorem hasGradeOver_reducesPreservation {R : OrderedGradeSemiring}
    (lawful : IsLawfulOrderedGradeSemiring R) {term term' : GradedLambda}
    (step : GradedLambda.Reduces term term') :
    ∀ {ctx : List (GTypeOver R)} {grades : GradeVectorOver R} {resultType : GTypeOver R},
      HasGradeOver R ctx grades term resultType → HasGradeOver R ctx grades term' resultType := by
  induction step with
  | beta body argTerm =>
      intro ctx grades resultType typed
      exact hasGradeOver_betaPreservation lawful typed
  | congLam body body' _ bodyIH =>
      intro ctx grades resultType typed
      obtain ⟨binderGrade, domain, codomain, arrowEq, bodyTyped⟩ := HasGradeOver.invertLam typed
      subst arrowEq
      exact HasGradeOver.lam ctx binderGrade domain codomain grades body' (bodyIH bodyTyped)
  | congAppLeft function function' argTerm _ functionIH =>
      intro ctx grades resultType typed
      obtain ⟨binderGrade, domain, functionGrades, argumentGrades, functionTyped, argTyped,
        gradesEq⟩ := HasGradeOver.invertApp typed
      subst gradesEq
      exact HasGradeOver.app ctx binderGrade domain resultType functionGrades argumentGrades
        function' argTerm (functionIH functionTyped) argTyped
  | congAppRight function argTerm argTerm' _ argumentIH =>
      intro ctx grades resultType typed
      obtain ⟨binderGrade, domain, functionGrades, argumentGrades, functionTyped, argTyped,
        gradesEq⟩ := HasGradeOver.invertApp typed
      subst gradesEq
      exact HasGradeOver.app ctx binderGrade domain resultType functionGrades argumentGrades
        function argTerm' functionTyped (argumentIH argTyped)

/-- Multi-step full-β subject reduction: typing preserved along any `ReducesStar` chain. -/
theorem hasGradeOver_reducesStarPreservation {R : OrderedGradeSemiring}
    (lawful : IsLawfulOrderedGradeSemiring R) {ctx : List (GTypeOver R)}
    {term term' : GradedLambda} (star : GradedLambda.ReducesStar term term') :
    ∀ {grades : GradeVectorOver R} {resultType : GTypeOver R},
      HasGradeOver R ctx grades term resultType → HasGradeOver R ctx grades term' resultType := by
  induction star with
  | refl _ => intro grades resultType typed; exact typed
  | head first _ restIH =>
      intro grades resultType typed
      exact restIH (hasGradeOver_reducesPreservation lawful first typed)

/-- ★ The capstone — EVALUATION: every closed well-typed term β-reduces to a `.lam` value.  SN gives a
finite reduction (`Acc`); at each step progress says reduce-or-be-a-lam, SR retypes the reduct (grades
exact), so the well-founded recursion terminates at a `.lam`. -/
theorem closedReducesToLam {R : OrderedGradeSemiring} (lawful : IsLawfulOrderedGradeSemiring R)
    {grades : GradeVectorOver R} {term : GradedLambda} {resultType : GTypeOver R}
    (typed : HasGradeOver R [] grades term resultType) :
    ∃ body, GradedLambda.ReducesStar term (.lam body) := by
  have general : ∀ (current : GradedLambda), GradedLambda.IsStronglyNormalizing current →
      ∀ {currentGrades : GradeVectorOver R} {currentType : GTypeOver R},
        HasGradeOver R [] currentGrades current currentType →
          ∃ body, GradedLambda.ReducesStar current (.lam body) := by
    intro current accessible
    induction accessible with
    | intro current _ reductIH =>
        intro currentGrades currentType currentTyped
        cases GradedLambda.stepOrNormal current with
        | inr normal =>
            obtain ⟨body, currentEq⟩ := closedNormalFormIsLam current currentTyped normal
            refine ⟨body, ?_⟩
            rw [currentEq]
            exact ReflTransClosure.refl _
        | inl stepWitness =>
            obtain ⟨reduct, step⟩ := stepWitness
            obtain ⟨body, reductStar⟩ :=
              reductIH reduct step (hasGradeOver_reducesPreservation lawful step currentTyped)
            exact ⟨body, ReflTransClosure.head step reductStar⟩
  exact general term typed.stronglyNormalizing typed

/-- Usage-dimension smoke: the linear identity already IS a `.lam` (reduces in zero steps). -/
theorem usageLinearIdentity_reducesToLam :
    ∃ body, GradedLambda.ReducesStar (.lam (.var 0)) (.lam body) :=
  closedReducesToLam fxUsageSemiring_isLawful usageLinearIdentity_typedViaGeneric

end FX1Poly.Modal

#print axioms FX1Poly.Modal.hasGradeOver_reducesPreservation
#print axioms FX1Poly.Modal.hasGradeOver_reducesStarPreservation
#print axioms FX1Poly.Modal.closedReducesToLam
#print axioms FX1Poly.Modal.usageLinearIdentity_reducesToLam
