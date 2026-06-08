import FX1Poly.Modal.UsageDiscipline

/-! Scratch probe: the usage check as a verified Boolean decision procedure.
`isPointwiseBelowBool` (computable) + correctness (`= true ↔ IsPointwiseBelow`), lifted to
`wellGradedCheck`; the Atkey/linear examples compute to false/true by rfl. -/

namespace FX1Poly.Modal

/-- Computable pointwise-`≤` on grade vectors (truncating; `false` on length mismatch). -/
def GradeVector.isPointwiseBelowBool : GradeVector → GradeVector → Bool
  | .nil, .nil => true
  | .nil, .cons _ _ => false
  | .cons _ _, .nil => false
  | .cons firstHead firstRest, .cons secondHead secondRest =>
      (UsageGrade.le firstHead secondHead) && (GradeVector.isPointwiseBelowBool firstRest secondRest)

/-- **Correctness of the Boolean check.**  `isPointwiseBelowBool a b = true ↔ IsPointwiseBelow a b`
— the decision procedure is sound and complete for the pointwise order. -/
theorem GradeVector.isPointwiseBelowBool_correct (firstVector secondVector : GradeVector) :
    GradeVector.isPointwiseBelowBool firstVector secondVector = true ↔
      GradeVector.IsPointwiseBelow firstVector secondVector := by
  induction firstVector generalizing secondVector with
  | nil =>
      cases secondVector with
      | nil => exact ⟨fun _ => True.intro, fun _ => rfl⟩
      | cons _ _ => exact ⟨fun contra => Bool.noConfusion contra, fun contra => contra.elim⟩
  | cons firstHead firstRest restIH =>
      cases secondVector with
      | nil => exact ⟨fun contra => Bool.noConfusion contra, fun contra => contra.elim⟩
      | cons secondHead secondRest =>
          show (UsageGrade.le firstHead secondHead &&
                GradeVector.isPointwiseBelowBool firstRest secondRest) = true ↔
              (UsageGrade.le firstHead secondHead = true) ∧
                GradeVector.IsPointwiseBelow firstRest secondRest
          constructor
          · intro hbool
            have headOk : UsageGrade.le firstHead secondHead = true := by
              cases hle : UsageGrade.le firstHead secondHead with
              | true => rfl
              | false => rw [hle] at hbool; exact Bool.noConfusion hbool
            have restBool : GradeVector.isPointwiseBelowBool firstRest secondRest = true := by
              rw [headOk] at hbool; exact hbool
            exact ⟨headOk, (restIH secondRest).mp restBool⟩
          · intro hprop
            have restBool : GradeVector.isPointwiseBelowBool firstRest secondRest = true :=
              (restIH secondRest).mpr hprop.2
            rw [hprop.1]
            exact restBool

/-- The usage check as a computable Boolean: `usage ≤ declaredGrades`. -/
def GradedLambda.wellGradedCheck (scope : Nat) (term : GradedLambda)
    (declaredGrades : GradeVector) : Bool :=
  GradeVector.isPointwiseBelowBool (GradedLambda.usage scope term) declaredGrades

/-- **Correctness of the usage check.**  `wellGradedCheck = true ↔ WellGraded` — the computable
check decides well-gradedness. -/
theorem GradedLambda.wellGradedCheck_correct (scope : Nat) (term : GradedLambda)
    (declaredGrades : GradeVector) :
    GradedLambda.wellGradedCheck scope term declaredGrades = true ↔
      GradedLambda.WellGraded scope term declaredGrades :=
  GradeVector.isPointwiseBelowBool_correct (GradedLambda.usage scope term) declaredGrades

-- ===== the check computes the right answers on the §27.2 corpus =====

/-- The check COMPUTES `false` on the Atkey closure (f used at ω, declared linear). -/
theorem atkey_check_false :
    GradedLambda.wellGradedCheck 1 atkeyClosure linearContext = false := rfl

/-- The check COMPUTES `true` on the linear closure (f used once, declared linear). -/
theorem linear_check_true :
    GradedLambda.wellGradedCheck 1 linearClosure linearContext = true := rfl

#print axioms GradeVector.isPointwiseBelowBool
#print axioms GradeVector.isPointwiseBelowBool_correct
#print axioms GradedLambda.wellGradedCheck
#print axioms GradedLambda.wellGradedCheck_correct
#print axioms atkey_check_false
#print axioms linear_check_true

end FX1Poly.Modal
