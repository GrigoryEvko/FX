import FX1Poly.Modal.GradeVector

/-! Scratch probe: grade-vector order (IsPointwiseBelow as a partial order) + the context-division
Galois connection (vector residuation) + operation monotonicity.  Toward DIM2-3's Lam-rule
comparison. -/

namespace FX1Poly.Modal

-- scalar: two-sided add monotonicity (companion to the shipped add_le_add_left)
theorem UsageGrade.add_le_add {firstGrade firstBound secondGrade secondBound : UsageGrade}
    (firstBelow : UsageGrade.le firstGrade firstBound = true)
    (secondBelow : UsageGrade.le secondGrade secondBound = true) :
    UsageGrade.le (UsageGrade.add firstGrade secondGrade) (UsageGrade.add firstBound secondBound) = true := by
  cases firstGrade <;> cases firstBound <;> cases secondGrade <;> cases secondBound <;>
    first | rfl | exact Bool.noConfusion firstBelow | exact Bool.noConfusion secondBelow

-- ===== IsPointwiseBelow is a partial order =====

theorem GradeVector.IsPointwiseBelow.refl (someVector : GradeVector) :
    GradeVector.IsPointwiseBelow someVector someVector := by
  induction someVector with
  | nil => exact True.intro
  | cons headGrade restGrades restIH => exact ⟨UsageGrade.le_refl headGrade, restIH⟩

theorem GradeVector.IsPointwiseBelow.trans {firstVector secondVector thirdVector : GradeVector}
    (firstBelowSecond : GradeVector.IsPointwiseBelow firstVector secondVector)
    (secondBelowThird : GradeVector.IsPointwiseBelow secondVector thirdVector) :
    GradeVector.IsPointwiseBelow firstVector thirdVector := by
  induction firstVector generalizing secondVector thirdVector with
  | nil =>
      cases secondVector with
      | nil =>
          cases thirdVector with
          | nil => exact True.intro
          | cons _ _ => exact secondBelowThird.elim
      | cons _ _ => exact firstBelowSecond.elim
  | cons firstHead firstRest restIH =>
      cases secondVector with
      | nil => exact firstBelowSecond.elim
      | cons secondHead secondRest =>
          cases thirdVector with
          | nil => exact secondBelowThird.elim
          | cons thirdHead thirdRest =>
              exact ⟨UsageGrade.le_trans firstBelowSecond.1 secondBelowThird.1,
                restIH firstBelowSecond.2 secondBelowThird.2⟩

theorem GradeVector.IsPointwiseBelow.antisymm {firstVector secondVector : GradeVector}
    (firstBelowSecond : GradeVector.IsPointwiseBelow firstVector secondVector)
    (secondBelowFirst : GradeVector.IsPointwiseBelow secondVector firstVector) :
    firstVector = secondVector := by
  induction firstVector generalizing secondVector with
  | nil =>
      cases secondVector with
      | nil => rfl
      | cons _ _ => exact firstBelowSecond.elim
  | cons firstHead firstRest restIH =>
      cases secondVector with
      | nil => exact firstBelowSecond.elim
      | cons secondHead secondRest =>
          have headEq : firstHead = secondHead :=
            UsageGrade.le_antisymm firstBelowSecond.1 secondBelowFirst.1
          have restEq : firstRest = secondRest := restIH firstBelowSecond.2 secondBelowFirst.2
          rw [headEq, restEq]

-- ===== operation monotonicity w.r.t. the order =====

theorem GradeVector.IsPointwiseBelow.scale_mono (scaleGrade : UsageGrade)
    {firstVector secondVector : GradeVector}
    (below : GradeVector.IsPointwiseBelow firstVector secondVector) :
    GradeVector.IsPointwiseBelow (GradeVector.scale scaleGrade firstVector)
      (GradeVector.scale scaleGrade secondVector) := by
  induction firstVector generalizing secondVector with
  | nil =>
      cases secondVector with
      | nil => exact True.intro
      | cons _ _ => exact below.elim
  | cons firstHead firstRest restIH =>
      cases secondVector with
      | nil => exact below.elim
      | cons secondHead secondRest =>
          exact ⟨UsageGrade.mul_le_mul_left scaleGrade below.1, restIH below.2⟩

theorem GradeVector.IsPointwiseBelow.add_mono {firstVector firstBound secondVector secondBound : GradeVector}
    (firstBelow : GradeVector.IsPointwiseBelow firstVector firstBound)
    (secondBelow : GradeVector.IsPointwiseBelow secondVector secondBound) :
    GradeVector.IsPointwiseBelow (GradeVector.add firstVector secondVector)
      (GradeVector.add firstBound secondBound) := by
  induction firstVector generalizing firstBound secondVector secondBound with
  | nil =>
      cases firstBound with
      | nil => exact True.intro
      | cons _ _ => exact firstBelow.elim
  | cons firstHead firstRest restIH =>
      cases firstBound with
      | nil => exact firstBelow.elim
      | cons firstBoundHead firstBoundRest =>
          cases secondVector with
          | nil =>
              cases secondBound with
              | nil => exact True.intro
              | cons _ _ => exact secondBelow.elim
          | cons secondHead secondRest =>
              cases secondBound with
              | nil => exact secondBelow.elim
              | cons secondBoundHead secondBoundRest =>
                  exact ⟨UsageGrade.add_le_add firstBelow.1 secondBelow.1,
                    restIH firstBelow.2 secondBelow.2⟩

-- ===== the context-division Galois connection (vector residuation) =====

theorem GradeVector.contextDivide_residuation (divisorGrade : UsageGrade)
    (quotientCandidate dividendVector : GradeVector) :
    GradeVector.IsPointwiseBelow (GradeVector.scale divisorGrade quotientCandidate) dividendVector ↔
      GradeVector.IsPointwiseBelow quotientCandidate
        (GradeVector.contextDivide divisorGrade dividendVector) := by
  induction quotientCandidate generalizing dividendVector with
  | nil =>
      cases dividendVector with
      | nil => exact Iff.rfl
      | cons _ _ => exact Iff.rfl
  | cons quotientHead quotientRest restIH =>
      cases dividendVector with
      | nil => exact Iff.rfl
      | cons dividendHead dividendRest =>
          have headIff : (UsageGrade.le (UsageGrade.mul divisorGrade quotientHead) dividendHead = true) ↔
              (UsageGrade.le quotientHead (UsageGrade.div dividendHead divisorGrade) = true) := by
            rw [UsageGrade.mul_comm divisorGrade quotientHead]
            exact UsageGrade.div_residuation dividendHead divisorGrade quotientHead
          exact Iff.intro
            (fun ⟨headBelow, restBelow⟩ => ⟨headIff.mp headBelow, (restIH dividendRest).mp restBelow⟩)
            (fun ⟨headBelow, restBelow⟩ => ⟨headIff.mpr headBelow, (restIH dividendRest).mpr restBelow⟩)

#print axioms UsageGrade.add_le_add
#print axioms GradeVector.IsPointwiseBelow.refl
#print axioms GradeVector.IsPointwiseBelow.trans
#print axioms GradeVector.IsPointwiseBelow.antisymm
#print axioms GradeVector.IsPointwiseBelow.scale_mono
#print axioms GradeVector.IsPointwiseBelow.add_mono
#print axioms GradeVector.contextDivide_residuation

end FX1Poly.Modal
