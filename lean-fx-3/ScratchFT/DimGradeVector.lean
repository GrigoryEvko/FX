import FX1Poly.Modal.ResourceGraded

/-! Scratch probe v4 for DIM2-2 (#875): grade-vector substrate as an UNINDEXED grade list
(length-aligned to scope like TypingContext.length).  Plain inductive ⟹ binary `add` match is
genuinely total (no index-impossible arms) ⟹ propext-clean. -/

namespace FX1Poly.Modal

/-- A grade vector: one usage grade per binding, as a cons-list.  Unindexed; alignment with the
type context is by `length` (mirroring `TypingContext.length`), keeping the binary pointwise `add`
match total and propext-free. -/
inductive GradeVector where
  | nil : GradeVector
  | cons : UsageGrade → GradeVector → GradeVector
  deriving DecidableEq, Repr

/-- The number of graded bindings. -/
def GradeVector.length : GradeVector → Nat
  | .nil => 0
  | .cons _ restGrades => restGrades.length + 1

/-- The all-zero grade vector of a given length (every binding erased / ghost). -/
def GradeVector.zero : Nat → GradeVector
  | 0 => .nil
  | scope + 1 => .cons UsageGrade.zero (GradeVector.zero scope)

/-- Pointwise addition (context splitting / parallel use, §7.7); truncates to the shorter length. -/
def GradeVector.add : GradeVector → GradeVector → GradeVector
  | .nil, _ => .nil
  | .cons _ _, .nil => .nil
  | .cons firstHead firstRest, .cons secondHead secondRest =>
      .cons (UsageGrade.add firstHead secondHead) (GradeVector.add firstRest secondRest)

/-- Scalar multiplication: scale every binding's grade by `scaleGrade` (the App rule's `r * p`). -/
def GradeVector.scale (scaleGrade : UsageGrade) : GradeVector → GradeVector
  | .nil => .nil
  | .cons headGrade restGrades =>
      .cons (UsageGrade.mul scaleGrade headGrade) (GradeVector.scale scaleGrade restGrades)

-- ===== length coherence =====

theorem GradeVector.zero_length (scope : Nat) : (GradeVector.zero scope).length = scope := by
  induction scope with
  | zero => rfl
  | succ scope restIH => show (GradeVector.zero scope).length + 1 = scope + 1; rw [restIH]

theorem GradeVector.scale_length (scaleGrade : UsageGrade) (someVector : GradeVector) :
    (GradeVector.scale scaleGrade someVector).length = someVector.length := by
  induction someVector with
  | nil => rfl
  | cons headGrade restGrades restIH =>
      show (GradeVector.scale scaleGrade restGrades).length + 1 = restGrades.length + 1
      rw [restIH]

-- ===== pointwise-lifted commutative-monoid laws =====

theorem GradeVector.add_comm (firstVector secondVector : GradeVector) :
    GradeVector.add firstVector secondVector = GradeVector.add secondVector firstVector := by
  induction firstVector generalizing secondVector with
  | nil => cases secondVector <;> rfl
  | cons firstHead firstRest restIH =>
      cases secondVector with
      | nil => rfl
      | cons secondHead secondRest =>
          simp only [GradeVector.add]
          rw [UsageGrade.add_comm firstHead secondHead, restIH secondRest]

theorem GradeVector.add_assoc (firstVector secondVector thirdVector : GradeVector) :
    GradeVector.add (GradeVector.add firstVector secondVector) thirdVector =
      GradeVector.add firstVector (GradeVector.add secondVector thirdVector) := by
  induction firstVector generalizing secondVector thirdVector with
  | nil => rfl
  | cons firstHead firstRest restIH =>
      cases secondVector with
      | nil => cases thirdVector <;> rfl
      | cons secondHead secondRest =>
          cases thirdVector with
          | nil => rfl
          | cons thirdHead thirdRest =>
              simp only [GradeVector.add]
              rw [UsageGrade.add_assoc firstHead secondHead thirdHead, restIH secondRest thirdRest]

theorem GradeVector.add_zero (someVector : GradeVector) :
    GradeVector.add someVector (GradeVector.zero someVector.length) = someVector := by
  induction someVector with
  | nil => rfl
  | cons headGrade restGrades restIH =>
      show GradeVector.cons (UsageGrade.add headGrade UsageGrade.zero) (GradeVector.add restGrades (GradeVector.zero restGrades.length)) = _
      rw [UsageGrade.add_zero headGrade, restIH]

theorem GradeVector.zero_add (someVector : GradeVector) :
    GradeVector.add (GradeVector.zero someVector.length) someVector = someVector := by
  induction someVector with
  | nil => rfl
  | cons headGrade restGrades restIH =>
      show GradeVector.cons (UsageGrade.add UsageGrade.zero headGrade) (GradeVector.add (GradeVector.zero restGrades.length) restGrades) = _
      rw [UsageGrade.zero_add headGrade, restIH]

-- ===== scale laws (lifting the semiring's scalar action) =====

theorem GradeVector.scale_zero_scalar (someVector : GradeVector) :
    GradeVector.scale UsageGrade.zero someVector = GradeVector.zero someVector.length := by
  induction someVector with
  | nil => rfl
  | cons headGrade restGrades restIH =>
      simp only [GradeVector.scale, GradeVector.zero, GradeVector.length]
      rw [UsageGrade.zero_mul headGrade, restIH]

theorem GradeVector.scale_one_scalar (someVector : GradeVector) :
    GradeVector.scale UsageGrade.one someVector = someVector := by
  induction someVector with
  | nil => rfl
  | cons headGrade restGrades restIH =>
      show GradeVector.cons (UsageGrade.mul UsageGrade.one headGrade) (GradeVector.scale UsageGrade.one restGrades) = _
      rw [UsageGrade.one_mul headGrade, restIH]

theorem GradeVector.scale_add (scaleGrade : UsageGrade) (firstVector secondVector : GradeVector) :
    GradeVector.scale scaleGrade (GradeVector.add firstVector secondVector) =
      GradeVector.add (GradeVector.scale scaleGrade firstVector)
        (GradeVector.scale scaleGrade secondVector) := by
  induction firstVector generalizing secondVector with
  | nil => rfl
  | cons firstHead firstRest restIH =>
      cases secondVector with
      | nil => rfl
      | cons secondHead secondRest =>
          simp only [GradeVector.add, GradeVector.scale]
          rw [UsageGrade.left_distrib scaleGrade firstHead secondHead, restIH secondRest]

theorem GradeVector.scale_scale (firstScale secondScale : UsageGrade) (someVector : GradeVector) :
    GradeVector.scale firstScale (GradeVector.scale secondScale someVector) =
      GradeVector.scale (UsageGrade.mul firstScale secondScale) someVector := by
  induction someVector with
  | nil => rfl
  | cons headGrade restGrades restIH =>
      simp only [GradeVector.scale]
      rw [UsageGrade.mul_assoc firstScale secondScale headGrade, restIH]

theorem GradeVector.scale_add_scalar (firstScale secondScale : UsageGrade) (someVector : GradeVector) :
    GradeVector.scale (UsageGrade.add firstScale secondScale) someVector =
      GradeVector.add (GradeVector.scale firstScale someVector)
        (GradeVector.scale secondScale someVector) := by
  induction someVector with
  | nil => rfl
  | cons headGrade restGrades restIH =>
      simp only [GradeVector.scale, GradeVector.add]
      rw [UsageGrade.right_distrib firstScale secondScale headGrade, restIH]

#print axioms GradeVector
#print axioms GradeVector.length
#print axioms GradeVector.zero
#print axioms GradeVector.add
#print axioms GradeVector.scale
#print axioms GradeVector.zero_length
#print axioms GradeVector.scale_length
#print axioms GradeVector.add_comm
#print axioms GradeVector.add_assoc
#print axioms GradeVector.add_zero
#print axioms GradeVector.zero_add
#print axioms GradeVector.scale_zero_scalar
#print axioms GradeVector.scale_one_scalar
#print axioms GradeVector.scale_add
#print axioms GradeVector.scale_scale
#print axioms GradeVector.scale_add_scalar

end FX1Poly.Modal
