import FX1Poly.Modal.OverflowLatticeDimension

namespace FX1Poly.Modal

-- PRECISION dimension (§6.3 Dim 14), qualitative projection: exact (0 ULP, bottom) vs inexact (>0 ULP).
inductive PrecisionGrade where
  | exactPrecision
  | inexactPrecision
  deriving DecidableEq

-- Does the overflow mode PRESERVE exactness (never silently yield a value differing from the true result)?
def OverflowGrade.isExactnessPreserving : OverflowGrade → Bool
  | .exactGrade => true
  | .trapGrade => true
  | .wrapGrade => false
  | .saturateGrade => false
  | .conflictGrade => false

-- §6.8 joint consistency: demanding exact precision is only consistent with an exactness-preserving overflow mode.
def IsJointlyConsistent (precision : PrecisionGrade) (overflow : OverflowGrade) : Prop :=
  precision = PrecisionGrade.exactPrecision → overflow.isExactnessPreserving = true

-- ★ THE §6.8 COLLISION: exact precision (decimal) and wrap overflow are NOT jointly consistent.
theorem exactPrecisionCollidesWithWrapOverflow :
    ¬ IsJointlyConsistent PrecisionGrade.exactPrecision OverflowGrade.wrapGrade :=
  fun consistent => Bool.noConfusion (consistent rfl)

theorem exactPrecisionCollidesWithSaturateOverflow :
    ¬ IsJointlyConsistent PrecisionGrade.exactPrecision OverflowGrade.saturateGrade :=
  fun consistent => Bool.noConfusion (consistent rfl)

theorem exactPrecisionConsistentWithExactOverflow :
    IsJointlyConsistent PrecisionGrade.exactPrecision OverflowGrade.exactGrade :=
  fun _ => rfl

theorem exactPrecisionConsistentWithTrapOverflow :
    IsJointlyConsistent PrecisionGrade.exactPrecision OverflowGrade.trapGrade :=
  fun _ => rfl

theorem inexactPrecisionConsistentWithEveryOverflow (overflow : OverflowGrade) :
    IsJointlyConsistent PrecisionGrade.inexactPrecision overflow :=
  fun absurdEq => PrecisionGrade.noConfusion absurdEq

-- FULL CHARACTERIZATION: the exact-precision collision set is EXACTLY the non-exactness-preserving modes.
theorem exactPrecisionCollision_iff_notPreserving (overflow : OverflowGrade) :
    ¬ IsJointlyConsistent PrecisionGrade.exactPrecision overflow ↔
      overflow.isExactnessPreserving = false := by
  constructor
  · intro collides
    cases hPreserve : overflow.isExactnessPreserving with
    | false => rfl
    | true => exact absurd (fun _ => hPreserve) collides
  · intro notPreserving consistent
    rw [consistent rfl] at notPreserving
    exact Bool.noConfusion notPreserving

theorem isJointlyConsistent_iff (precision : PrecisionGrade) (overflow : OverflowGrade) :
    IsJointlyConsistent precision overflow ↔
      (precision = PrecisionGrade.inexactPrecision ∨ overflow.isExactnessPreserving = true) := by
  constructor
  · intro consistent
    cases precision with
    | exactPrecision => exact Or.inr (consistent rfl)
    | inexactPrecision => exact Or.inl rfl
  · intro disjunct exactEq
    cases disjunct with
    | inl inexactEq => rw [exactEq] at inexactEq; exact PrecisionGrade.noConfusion inexactEq
    | inr preserving => exact preserving

end FX1Poly.Modal

#print axioms FX1Poly.Modal.exactPrecisionCollidesWithWrapOverflow
#print axioms FX1Poly.Modal.exactPrecisionCollision_iff_notPreserving
#print axioms FX1Poly.Modal.isJointlyConsistent_iff
