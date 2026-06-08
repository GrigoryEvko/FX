import FX1Poly.Modal.ResourceGraded

/-! Scratch probe for DIM2-1 (#874): complete the usage ordered-semiring laws +
lawfulness bundle, zero-axiom.  Validates against the REAL `ResourceGraded` defs. -/

namespace FX1Poly.Modal

-- ===== USAGE: the missing core semiring laws =====

theorem UsageGrade.add_assoc (firstGrade secondGrade thirdGrade : UsageGrade) :
    UsageGrade.add (UsageGrade.add firstGrade secondGrade) thirdGrade =
      UsageGrade.add firstGrade (UsageGrade.add secondGrade thirdGrade) := by
  cases firstGrade <;> cases secondGrade <;> cases thirdGrade <;> rfl

theorem UsageGrade.mul_assoc (firstGrade secondGrade thirdGrade : UsageGrade) :
    UsageGrade.mul (UsageGrade.mul firstGrade secondGrade) thirdGrade =
      UsageGrade.mul firstGrade (UsageGrade.mul secondGrade thirdGrade) := by
  cases firstGrade <;> cases secondGrade <;> cases thirdGrade <;> rfl

theorem UsageGrade.mul_comm (firstGrade secondGrade : UsageGrade) :
    UsageGrade.mul firstGrade secondGrade = UsageGrade.mul secondGrade firstGrade := by
  cases firstGrade <;> cases secondGrade <;> rfl

theorem UsageGrade.left_distrib (firstGrade secondGrade thirdGrade : UsageGrade) :
    UsageGrade.mul firstGrade (UsageGrade.add secondGrade thirdGrade) =
      UsageGrade.add (UsageGrade.mul firstGrade secondGrade)
        (UsageGrade.mul firstGrade thirdGrade) := by
  cases firstGrade <;> cases secondGrade <;> cases thirdGrade <;> rfl

theorem UsageGrade.right_distrib (firstGrade secondGrade thirdGrade : UsageGrade) :
    UsageGrade.mul (UsageGrade.add firstGrade secondGrade) thirdGrade =
      UsageGrade.add (UsageGrade.mul firstGrade thirdGrade)
        (UsageGrade.mul secondGrade thirdGrade) := by
  cases firstGrade <;> cases secondGrade <;> cases thirdGrade <;> rfl

-- ===== USAGE: order laws (the "ordered" part) =====

theorem UsageGrade.le_refl (someGrade : UsageGrade) :
    UsageGrade.le someGrade someGrade = true := by
  cases someGrade <;> rfl

theorem UsageGrade.le_trans {firstGrade secondGrade thirdGrade : UsageGrade}
    (firstBelowSecond : UsageGrade.le firstGrade secondGrade = true)
    (secondBelowThird : UsageGrade.le secondGrade thirdGrade = true) :
    UsageGrade.le firstGrade thirdGrade = true := by
  cases firstGrade <;> cases secondGrade <;> cases thirdGrade <;>
    first
      | rfl
      | exact Bool.noConfusion firstBelowSecond
      | exact Bool.noConfusion secondBelowThird

theorem UsageGrade.le_antisymm {firstGrade secondGrade : UsageGrade}
    (firstBelowSecond : UsageGrade.le firstGrade secondGrade = true)
    (secondBelowFirst : UsageGrade.le secondGrade firstGrade = true) :
    firstGrade = secondGrade := by
  cases firstGrade <;> cases secondGrade <;>
    first
      | rfl
      | exact Bool.noConfusion firstBelowSecond
      | exact Bool.noConfusion secondBelowFirst

theorem UsageGrade.add_le_add_left {firstGrade secondGrade : UsageGrade}
    (scaleGrade : UsageGrade) (firstBelowSecond : UsageGrade.le firstGrade secondGrade = true) :
    UsageGrade.le (UsageGrade.add scaleGrade firstGrade)
      (UsageGrade.add scaleGrade secondGrade) = true := by
  cases scaleGrade <;> cases firstGrade <;> cases secondGrade <;>
    first | rfl | exact Bool.noConfusion firstBelowSecond

theorem UsageGrade.mul_le_mul_left {firstGrade secondGrade : UsageGrade}
    (scaleGrade : UsageGrade) (firstBelowSecond : UsageGrade.le firstGrade secondGrade = true) :
    UsageGrade.le (UsageGrade.mul scaleGrade firstGrade)
      (UsageGrade.mul scaleGrade secondGrade) = true := by
  cases scaleGrade <;> cases firstGrade <;> cases secondGrade <;>
    first | rfl | exact Bool.noConfusion firstBelowSecond

-- ===== The lawfulness bundle (ordered-semiring laws per §6.1) =====

structure IsLawfulOrderedGradeSemiring (semiring : OrderedGradeSemiring) : Prop where
  add_comm : ∀ firstGrade secondGrade : semiring.Carrier,
    semiring.add firstGrade secondGrade = semiring.add secondGrade firstGrade
  add_assoc : ∀ firstGrade secondGrade thirdGrade : semiring.Carrier,
    semiring.add (semiring.add firstGrade secondGrade) thirdGrade =
      semiring.add firstGrade (semiring.add secondGrade thirdGrade)
  add_zero : ∀ someGrade : semiring.Carrier, semiring.add someGrade semiring.zero = someGrade
  zero_add : ∀ someGrade : semiring.Carrier, semiring.add semiring.zero someGrade = someGrade
  mul_assoc : ∀ firstGrade secondGrade thirdGrade : semiring.Carrier,
    semiring.mul (semiring.mul firstGrade secondGrade) thirdGrade =
      semiring.mul firstGrade (semiring.mul secondGrade thirdGrade)
  mul_one : ∀ someGrade : semiring.Carrier, semiring.mul someGrade semiring.one = someGrade
  one_mul : ∀ someGrade : semiring.Carrier, semiring.mul semiring.one someGrade = someGrade
  mul_zero : ∀ someGrade : semiring.Carrier, semiring.mul someGrade semiring.zero = semiring.zero
  zero_mul : ∀ someGrade : semiring.Carrier, semiring.mul semiring.zero someGrade = semiring.zero
  left_distrib : ∀ firstGrade secondGrade thirdGrade : semiring.Carrier,
    semiring.mul firstGrade (semiring.add secondGrade thirdGrade) =
      semiring.add (semiring.mul firstGrade secondGrade) (semiring.mul firstGrade thirdGrade)
  right_distrib : ∀ firstGrade secondGrade thirdGrade : semiring.Carrier,
    semiring.mul (semiring.add firstGrade secondGrade) thirdGrade =
      semiring.add (semiring.mul firstGrade thirdGrade) (semiring.mul secondGrade thirdGrade)
  le_refl : ∀ someGrade : semiring.Carrier, semiring.le someGrade someGrade = true
  le_trans : ∀ firstGrade secondGrade thirdGrade : semiring.Carrier,
    semiring.le firstGrade secondGrade = true → semiring.le secondGrade thirdGrade = true →
      semiring.le firstGrade thirdGrade = true
  le_antisymm : ∀ firstGrade secondGrade : semiring.Carrier,
    semiring.le firstGrade secondGrade = true → semiring.le secondGrade firstGrade = true →
      firstGrade = secondGrade
  add_le_add_left : ∀ scaleGrade firstGrade secondGrade : semiring.Carrier,
    semiring.le firstGrade secondGrade = true →
      semiring.le (semiring.add scaleGrade firstGrade) (semiring.add scaleGrade secondGrade) = true
  mul_le_mul_left : ∀ scaleGrade firstGrade secondGrade : semiring.Carrier,
    semiring.le firstGrade secondGrade = true →
      semiring.le (semiring.mul scaleGrade firstGrade) (semiring.mul scaleGrade secondGrade) = true

theorem fxUsageSemiring_isLawful : IsLawfulOrderedGradeSemiring fxUsageSemiring where
  add_comm := UsageGrade.add_comm
  add_assoc := UsageGrade.add_assoc
  add_zero := UsageGrade.add_zero
  zero_add := UsageGrade.zero_add
  mul_assoc := UsageGrade.mul_assoc
  mul_one := UsageGrade.mul_one
  one_mul := UsageGrade.one_mul
  mul_zero := UsageGrade.mul_zero
  zero_mul := UsageGrade.zero_mul
  left_distrib := UsageGrade.left_distrib
  right_distrib := UsageGrade.right_distrib
  le_refl := UsageGrade.le_refl
  le_trans := fun _ _ _ firstBelowSecond secondBelowThird =>
    UsageGrade.le_trans firstBelowSecond secondBelowThird
  le_antisymm := fun _ _ firstBelowSecond secondBelowFirst =>
    UsageGrade.le_antisymm firstBelowSecond secondBelowFirst
  add_le_add_left := fun scaleGrade _ _ firstBelowSecond =>
    UsageGrade.add_le_add_left scaleGrade firstBelowSecond
  mul_le_mul_left := fun scaleGrade _ _ firstBelowSecond =>
    UsageGrade.mul_le_mul_left scaleGrade firstBelowSecond

-- ===== Confirm the SECURITY bug: the FIXED instance (mul := meet) is lawful =====

def fxSecuritySemiringFixed : OrderedGradeSemiring where
  Carrier := SecurityGrade
  zero := .unclassified
  one := .classified
  add := SecurityGrade.add
  mul := SecurityGrade.mul
  le := SecurityGrade.le
  carrierDecEq := instDecidableEqSecurityGrade

theorem fxSecuritySemiringFixed_isLawful : IsLawfulOrderedGradeSemiring fxSecuritySemiringFixed where
  add_comm := fun a b => by cases a <;> cases b <;> rfl
  add_assoc := fun a b c => by cases a <;> cases b <;> cases c <;> rfl
  add_zero := fun a => by cases a <;> rfl
  zero_add := fun a => by cases a <;> rfl
  mul_assoc := fun a b c => by cases a <;> cases b <;> cases c <;> rfl
  mul_one := fun a => by cases a <;> rfl
  one_mul := fun a => by cases a <;> rfl
  mul_zero := fun a => by cases a <;> rfl
  zero_mul := fun a => by cases a <;> rfl
  left_distrib := fun a b c => by cases a <;> cases b <;> cases c <;> rfl
  right_distrib := fun a b c => by cases a <;> cases b <;> cases c <;> rfl
  le_refl := fun a => by cases a <;> rfl
  le_trans := fun a b c hab hbc => by
    cases a <;> cases b <;> cases c <;>
      first | rfl | exact Bool.noConfusion hab | exact Bool.noConfusion hbc
  le_antisymm := fun a b hab hba => by
    cases a <;> cases b <;>
      first | rfl | exact Bool.noConfusion hab | exact Bool.noConfusion hba
  add_le_add_left := fun s a b hab => by
    cases s <;> cases a <;> cases b <;> first | rfl | exact Bool.noConfusion hab
  mul_le_mul_left := fun s a b hab => by
    cases s <;> cases a <;> cases b <;> first | rfl | exact Bool.noConfusion hab

-- Negative probe: the SHIPPED (buggy) instance fails one_mul (mul := join).
-- `fxSecuritySemiring.one = classified`; `classified ∨ unclassified = classified ≠ unclassified`.
example : fxSecuritySemiring.mul fxSecuritySemiring.one SecurityGrade.unclassified
    = SecurityGrade.classified := rfl   -- should be `.unclassified` for one_mul to hold

#print axioms UsageGrade.add_assoc
#print axioms UsageGrade.mul_assoc
#print axioms UsageGrade.mul_comm
#print axioms UsageGrade.left_distrib
#print axioms UsageGrade.right_distrib
#print axioms UsageGrade.le_refl
#print axioms UsageGrade.le_trans
#print axioms UsageGrade.le_antisymm
#print axioms UsageGrade.add_le_add_left
#print axioms UsageGrade.mul_le_mul_left
#print axioms fxUsageSemiring_isLawful
#print axioms fxSecuritySemiringFixed_isLawful

end FX1Poly.Modal
