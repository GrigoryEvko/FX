import LeanFX2.Graded.Instances.NatResource

/-! # Graded/Instances/Space — allocation-space bound semiring

`SpaceGrade` tracks an erased natural bound for allocation or storage
space.  The carrier intentionally wraps `Nat` instead of aliasing it,
so a grade vector can distinguish space from complexity even though
both use the same algebra.

Operations use the ordinary natural-number semiring:

* `0` = no allocation
* `1` = unit space
* `+` = combined allocation demand
* `*` = sequential scaling
* `≤` = bound subsumption

Zero-axiom verified per declaration. -/

namespace LeanFX2.Graded.Instances

open LeanFX2.Graded

/-- Space grade: natural allocation/storage bound. -/
structure SpaceGrade : Type where
  /-- The checked natural space witness. -/
  bound : Nat
  deriving DecidableEq, Repr

namespace SpaceGrade

/-- Parallel composition adds space bounds. -/
def add (first second : SpaceGrade) : SpaceGrade :=
  ⟨first.bound + second.bound⟩

/-- Sequential composition multiplies space bounds. -/
def mul (first second : SpaceGrade) : SpaceGrade :=
  ⟨first.bound * second.bound⟩

/-- Space-bound subsumption. -/
def le (first second : SpaceGrade) : Prop :=
  first.bound ≤ second.bound

end SpaceGrade

/-- Space bounds form the natural-number semiring with the usual
order.  Proofs reduce to the corresponding `Nat` laws. -/
instance : GradeSemiring SpaceGrade where
  zero := ⟨0⟩
  one  := ⟨1⟩
  add  := SpaceGrade.add
  mul  := SpaceGrade.mul
  le   := SpaceGrade.le

  add_assoc := fun first second third => by
    cases first with
    | mk firstBound =>
    cases second with
    | mk secondBound =>
    cases third with
    | mk thirdBound =>
      exact congrArg SpaceGrade.mk
        (Nat.add_assoc firstBound secondBound thirdBound)

  add_comm := fun first second => by
    cases first with
    | mk firstBound =>
    cases second with
    | mk secondBound =>
      exact congrArg SpaceGrade.mk (Nat.add_comm firstBound secondBound)

  add_zero_left := fun value => by
    cases value with
    | mk valueBound =>
      exact congrArg SpaceGrade.mk (Nat.zero_add valueBound)

  add_zero_right := fun value => by
    cases value with
    | mk valueBound =>
      exact congrArg SpaceGrade.mk (Nat.add_zero valueBound)

  mul_assoc := fun first second third => by
    cases first with
    | mk firstBound =>
    cases second with
    | mk secondBound =>
    cases third with
    | mk thirdBound =>
      exact congrArg SpaceGrade.mk
        (NatResource.mulAssocClean firstBound secondBound thirdBound)

  mul_one_left := fun value => by
    cases value with
    | mk valueBound =>
      exact congrArg SpaceGrade.mk (Nat.one_mul valueBound)

  mul_one_right := fun value => by
    cases value with
    | mk valueBound =>
      exact congrArg SpaceGrade.mk (Nat.mul_one valueBound)

  mul_distrib_left := fun scalar leftAddend rightAddend => by
    cases scalar with
    | mk scalarBound =>
    cases leftAddend with
    | mk leftBound =>
    cases rightAddend with
    | mk rightBound =>
      exact congrArg SpaceGrade.mk
        (Nat.left_distrib scalarBound leftBound rightBound)

  mul_distrib_right := fun leftAddend rightAddend scalar => by
    cases leftAddend with
    | mk leftBound =>
    cases rightAddend with
    | mk rightBound =>
    cases scalar with
    | mk scalarBound =>
      exact congrArg SpaceGrade.mk
        (NatResource.mulRightDistribClean leftBound rightBound scalarBound)

  mul_zero_left := fun value => by
    cases value with
    | mk valueBound =>
      exact congrArg SpaceGrade.mk (Nat.zero_mul valueBound)

  mul_zero_right := fun value => by
    cases value with
    | mk valueBound =>
      exact congrArg SpaceGrade.mk (Nat.mul_zero valueBound)

  le_refl := fun value => Nat.le_refl value.bound

  le_trans := fun _ _ _ firstLeSecond secondLeThird =>
    Nat.le_trans firstLeSecond secondLeThird

  add_mono := fun _ _ _ _ leftLeq rightLeq =>
    Nat.add_le_add leftLeq rightLeq

  mul_mono := fun _ _ _ _ leftLeq rightLeq =>
    Nat.mul_le_mul leftLeq rightLeq

/-! ## Smoke samples -/

/-- Combining two checked space witnesses adds their bounds. -/
example :
    SpaceGrade.add ⟨2⟩ ⟨3⟩ = ⟨5⟩ := rfl

/-- Sequential scaling multiplies checked space witnesses. -/
example :
    SpaceGrade.mul ⟨2⟩ ⟨3⟩ = ⟨6⟩ := rfl

/-- Smaller space bounds subsume larger allowances. -/
example :
    SpaceGrade.le ⟨3⟩ ⟨5⟩ := by
  exact Nat.le.step (Nat.le.step (Nat.le_refl 3))

end LeanFX2.Graded.Instances
