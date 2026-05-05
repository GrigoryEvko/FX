import LeanFX2.Graded.Instances.NatResource

/-! # Graded/Instances/Complexity — asymptotic cost-bound semiring

`ComplexityGrade` tracks an erased natural cost bound for the
complexity dimension.  The carrier is a wrapper around `Nat` so the
dimension remains distinct from other numeric resources in grade
vectors.

Operations use the ordinary natural-number semiring:

* `0` = zero cost
* `1` = unit cost
* `+` = parallel/combined cost
* `*` = sequential scaling
* `≤` = cost-bound subsumption

This models the kernel-side algebra needed by graded typing rules.
Surface-level Big-O notation and solver-backed asymptotic comparison
belong in the elaborator; the core dimension records the checked
natural witness.

Zero-axiom verified per declaration. -/

namespace LeanFX2.Graded.Instances

open LeanFX2.Graded

/-- Complexity grade: natural cost bound, kept as a distinct wrapper
from other numeric grade dimensions. -/
structure ComplexityGrade : Type where
  /-- The checked natural cost witness. -/
  bound : Nat
  deriving DecidableEq, Repr

namespace ComplexityGrade

/-- Parallel composition adds cost bounds. -/
def add (first second : ComplexityGrade) : ComplexityGrade :=
  ⟨first.bound + second.bound⟩

/-- Sequential composition multiplies cost bounds. -/
def mul (first second : ComplexityGrade) : ComplexityGrade :=
  ⟨first.bound * second.bound⟩

/-- Cost-bound subsumption. -/
def le (first second : ComplexityGrade) : Prop :=
  first.bound ≤ second.bound

end ComplexityGrade

/-- Complexity cost bounds form the natural-number semiring with
the usual order.  Proofs reduce to the corresponding `Nat` laws. -/
instance : GradeSemiring ComplexityGrade where
  zero := ⟨0⟩
  one  := ⟨1⟩
  add  := ComplexityGrade.add
  mul  := ComplexityGrade.mul
  le   := ComplexityGrade.le

  add_assoc := fun first second third => by
    cases first with
    | mk firstBound =>
    cases second with
    | mk secondBound =>
    cases third with
    | mk thirdBound =>
      exact congrArg ComplexityGrade.mk
        (Nat.add_assoc firstBound secondBound thirdBound)

  add_comm := fun first second => by
    cases first with
    | mk firstBound =>
    cases second with
    | mk secondBound =>
      exact congrArg ComplexityGrade.mk (Nat.add_comm firstBound secondBound)

  add_zero_left := fun value => by
    cases value with
    | mk valueBound =>
      exact congrArg ComplexityGrade.mk (Nat.zero_add valueBound)

  add_zero_right := fun value => by
    cases value with
    | mk valueBound =>
      exact congrArg ComplexityGrade.mk (Nat.add_zero valueBound)

  mul_assoc := fun first second third => by
    cases first with
    | mk firstBound =>
    cases second with
    | mk secondBound =>
    cases third with
    | mk thirdBound =>
      exact congrArg ComplexityGrade.mk
        (NatResource.mulAssocClean firstBound secondBound thirdBound)

  mul_one_left := fun value => by
    cases value with
    | mk valueBound =>
      exact congrArg ComplexityGrade.mk (Nat.one_mul valueBound)

  mul_one_right := fun value => by
    cases value with
    | mk valueBound =>
      exact congrArg ComplexityGrade.mk (Nat.mul_one valueBound)

  mul_distrib_left := fun scalar leftAddend rightAddend => by
    cases scalar with
    | mk scalarBound =>
    cases leftAddend with
    | mk leftBound =>
    cases rightAddend with
    | mk rightBound =>
      exact congrArg ComplexityGrade.mk
        (Nat.left_distrib scalarBound leftBound rightBound)

  mul_distrib_right := fun leftAddend rightAddend scalar => by
    cases leftAddend with
    | mk leftBound =>
    cases rightAddend with
    | mk rightBound =>
    cases scalar with
    | mk scalarBound =>
      exact congrArg ComplexityGrade.mk
        (NatResource.mulRightDistribClean leftBound rightBound scalarBound)

  mul_zero_left := fun value => by
    cases value with
    | mk valueBound =>
      exact congrArg ComplexityGrade.mk (Nat.zero_mul valueBound)

  mul_zero_right := fun value => by
    cases value with
    | mk valueBound =>
      exact congrArg ComplexityGrade.mk (Nat.mul_zero valueBound)

  le_refl := fun value => Nat.le_refl value.bound

  le_trans := fun first second third firstLeSecond secondLeThird =>
    Nat.le_trans firstLeSecond secondLeThird

  add_mono := fun _ _ _ _ leftLeq rightLeq =>
    Nat.add_le_add leftLeq rightLeq

  mul_mono := fun _ _ _ _ leftLeq rightLeq =>
    Nat.mul_le_mul leftLeq rightLeq

/-! ## Smoke samples -/

/-- Combining two checked cost witnesses adds their bounds. -/
example :
    ComplexityGrade.add ⟨2⟩ ⟨3⟩ = ⟨5⟩ := rfl

/-- Sequential scaling multiplies checked cost witnesses. -/
example :
    ComplexityGrade.mul ⟨2⟩ ⟨3⟩ = ⟨6⟩ := rfl

/-- Smaller cost bounds subsume larger allowances. -/
example :
    ComplexityGrade.le ⟨3⟩ ⟨5⟩ := by
  exact Nat.le.step (Nat.le.step (Nat.le_refl 3))

end LeanFX2.Graded.Instances
