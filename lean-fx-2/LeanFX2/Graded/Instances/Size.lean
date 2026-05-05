import LeanFX2.Graded.Instances.NatResource

/-! # Graded/Instances/Size — codata observation-depth semiring

`SizeGrade` tracks an erased natural observation-depth bound for
codata productivity.  The carrier wraps `Nat` so the size dimension
remains distinct from complexity and space even though all three use
the same axiom-clean numeric resource algebra.

Operations use the ordinary natural-number semiring:

* `0` = no observation
* `1` = one observation step
* `+` = combined observation demand
* `*` = sequential scaling of observation demand
* `≤` = depth-bound subsumption

Zero-axiom verified per declaration. -/

namespace LeanFX2.Graded.Instances

open LeanFX2.Graded

/-- Size grade: natural codata observation-depth bound. -/
structure SizeGrade : Type where
  /-- The checked natural observation-depth witness. -/
  bound : Nat
  deriving DecidableEq, Repr

namespace SizeGrade

/-- Parallel composition adds observation-depth bounds. -/
def add (first second : SizeGrade) : SizeGrade :=
  ⟨first.bound + second.bound⟩

/-- Sequential composition multiplies observation-depth bounds. -/
def mul (first second : SizeGrade) : SizeGrade :=
  ⟨first.bound * second.bound⟩

/-- Observation-depth subsumption. -/
def le (first second : SizeGrade) : Prop :=
  first.bound ≤ second.bound

end SizeGrade

/-- Codata observation depth forms the natural-number semiring with
the usual order.  Multiplication associativity and right
distributivity use local axiom-clean Nat lemmas. -/
instance : GradeSemiring SizeGrade where
  zero := ⟨0⟩
  one  := ⟨1⟩
  add  := SizeGrade.add
  mul  := SizeGrade.mul
  le   := SizeGrade.le

  add_assoc := fun first second third => by
    cases first with
    | mk firstBound =>
    cases second with
    | mk secondBound =>
    cases third with
    | mk thirdBound =>
      exact congrArg SizeGrade.mk
        (Nat.add_assoc firstBound secondBound thirdBound)

  add_comm := fun first second => by
    cases first with
    | mk firstBound =>
    cases second with
    | mk secondBound =>
      exact congrArg SizeGrade.mk (Nat.add_comm firstBound secondBound)

  add_zero_left := fun value => by
    cases value with
    | mk valueBound =>
      exact congrArg SizeGrade.mk (Nat.zero_add valueBound)

  add_zero_right := fun value => by
    cases value with
    | mk valueBound =>
      exact congrArg SizeGrade.mk (Nat.add_zero valueBound)

  mul_assoc := fun first second third => by
    cases first with
    | mk firstBound =>
    cases second with
    | mk secondBound =>
    cases third with
    | mk thirdBound =>
      exact congrArg SizeGrade.mk
        (NatResource.mulAssocClean firstBound secondBound thirdBound)

  mul_one_left := fun value => by
    cases value with
    | mk valueBound =>
      exact congrArg SizeGrade.mk (Nat.one_mul valueBound)

  mul_one_right := fun value => by
    cases value with
    | mk valueBound =>
      exact congrArg SizeGrade.mk (Nat.mul_one valueBound)

  mul_distrib_left := fun scalar leftAddend rightAddend => by
    cases scalar with
    | mk scalarBound =>
    cases leftAddend with
    | mk leftBound =>
    cases rightAddend with
    | mk rightBound =>
      exact congrArg SizeGrade.mk
        (Nat.left_distrib scalarBound leftBound rightBound)

  mul_distrib_right := fun leftAddend rightAddend scalar => by
    cases leftAddend with
    | mk leftBound =>
    cases rightAddend with
    | mk rightBound =>
    cases scalar with
    | mk scalarBound =>
      exact congrArg SizeGrade.mk
        (NatResource.mulRightDistribClean leftBound rightBound scalarBound)

  mul_zero_left := fun value => by
    cases value with
    | mk valueBound =>
      exact congrArg SizeGrade.mk (Nat.zero_mul valueBound)

  mul_zero_right := fun value => by
    cases value with
    | mk valueBound =>
      exact congrArg SizeGrade.mk (Nat.mul_zero valueBound)

  le_refl := fun value => Nat.le_refl value.bound

  le_trans := fun _ _ _ firstLeSecond secondLeThird =>
    Nat.le_trans firstLeSecond secondLeThird

  add_mono := fun _ _ _ _ leftLeq rightLeq =>
    Nat.add_le_add leftLeq rightLeq

  mul_mono := fun _ _ _ _ leftLeq rightLeq =>
    Nat.mul_le_mul leftLeq rightLeq

/-! ## Smoke samples -/

/-- Combining two checked observation-depth witnesses adds them. -/
example :
    SizeGrade.add ⟨2⟩ ⟨3⟩ = ⟨5⟩ := rfl

/-- Sequential scaling multiplies checked observation-depth witnesses. -/
example :
    SizeGrade.mul ⟨2⟩ ⟨3⟩ = ⟨6⟩ := rfl

/-- Smaller observation-depth bounds subsume larger allowances. -/
example :
    SizeGrade.le ⟨3⟩ ⟨5⟩ := by
  exact Nat.le.step (Nat.le.step (Nat.le_refl 3))

end LeanFX2.Graded.Instances
