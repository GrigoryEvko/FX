import FX.Kernel.Grade.FpOrder

/-!
# FP order dimension tests
-/

namespace Tests.Kernel.Grade.FpOrder

open FX.Kernel
open FX.Kernel.FpOrder

/-! ## Add truth table -/

example : add strict      strict      = strict       := rfl
example : add strict      reassociate = reassociate  := rfl
example : add reassociate strict      = reassociate  := rfl
example : add reassociate reassociate = reassociate  := rfl

/-! ## Mul truth table -/

example : mul strict      strict      = strict       := rfl
example : mul strict      reassociate = reassociate  := rfl
example : mul reassociate strict      = reassociate  := rfl
example : mul reassociate reassociate = reassociate  := rfl

/-! ## LessEq truth table -/

example : LessEq strict strict := by decide
example : LessEq strict reassociate := by decide
example : ¬ LessEq reassociate strict := by decide
example : LessEq reassociate reassociate := by decide

/-! ## Laws -/

example : ∀ x y : FpOrder, add x y = add y x := by
  intro x y; cases x <;> cases y <;> rfl
example : ∀ x y z : FpOrder, add (add x y) z = add x (add y z) := by
  intro x y z; cases x <;> cases y <;> cases z <;> rfl
example : ∀ x : FpOrder, add x x = x := by intro x; cases x <;> rfl
example : ∀ x : FpOrder, add strict x = x := by intro x; cases x <;> rfl
example : ∀ x : FpOrder, add x strict = x := by intro x; cases x <;> rfl

example : ∀ x : FpOrder, LessEq x x := LessEq.refl
example : ∀ x y z : FpOrder, LessEq x y → LessEq y z → LessEq x z :=
  fun _ _ _ => LessEq.trans

/-! ## Antisymmetry and bounded-lattice witnesses -/

example : ∀ x y : FpOrder, LessEq x y → LessEq y x → x = y :=
  fun _ _ => FpOrder.LessEq.antisymm
example : ∀ x : FpOrder, x ≤ reassociate := FpOrder.le_reassociate
example : ∀ x : FpOrder, strict ≤ x := FpOrder.strict_le

/-! ## Grant propagation — `reassociate` absorbs into `add` -/

example : ∀ x : FpOrder, add reassociate x = reassociate :=
  FpOrder.add_reassociate_left
example : ∀ x : FpOrder, add x reassociate = reassociate :=
  FpOrder.add_reassociate_right

/-! ## Monotonicity, idempotence, distributivity -/

example : ∀ x x' y : FpOrder, LessEq x x' → LessEq (add x y) (add x' y) :=
  fun _ _ y h => FpOrder.add_mono_left y h
example : ∀ x : FpOrder, mul x x = x := FpOrder.mul_idem
example : ∀ x y z : FpOrder,
    mul x (add y z) = add (mul x y) (mul x z) := by
  intro x y z; cases x <;> cases y <;> cases z <;> rfl
example : ∀ x y z : FpOrder,
    mul (add x y) z = add (mul x z) (mul y z) := by
  intro x y z; cases x <;> cases y <;> cases z <;> rfl

/-! ## Decidability sanity checks -/

example : (decide (LessEq strict reassociate) : Bool) = true := rfl
example : (decide (LessEq reassociate strict) : Bool) = false := rfl

/-! ## Surface-mapping witnesses -/

example : (strict      : FpOrder) = FpOrder.strict      := rfl
example : (reassociate : FpOrder) = FpOrder.reassociate := rfl

end Tests.Kernel.Grade.FpOrder
