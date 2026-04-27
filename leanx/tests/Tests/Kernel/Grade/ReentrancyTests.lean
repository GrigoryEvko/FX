import FX.Kernel.Grade.Reentrancy

/-!
# Reentrancy dimension tests
-/

namespace Tests.Kernel.Grade.Reentrancy

open FX.Kernel
open FX.Kernel.Reentrancy

/-! ## Add truth table -/

example : add nonReentrant nonReentrant = nonReentrant := rfl
example : add nonReentrant reentrant    = reentrant    := rfl
example : add reentrant    nonReentrant = reentrant    := rfl
example : add reentrant    reentrant    = reentrant    := rfl

/-! ## Mul truth table -/

example : mul nonReentrant nonReentrant = nonReentrant := rfl
example : mul nonReentrant reentrant    = reentrant    := rfl
example : mul reentrant    nonReentrant = reentrant    := rfl
example : mul reentrant    reentrant    = reentrant    := rfl

/-! ## LessEq truth table -/

example : LessEq nonReentrant nonReentrant := by decide
example : LessEq nonReentrant reentrant    := by decide
example : ¬ LessEq reentrant  nonReentrant := by decide
example : LessEq reentrant    reentrant    := by decide

/-! ## Laws -/

example : ∀ x y : Reentrancy, add x y = add y x := by
  intro x y; cases x <;> cases y <;> rfl
example : ∀ x y z : Reentrancy, add (add x y) z = add x (add y z) := by
  intro x y z; cases x <;> cases y <;> cases z <;> rfl
example : ∀ x : Reentrancy, add x x = x := by intro x; cases x <;> rfl
example : ∀ x : Reentrancy, add nonReentrant x = x := by intro x; cases x <;> rfl
example : ∀ x : Reentrancy, add x nonReentrant = x := by intro x; cases x <;> rfl

example : ∀ x : Reentrancy, LessEq x x := LessEq.refl
example : ∀ x y z : Reentrancy, LessEq x y → LessEq y z → LessEq x z :=
  fun _ _ _ => LessEq.trans

/-! ## Antisymmetry and bounded-lattice witnesses -/

example : ∀ x y : Reentrancy, LessEq x y → LessEq y x → x = y :=
  fun _ _ => Reentrancy.LessEq.antisymm
example : ∀ x : Reentrancy, x ≤ reentrant := Reentrancy.le_reentrant
example : ∀ x : Reentrancy, nonReentrant ≤ x := Reentrancy.nonReentrant_le

/-! ## Grant propagation — `reentrant` absorbs into `add` -/

example : ∀ x : Reentrancy, add reentrant x = reentrant :=
  Reentrancy.add_reentrant_left
example : ∀ x : Reentrancy, add x reentrant = reentrant :=
  Reentrancy.add_reentrant_right

/-! ## Monotonicity, idempotence, distributivity -/

example : ∀ x x' y : Reentrancy, LessEq x x' → LessEq (add x y) (add x' y) :=
  fun _ _ y h => Reentrancy.add_mono_left y h
example : ∀ x : Reentrancy, mul x x = x := Reentrancy.mul_idem
example : ∀ x y z : Reentrancy,
    mul x (add y z) = add (mul x y) (mul x z) := by
  intro x y z; cases x <;> cases y <;> cases z <;> rfl
example : ∀ x y z : Reentrancy,
    mul (add x y) z = add (mul x z) (mul y z) := by
  intro x y z; cases x <;> cases y <;> cases z <;> rfl

/-! ## Decidability sanity checks -/

example : (decide (LessEq nonReentrant reentrant) : Bool) = true := rfl
example : (decide (LessEq reentrant nonReentrant) : Bool) = false := rfl

/-! ## Surface-mapping witnesses

Per §6.3 dim 19 and §5.2: default = nonReentrant, `rec` / `with
Reentrant` = reentrant. -/

example : (nonReentrant : Reentrancy) = Reentrancy.nonReentrant := rfl
example : (reentrant    : Reentrancy) = Reentrancy.reentrant    := rfl

end Tests.Kernel.Grade.Reentrancy
