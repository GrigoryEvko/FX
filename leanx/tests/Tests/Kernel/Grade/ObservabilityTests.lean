import FX.Kernel.Grade.Observability

/-!
# Observability dimension tests
-/

namespace Tests.Kernel.Grade.Observability

open FX.Kernel
open FX.Kernel.Observability

/-! ## Add truth table -/

example : add opaq        opaq        = opaq := rfl
example : add opaq        transparent = opaq := rfl
example : add transparent opaq        = opaq := rfl
example : add transparent transparent = transparent := rfl

/-! ## Mul truth table (same as add) -/

example : mul opaq        opaq        = opaq := rfl
example : mul opaq        transparent = opaq := rfl
example : mul transparent opaq        = opaq := rfl
example : mul transparent transparent = transparent := rfl

/-! ## LessEq truth table -/

example : LessEq opaq opaq := by decide
example : LessEq opaq transparent := by decide
example : ¬ LessEq transparent opaq := by decide
example : LessEq transparent transparent := by decide

/-! ## Laws -/

example : ∀ x y : Observability, add x y = add y x := by
  intro x y; cases x <;> cases y <;> rfl
example : ∀ x y z : Observability,
    add (add x y) z = add x (add y z) := by
  intro x y z; cases x <;> cases y <;> cases z <;> rfl
example : ∀ x : Observability, add x x = x := by intro x; cases x <;> rfl
example : ∀ x : Observability, add transparent x = x := by
  intro x; cases x <;> rfl
example : ∀ x : Observability, add x transparent = x := by
  intro x; cases x <;> rfl

example : ∀ x : Observability, LessEq x x := LessEq.refl
example : ∀ x y z : Observability, LessEq x y → LessEq y z → LessEq x z :=
  fun _ _ _ => LessEq.trans

/-! ## CT enforcement witness

`with CT` demands `value ≤ opaq`.  An opaque value clears,
a transparent one does not. -/

example : LessEq opaq transparent := by decide
example : ¬ LessEq transparent opaq := by decide
-- Restated as the actual CT predicate: `grade ≤ opaq` is the
-- bound CT imposes.  Opaque passes; transparent fails.
example : LessEq opaq        opaq := by decide
example : ¬ LessEq transparent opaq := by decide

/-! ## Meet identity, distributivity, idempotence -/

example : ∀ x : Observability, add opaq x = opaq := Observability.add_opaq_left
example : ∀ x : Observability, add x opaq = opaq := Observability.add_opaq_right
example : ∀ x : Observability, mul x x = x := Observability.mul_idem

example : ∀ x y z : Observability,
    mul x (add y z) = add (mul x y) (mul x z) := by
  intro x y z; cases x <;> cases y <;> cases z <;> rfl
example : ∀ x y z : Observability,
    mul (add x y) z = add (mul x z) (mul y z) := by
  intro x y z; cases x <;> cases y <;> cases z <;> rfl

/-! ## Antisymmetry and bounded-lattice witnesses -/

example : ∀ x y : Observability, LessEq x y → LessEq y x → x = y :=
  fun _ _ => Observability.LessEq.antisymm

example : ∀ x : Observability, x ≤ transparent := Observability.le_transparent
example : ∀ x : Observability, opaq ≤ x := Observability.opaq_le

/-! ## Monotonicity -/

example : ∀ x x' y : Observability, LessEq x x' → LessEq (add x y) (add x' y) :=
  fun _ _ y h => Observability.add_mono_left y h

/-! ## Decidability sanity checks -/

example : (decide (LessEq opaq transparent) : Bool) = true := rfl
example : (decide (LessEq transparent opaq) : Bool) = false := rfl

/-! ## Surface-mapping witnesses -/

-- default = opaq
example : (opaq : Observability) = Observability.opaq := rfl
-- `transparent` grant
example : (transparent : Observability) = Observability.transparent := rfl

end Tests.Kernel.Grade.Observability
