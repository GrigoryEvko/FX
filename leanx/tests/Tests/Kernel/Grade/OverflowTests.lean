import FX.Kernel.Grade.Overflow

/-!
# Overflow dimension tests
-/

namespace Tests.Kernel.Grade.Overflow

open FX.Kernel
open FX.Kernel.Overflow

/-! ## Add truth table — 16 cells -/

example : add exact    exact    = some exact    := rfl
example : add exact    wrap     = some wrap     := rfl
example : add exact    trap     = some trap     := rfl
example : add exact    saturate = some saturate := rfl

example : add wrap     exact    = some wrap     := rfl
example : add wrap     wrap     = some wrap     := rfl
example : add wrap     trap     = none          := rfl
example : add wrap     saturate = none          := rfl

example : add trap     exact    = some trap     := rfl
example : add trap     wrap     = none          := rfl
example : add trap     trap     = some trap     := rfl
example : add trap     saturate = none          := rfl

example : add saturate exact    = some saturate := rfl
example : add saturate wrap     = none          := rfl
example : add saturate trap     = none          := rfl
example : add saturate saturate = some saturate := rfl

/-! ## Mul truth table (same as add) -/

example : mul exact wrap = some wrap := rfl
example : mul wrap trap  = none      := rfl

/-! ## LessEq -/

example : LessEq exact    exact    := by decide
example : LessEq exact    wrap     := by decide
example : LessEq exact    trap     := by decide
example : LessEq exact    saturate := by decide

example : ¬ LessEq wrap     exact := by decide
example : ¬ LessEq wrap     trap  := by decide
example : ¬ LessEq wrap     saturate := by decide
example : LessEq wrap       wrap  := by decide

example : ¬ LessEq trap     wrap     := by decide
example : ¬ LessEq saturate wrap     := by decide
example : ¬ LessEq trap     saturate := by decide

/-! ## Laws -/

example : ∀ x y : Overflow, add x y = add y x := by
  intro x y; cases x <;> cases y <;> rfl

example : ∀ x : Overflow, add exact x = some x := by
  intro x; cases x <;> rfl
example : ∀ x : Overflow, add x exact = some x := by
  intro x; cases x <;> rfl

example : ∀ x : Overflow, add x x = some x := by
  intro x; cases x <;> rfl

/-! ## LessEq preorder -/

example : ∀ x : Overflow, LessEq x x := LessEq.refl
example : ∀ x y z : Overflow, LessEq x y → LessEq y z → LessEq x z :=
  fun _ _ _ => LessEq.trans

/-! ## Validity

`valid` is declared as `Prop` but unfolds to `Option.isSome`.
We assert the underlying boolean to avoid Decidable-instance
synthesis. -/

example : (add exact wrap).isSome = true := rfl
example : (add wrap trap).isSome = false := rfl

/-! ## Negative cases for the partial op (cross-top mixing)

Every cross-discipline pair MUST fail validity.  These six
failure cells are the `T047`-equivalent compile errors the
design gap (gaps.json) identifies for Overflow. -/

example : (add wrap     trap    ).isSome = false := rfl
example : (add wrap     saturate).isSome = false := rfl
example : (add trap     wrap    ).isSome = false := rfl
example : (add trap     saturate).isSome = false := rfl
example : (add saturate wrap    ).isSome = false := rfl
example : (add saturate trap    ).isSome = false := rfl

/-- `mul` has the same invalid cells as `add` (they are defeq). -/
example : (mul wrap     trap    ).isSome = false := rfl
example : (mul trap     saturate).isSome = false := rfl
example : (mul saturate wrap    ).isSome = false := rfl

/-- `exact` is never a source of invalidity — joining with `exact`
    always succeeds.  Seven positive cells complementing the six
    failures above. -/
example : (add exact    exact   ).isSome = true := rfl
example : (add exact    wrap    ).isSome = true := rfl
example : (add exact    trap    ).isSome = true := rfl
example : (add exact    saturate).isSome = true := rfl
example : (add wrap     exact   ).isSome = true := rfl
example : (add trap     exact   ).isSome = true := rfl
example : (add saturate exact   ).isSome = true := rfl

/-! ## Partial-order antisymmetry -/

example : ∀ x y : Overflow, LessEq x y → LessEq y x → x = y :=
  fun _ _ => LessEq.antisymm

example : LessEq.antisymm (LessEq.refl wrap) (LessEq.refl wrap) = rfl := rfl

example : ∀ x : Overflow, LessEq exact x := exact_le

end Tests.Kernel.Grade.Overflow
