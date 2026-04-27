import FX.Kernel.Grade.Precision

/-!
# Precision dimension tests

Declared ULP error bound; naturals with `+`.  Same algebraic
shape as Complexity — test surface mirrors ComplexityTests.
-/

namespace Tests.Kernel.Grade.Precision

open FX.Kernel
open FX.Kernel.Precision

/-! ## add = + (parallel branches' errors sum) -/

example : add 0 0 = 0 := rfl
example : add 0 5 = 5 := rfl
example : add 5 0 = 5 := rfl
example : add 3 4 = 7 := rfl
example : add 100 50 = 150 := by decide

/-! ## mul = + (sequential composition accumulates ULPs) -/

example : mul 0 0 = 0 := rfl
example : mul 5 3 = 8 := by decide
example : mul 100 50 = 150 := by decide

-- add = mul at all inputs — both accumulate error additively.
example : add 42 17 = mul 42 17 := rfl

/-! ## LessEq is Nat.le — tighter bound stands in for looser -/

example : (0 : Precision) ≤ 0    := by decide
example : (0 : Precision) ≤ 100  := by decide
example : (42 : Precision) ≤ 42  := by decide
example : ¬ ((10 : Precision) ≤ 5) := by decide
example : (5 : Precision) ≤ 10   := by decide

/-! ## Laws -/

example : add 3 4 = add 4 3 := add_comm _ _
example : add (add 1 2) 3 = add 1 (add 2 3) := add_assoc _ _ _
example : add 0 7 = 7 := zero_add _
example : add 7 0 = 7 := add_zero _

end Tests.Kernel.Grade.Precision
