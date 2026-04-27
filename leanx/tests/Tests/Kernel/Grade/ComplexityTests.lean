import FX.Kernel.Grade.Complexity

/-!
# Complexity dimension tests

Declared-operation-count budget; naturals with `+`.  Verifies
the add/mul/LessEq shape matches the documented algebra.
-/

namespace Tests.Kernel.Grade.Complexity

open FX.Kernel
open FX.Kernel.Complexity

/-! ## add = + -/

example : add 0 0 = 0 := rfl
example : add 0 5 = 5 := rfl
example : add 5 0 = 5 := rfl
example : add 3 4 = 7 := rfl
example : add 100 50 = 150 := by decide

/-! ## mul = + (sequential composition of costs is additive) -/

example : mul 0 0 = 0 := rfl
example : mul 5 3 = 8 := by decide
example : mul 100 50 = 150 := by decide

-- Sanity: add and mul produce the same result.
example : add 42 17 = mul 42 17 := rfl

/-! ## LessEq is Nat.le -/

example : (0 : Complexity) ≤ 0     := by decide
example : (0 : Complexity) ≤ 100   := by decide
example : (42 : Complexity) ≤ 42   := by decide
example : ¬ ((10 : Complexity) ≤ 5)  := by decide
example : (5 : Complexity) ≤ 10    := by decide

/-! ## Laws -/

example : add 3 4 = add 4 3 := add_comm _ _
example : add (add 1 2) 3 = add 1 (add 2 3) := add_assoc _ _ _
example : add 0 7 = 7 := zero_add _
example : add 7 0 = 7 := add_zero _

end Tests.Kernel.Grade.Complexity
