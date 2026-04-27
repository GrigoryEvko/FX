import FX.Kernel.Grade.Space

/-!
# Space dimension tests

Declared-allocation budget; naturals with `+`.  Same algebraic
shape as Complexity — test surface mirrors ComplexityTests.
-/

namespace Tests.Kernel.Grade.Space

open FX.Kernel
open FX.Kernel.Space

/-! ## add = + (parallel branches' allocations sum) -/

example : add 0 0 = 0 := rfl
example : add 4096 0 = 4096 := rfl
example : add 0 4096 = 4096 := rfl
example : add 1024 2048 = 3072 := by decide
example : add 100 200 = 300 := by decide

/-! ## mul = + (sequential composition is additive) -/

example : mul 1024 2048 = 3072 := by decide

-- add = mul at all inputs — space is additive both ways.
example : add 512 1024 = mul 512 1024 := rfl

/-! ## LessEq is Nat.le -/

example : (0 : Space) ≤ 4096     := by decide
example : (4096 : Space) ≤ 4096  := by decide
example : ¬ ((4096 : Space) ≤ 100) := by decide

/-! ## Laws -/

example : add 1024 2048 = add 2048 1024 := add_comm _ _
example : add (add 256 512) 1024 = add 256 (add 512 1024) := add_assoc _ _ _
example : add 0 4096 = 4096 := zero_add _
example : add 4096 0 = 4096 := add_zero _

end Tests.Kernel.Grade.Space
