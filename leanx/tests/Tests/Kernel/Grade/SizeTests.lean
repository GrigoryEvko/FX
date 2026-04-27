import FX.Kernel.Grade.Size

/-!
# Size dimension tests

Codata observation depth — `finite n | omega`.  `add` is `max`
(parallel branches take the worst case), `mul` is addition
(sequential destructor chaining), `omega` absorbs both.
-/

namespace Tests.Kernel.Grade.Size

open FX.Kernel
open FX.Kernel.Size

/-! ## add = max (finite-finite) / omega-absorbing -/

example : add (finite 0) (finite 0) = finite 0 := by native_decide
example : add (finite 3) (finite 5) = finite 5 := by native_decide
example : add (finite 5) (finite 3) = finite 5 := by native_decide
example : add (finite 7) (finite 7) = finite 7 := by native_decide

example : add omega (finite 100)    = omega := rfl
example : add (finite 100) omega    = omega := by native_decide
example : add omega omega           = omega := rfl

/-! ## mul = + (finite-finite) / omega-absorbing -/

example : mul (finite 0) (finite 0) = finite 0 := by native_decide
example : mul (finite 3) (finite 5) = finite 8 := by native_decide
example : mul (finite 5) (finite 3) = finite 8 := by native_decide

example : mul omega (finite 100)    = omega := rfl
example : mul (finite 100) omega    = omega := by native_decide
example : mul omega omega           = omega := rfl

/-! ## Subsumption

`finite 0` is the bottom, `omega` is the top, and `finite n ≤
finite m` iff `n ≤ m`.
-/

example : LessEq (finite 0) (finite 5)      := by decide
example : LessEq (finite 0) omega           := LessEq.finiteLeOmega _
example : LessEq (finite 5) omega           := LessEq.finiteLeOmega _
example : LessEq omega omega                := LessEq.omegaRefl
example : LessEq (finite 3) (finite 3)      := LessEq.refl _

example : ¬ LessEq omega (finite 100)       := by decide
example : ¬ LessEq (finite 5) (finite 3)    := by decide

/-! ## Laws -/

example : add (finite 3) (finite 5) = add (finite 5) (finite 3) := add_comm _ _
example : add omega (finite 5)      = add (finite 5) omega      := by native_decide

-- Associativity at a specific instance.
example : add (add (finite 2) (finite 4)) (finite 3)
            = add (finite 2) (add (finite 4) (finite 3)) := add_assoc _ _ _

-- `finite 0` acts as unit for `add` only up to max — since max
-- with anything non-zero gives the other, `finite 0` is the
-- neutral on the finite side; on the omega side, omega absorbs.
example : add (finite 0) (finite 5) = finite 5 := finite_zero_add _
example : add (finite 0) omega      = omega    := finite_zero_add _

-- `omega` is top.
example : le_omega (finite 100) = LessEq.finiteLeOmega _ := rfl
example : le_omega omega        = LessEq.omegaRefl      := rfl

end Tests.Kernel.Grade.Size
