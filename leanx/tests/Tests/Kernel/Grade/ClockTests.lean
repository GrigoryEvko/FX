import FX.Kernel.Grade.Clock

/-!
# Clock dimension tests

Exercise the partial join and the subsumption preorder on the
`combinational | sync(clkName)` carrier per `fx_design.md` §6.3
dim 12 + §18.7.  Since `sync` carries a `String` the tests pick
a handful of representative clock names; the algebra is uniform
across names, so two distinct names are enough to cover the
cross-domain rejection case.
-/

namespace Tests.Kernel.Grade.Clock

open FX.Kernel
open FX.Kernel.Clock

/-! ## Add truth table — the important cells -/

-- combinational is unit on both sides.
example : add combinational combinational = some combinational := rfl
example : add combinational (sync "clk_a") = some (sync "clk_a") := rfl
example : add (sync "clk_a") combinational = some (sync "clk_a") := rfl

-- Same clock: idempotent.
example : add (sync "clk_a") (sync "clk_a") = some (sync "clk_a") := by
  native_decide

-- Distinct clocks: cross-domain rejection (CD001).
example : add (sync "clk_a") (sync "clk_b") = none := by native_decide
example : add (sync "sys")   (sync "io")    = none := by native_decide

/-! ## Mul is the same partial join -/

example : mul combinational (sync "clk_a") = some (sync "clk_a") := rfl
example : mul (sync "clk_a") (sync "clk_a") = some (sync "clk_a") := by
  native_decide
example : mul (sync "clk_a") (sync "clk_b") = none := by native_decide

/-! ## Subsumption -/

-- combinational is bottom — below every clock.
example : LessEq combinational combinational         := LessEq.refl _
example : LessEq combinational (sync "clk_a")        := LessEq.combinationalLe _
example : LessEq combinational (sync "any_other")    := LessEq.combinationalLe _

-- sync reflects only to itself.
example : LessEq (sync "clk_a") (sync "clk_a")       := LessEq.refl _
example : ¬ LessEq (sync "clk_a") combinational      := by decide
example : ¬ LessEq (sync "clk_a") (sync "clk_b")     := by decide

/-! ## Commutativity / idempotence laws -/

example : add (sync "clk") combinational = add combinational (sync "clk") := by
  native_decide

-- The add_idem theorem holds for a specific clock — invoke it
-- as a proof.  This is about the theorem's type-checking, not a
-- runtime assertion.
example : add (sync "clk") (sync "clk") = some (sync "clk") := add_idem _

-- Combinational + combinational = combinational (double-unit case).
example : add combinational combinational = some combinational := rfl

/-! ## sync-sync-none symmetry

Two distinct clocks cannot combine, regardless of order — a
specific instance of `sync_sync_none_iff`. -/

example : add (sync "a") (sync "b") = none := by native_decide
example : add (sync "b") (sync "a") = none := by native_decide

end Tests.Kernel.Grade.Clock
