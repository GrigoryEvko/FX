import FX.Kernel.Grade.Security

/-!
# Security dimension tests

Compile-time proofs covering `fx_design.md` §6.3 dim 5.
-/

namespace Tests.Kernel.Grade.Security

open FX.Kernel
open FX.Kernel.Security

/-! ## Add truth table -/

example : add unclassified unclassified = unclassified := rfl
example : add unclassified classified   = classified   := rfl
example : add classified   unclassified = classified   := rfl
example : add classified   classified   = classified   := rfl

/-! ## Mul truth table -/

example : mul unclassified unclassified = unclassified := rfl
example : mul unclassified classified   = classified   := rfl
example : mul classified   unclassified = classified   := rfl
example : mul classified   classified   = classified   := rfl

/-! ## LessEq truth table -/

example : LessEq unclassified unclassified := LessEq.refl _
example : LessEq unclassified classified   := LessEq.botLe
example : ¬ LessEq classified unclassified := fun absurdityProof => by cases absurdityProof
example : LessEq classified   classified   := LessEq.refl _

/-! ## Idempotent commutative monoid laws -/

example : ∀ x y : Security, add x y = add y x := by
  intro x y; cases x <;> cases y <;> rfl
example : ∀ x y z : Security, add (add x y) z = add x (add y z) := by
  intro x y z; cases x <;> cases y <;> cases z <;> rfl
example : ∀ x : Security, add x x = x := by intro x; cases x <;> rfl
example : ∀ x : Security, add unclassified x = x := by intro x; cases x <;> rfl
example : ∀ x : Security, add x unclassified = x := by intro x; cases x <;> rfl

example : ∀ x y z : Security, mul (mul x y) z = mul x (mul y z) := by
  intro x y z; cases x <;> cases y <;> cases z <;> rfl
example : ∀ x : Security, mul unclassified x = x := by intro x; cases x <;> rfl
example : ∀ x : Security, mul x unclassified = x := by intro x; cases x <;> rfl

example : ∀ x y z : Security, mul x (add y z) = add (mul x y) (mul x z) := by
  intro x y z; cases x <;> cases y <;> cases z <;> rfl
example : ∀ x y z : Security, mul (add x y) z = add (mul x z) (mul y z) := by
  intro x y z; cases x <;> cases y <;> cases z <;> rfl

/-! ## LessEq preorder -/

example : ∀ x : Security, LessEq x x := LessEq.refl
example : ∀ x y z : Security, LessEq x y → LessEq y z → LessEq x z :=
  fun _ _ _ => LessEq.trans

/-! ## Noninterference direction

Classified data does NOT subsume unclassified — the core
invariant of §12.2. -/

example : ¬ LessEq classified unclassified := fun absurdityProof => by cases absurdityProof

/-! ## Antisymmetry — `LessEq` is a partial order -/

example : ∀ x y : Security, LessEq x y → LessEq y x → x = y :=
  fun _ _ => Security.LessEq.antisymm

/-! ## Bounded lattice witnesses -/

example : ∀ x : Security, x ≤ classified := Security.le_classified
example : ∀ x : Security, unclassified ≤ x := Security.unclassified_le

/-! ## Monotonicity -/

example : ∀ x x' y : Security, LessEq x x' → LessEq (add x y) (add x' y) :=
  fun _ _ y h => Security.add_mono_left y h

/-! ## `classified` absorption — the high-water-mark rule -/

example : ∀ x : Security, add classified x = classified :=
  Security.add_classified_left
example : ∀ x : Security, add x classified = classified :=
  Security.add_classified_right

/-! ## Decidability sanity checks

`decLe` is a manual instance; these samples confirm it resolves
at the top level so `decide` calls above work. -/

example : (decide (LessEq unclassified classified) : Bool) = true := rfl
example : (decide (LessEq classified unclassified) : Bool) = false := rfl

/-! ## Surface-mapping witnesses

`unclassified` and `secret x` / default map to the two carrier
elements per §12.1 and `Security.lean` docstring. -/

example : (unclassified : Security) = Security.unclassified := rfl
example : (classified   : Security) = Security.classified   := rfl

end Tests.Kernel.Grade.Security
