import FX.Kernel.Grade.Mutation

/-!
# Mutation dimension tests
-/

namespace Tests.Kernel.Grade.Mutation

open FX.Kernel
open FX.Kernel.Mutation

/-! ## Rank injectivity -/

example : rank immutable  = 0 := rfl
example : rank appendOnly = 1 := rfl
example : rank monotonic  = 2 := rfl
example : rank readWrite  = 3 := rfl

example : ∀ x : Mutation, ofRank (rank x) = x := by intro x; cases x <;> rfl

/-! ## Add corner cells -/

example : add immutable  immutable  = immutable  := rfl
example : add immutable  readWrite  = readWrite  := rfl
example : add readWrite  immutable  = readWrite  := rfl
example : add readWrite  readWrite  = readWrite  := rfl
example : add appendOnly monotonic  = monotonic  := rfl
example : add monotonic  appendOnly = monotonic  := rfl

/-! ## Laws -/

example : ∀ x y : Mutation, add x y = add y x := by
  intro x y; cases x <;> cases y <;> rfl
example : ∀ x y z : Mutation, add (add x y) z = add x (add y z) := by
  intro x y z; cases x <;> cases y <;> cases z <;> rfl
example : ∀ x : Mutation, add x x = x := by intro x; cases x <;> rfl

example : ∀ x : Mutation, add immutable x = x := by intro x; cases x <;> rfl
example : ∀ x : Mutation, add x immutable = x := by intro x; cases x <;> rfl

example : ∀ x : Mutation, add readWrite x = readWrite := by
  intro x; cases x <;> rfl
example : ∀ x : Mutation, add x readWrite = readWrite := by
  intro x; cases x <;> rfl

/-! ## LessEq — strict chain -/

example : LessEq immutable  appendOnly := by decide
example : LessEq appendOnly monotonic  := by decide
example : LessEq monotonic  readWrite  := by decide
example : LessEq immutable  readWrite  := by decide

example : ¬ LessEq readWrite monotonic  := by decide
example : ¬ LessEq readWrite immutable  := by decide
example : ¬ LessEq monotonic appendOnly := by decide

example : ∀ x : Mutation, LessEq x x := LessEq.refl
example : ∀ x y z : Mutation, LessEq x y → LessEq y z → LessEq x z :=
  fun _ _ _ => LessEq.trans

/-! ## Subsumption witness -/

example : ∀ x : Mutation, LessEq immutable x := by intro x; cases x <;> decide
example : ∀ x : Mutation, LessEq x readWrite := by intro x; cases x <;> decide

end Tests.Kernel.Grade.Mutation
