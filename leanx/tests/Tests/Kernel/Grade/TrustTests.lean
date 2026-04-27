import FX.Kernel.Grade.Trust

/-!
# Trust dimension tests
-/

namespace Tests.Kernel.Grade.Trust

open FX.Kernel
open FX.Kernel.Trust

/-! ## Rank values and injectivity -/

example : rank external = 0 := rfl
example : rank assumed  = 1 := rfl
example : rank sorryT   = 2 := rfl
example : rank tested   = 3 := rfl
example : rank verified = 4 := rfl

example : ∀ x : Trust, ofRank (rank x) = x := by intro x; cases x <;> rfl

/-- `rank` is injective — distinct constructors have distinct ranks. -/
example : ∀ {x y : Trust}, rank x = rank y → x = y := rank_injective

example : ∀ x y : Trust, x ≠ y → rank x ≠ rank y := by
  intro x y hxy hr
  exact hxy (rank_injective hr)

/-! ## Surface-syntax mapping (§10.6) — each level maps to a rank -/

-- "Verified" source maps to top of chain
example : rank verified = 4 := rfl
-- `extern "C"` / deserialization maps to bottom
example : rank external = 0 := rfl
-- `sorry` placeholder: dev-only, one step above raw `axiom`
example : rank sorryT = rank assumed + 1 := rfl
-- `@[tested]` sits between `sorryT` and `verified`
example : rank sorryT < rank tested := by decide
example : rank tested < rank verified := by decide

/-! ## Min-based combine: corner cells -/

example : add verified verified = verified := rfl
example : add verified external = external := rfl
example : add external verified = external := rfl
example : add tested   sorryT   = sorryT   := rfl
example : add assumed  external = external := rfl
example : add sorryT   assumed  = assumed  := rfl

/-! ## Idempotent commutative monoid laws -/

example : ∀ x y : Trust, add x y = add y x := by
  intro x y; cases x <;> cases y <;> rfl
example : ∀ x y z : Trust, add (add x y) z = add x (add y z) := by
  intro x y z; cases x <;> cases y <;> cases z <;> rfl
example : ∀ x : Trust, add x x = x := by intro x; cases x <;> rfl

example : ∀ x : Trust, add verified x = x := by intro x; cases x <;> rfl
example : ∀ x : Trust, add x verified = x := by intro x; cases x <;> rfl

example : ∀ x : Trust, add external x = external := by intro x; cases x <;> rfl
example : ∀ x : Trust, add x external = external := by intro x; cases x <;> rfl

example : ∀ x y z : Trust, mul (mul x y) z = mul x (mul y z) := by
  intro x y z; cases x <;> cases y <;> cases z <;> rfl
example : ∀ x : Trust, mul x x = x := by intro x; cases x <;> rfl
example : ∀ x : Trust, mul verified x = x := by intro x; cases x <;> rfl
example : ∀ x : Trust, mul x verified = x := by intro x; cases x <;> rfl

example : ∀ x y z : Trust, mul x (add y z) = add (mul x y) (mul x z) := by
  intro x y z; cases x <;> cases y <;> cases z <;> rfl
example : ∀ x y z : Trust, mul (add x y) z = add (mul x z) (mul y z) := by
  intro x y z; cases x <;> cases y <;> cases z <;> rfl

/-! ## LessEq preorder + antisymmetry = partial order -/

example : ∀ x : Trust, LessEq x x := LessEq.refl
example : ∀ x y z : Trust, LessEq x y → LessEq y z → LessEq x z :=
  fun _ _ _ => LessEq.trans
example : ∀ x y : Trust, LessEq x y → LessEq y x → x = y :=
  fun _ _ => LessEq.antisymm

/-! ## Strict chain ordering -/

example : LessEq external assumed := by decide
example : LessEq assumed  sorryT  := by decide
example : LessEq sorryT   tested  := by decide
example : LessEq tested   verified := by decide

/-! ## Negative cases — the chain is strict -/

example : ¬ LessEq verified tested   := by decide
example : ¬ LessEq verified external := by decide
example : ¬ LessEq tested   sorryT   := by decide
example : ¬ LessEq sorryT   assumed  := by decide
example : ¬ LessEq assumed  external := by decide

/-! ## Release-build rule witness — §10.6: every trust ≤ verified -/

example : ∀ x : Trust, LessEq x verified := le_verified
example : ∀ x : Trust, LessEq external x := external_le

/-! ## Monotonicity of `add` and `mul` -/

example : ∀ {lower upper} (fixedRight : Trust),
    LessEq lower upper → LessEq (add lower fixedRight) (add upper fixedRight) :=
  fun fixedRight => add_mono_left fixedRight
example : ∀ {lower upper} (fixedLeft : Trust),
    LessEq lower upper → LessEq (add fixedLeft lower) (add fixedLeft upper) :=
  fun fixedLeft => add_mono_right fixedLeft

end Tests.Kernel.Grade.Trust
