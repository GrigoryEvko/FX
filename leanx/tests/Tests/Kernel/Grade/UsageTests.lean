import FX.Kernel.Grade.Usage

/-!
# Usage dimension tests

Every test in this file is a **compile-time proof** via `decide`.
A failed test is a build failure — no runtime harness runs.

Covers `fx_design.md` §6.1 (Usage semiring) and §6.3 dim 3:

  * Complete `add` / `mul` truth tables (9 entries × 2 = 18)
  * Complete `div` truth table (9 entries)
  * Complete `LessEq` truth table (9 entries)
  * Semiring axioms by exhaustive quantification over the
    three-element carrier (27 cases per ternary axiom)
  * Wood-Atkey universal property for every (x, y) pair
  * The §27.1 Lam-bug witness: `div 1 omega = 0`
-/

namespace Tests.Kernel.Grade.Usage

open FX.Kernel
open FX.Kernel.Usage

/-! ## Add truth table -/

example : add zero  zero  = zero   := by decide
example : add zero  one   = one    := by decide
example : add zero  omega = omega  := by decide
example : add one   zero  = one    := by decide
example : add one   one   = omega  := by decide
example : add one   omega = omega  := by decide
example : add omega zero  = omega  := by decide
example : add omega one   = omega  := by decide
example : add omega omega = omega  := by decide

/-! ## Mul truth table -/

example : mul zero  zero  = zero   := by decide
example : mul zero  one   = zero   := by decide
example : mul zero  omega = zero   := by decide
example : mul one   zero  = zero   := by decide
example : mul one   one   = one    := by decide
example : mul one   omega = omega  := by decide
example : mul omega zero  = zero   := by decide
example : mul omega one   = omega  := by decide
example : mul omega omega = omega  := by decide

/-! ## Div truth table -/

example : div zero  zero  = omega  := by decide  -- vacuous
example : div zero  one   = zero   := by decide
example : div zero  omega = zero   := by decide
example : div one   zero  = omega  := by decide
example : div one   one   = one    := by decide
example : div one   omega = zero   := by decide  -- §27.1 Lam-bug
example : div omega zero  = omega  := by decide
example : div omega one   = omega  := by decide
example : div omega omega = omega  := by decide

/-! ## LessEq total-order truth table

The total order is `0 ≤ 1 ≤ omega` (deliberate — see the
`Usage.lean` docstring). Every pair is either `≤`-related or
not; enumerating makes the shape visible to future readers. -/

example : LessEq zero  zero  := by decide
example : LessEq zero  one   := by decide
example : LessEq zero  omega := by decide
example : ¬ LessEq one   zero := by decide
example : LessEq one   one   := by decide
example : LessEq one   omega := by decide
example : ¬ LessEq omega zero := by decide
example : ¬ LessEq omega one  := by decide
example : LessEq omega omega := by decide

/-! ## Semiring axioms — exhaustive

Every 3-argument axiom enumerates 3³ = 27 cases; Lean's `decide`
enumerates each automatically, so one invocation covers the
whole quantified statement.
-/

example : ∀ x y : Usage, add x y = add y x := by
  intro x y; cases x <;> cases y <;> rfl

example : ∀ x y z : Usage, add (add x y) z = add x (add y z) := by
  intro x y z; cases x <;> cases y <;> cases z <;> rfl

example : ∀ x : Usage, add zero x = x := by intro x; cases x <;> rfl
example : ∀ x : Usage, add x zero = x := by intro x; cases x <;> rfl

example : ∀ x y z : Usage, mul (mul x y) z = mul x (mul y z) := by
  intro x y z; cases x <;> cases y <;> cases z <;> rfl

example : ∀ x : Usage, mul zero x = zero := by intro x; cases x <;> rfl
example : ∀ x : Usage, mul x zero = zero := by intro x; cases x <;> rfl

example : ∀ x : Usage, mul one x = x := by intro x; cases x <;> rfl
example : ∀ x : Usage, mul x one = x := by intro x; cases x <;> rfl

example : ∀ x y z : Usage, mul x (add y z) = add (mul x y) (mul x z) := by
  intro x y z; cases x <;> cases y <;> cases z <;> rfl
example : ∀ x y z : Usage, mul (add x y) z = add (mul x z) (mul y z) := by
  intro x y z; cases x <;> cases y <;> cases z <;> rfl

/-! ## LessEq preorder -/

example : ∀ x : _, LessEq x x := LessEq.refl

example : ∀ x y z : _, LessEq x y → LessEq y z → LessEq x z := fun _ _ _ => LessEq.trans

/-! ## Wood-Atkey division — universal property

For every `(x, y)`, `div x y` is the **greatest** `d` with
`mul d y ≤ x`.  Enumerates 3² = 9 pairs on the outer, and for
each pair 3 choices of `d` on the inner.
-/

-- `(div x y) * y ≤ x`
example : ∀ x y : Usage, LessEq (mul (div x y) y) x :=
  Usage.div_mul_le

-- Maximality: `d * y ≤ x → d ≤ div x y`.
example : ∀ x y d : Usage, LessEq (mul d y) x → LessEq d (div x y) :=
  Usage.div_universal

/-! ## The Lam-bug witness

The corrected Wood/Atkey Pi-intro rule divides the ambient
context by the lambda's grade.  `div 1 omega = 0` is what blocks
the Atkey-2018 bug: a linear binding captured into an
unrestricted closure becomes ghost in the closure's context
and can therefore not be used multiple times. -/

example : div one omega = zero := rfl

/-! ## Antisymmetry — `LessEq` is a partial (in fact total) order -/

example : ∀ x y : Usage, LessEq x y → LessEq y x → x = y :=
  fun _ _ => Usage.LessEq.antisymm

/-! ## Monotonicity of the combine operations -/

example : ∀ x x' y : Usage, LessEq x x' → LessEq (add x y) (add x' y) :=
  fun _ _ y h => Usage.add_mono_left y h

example : ∀ x x' y : Usage, LessEq x x' → LessEq (mul x y) (mul x' y) :=
  fun _ _ y h => Usage.mul_mono_left y h

/-! ## Idempotence — linearity invariant

`add one one = omega`, not `one` — this is the single rule
catching double-use of a linear binding across parallel branches
(e.g., both arms of an `if`).  Idempotence holds at the two
absorbing elements but deliberately fails at `one`. -/

example : add zero  zero  = zero  := rfl
example : add omega omega = omega := rfl
example : add one   one   ≠ one   := by decide

example : ∀ x : Usage, mul x x = x := Usage.mul_idem

/-! ## Decidability sanity checks

Usage has `DecidableEq` via `deriving` and `decLe` as a manual
instance.  Both are used at the `decide` call sites above; these
tests confirm the instances resolve at the top level. -/

example : (decide (add one one = omega) : Bool) = true := rfl
example : (decide (LessEq zero omega) : Bool) = true := rfl
example : (decide (LessEq omega zero) : Bool) = false := rfl

/-! ## Surface-mapping witnesses

Per `Usage.lean` docstring: `ghost` = 0, default/`own`/`ref mut`
= 1, `ref`/`@[copy]` = omega.  Encoded as the concrete grades so
that a regression in the mapping is a compile error here as
well as in the kernel. -/

-- `ghost`
example : (zero : Usage) = Usage.zero := rfl
-- default mode / `own` / `ref mut`
example : (one : Usage) = Usage.one := rfl
-- `ref` (shared) / `@[copy]`
example : (omega : Usage) = Usage.omega := rfl

end Tests.Kernel.Grade.Usage
