import FX.Kernel.Grade.Lifetime

/-!
# Lifetime dimension tests

Covers `fx_design.md` §6.3 dim 7: `Region = static | var n`.
The kernel's preorder is shallow — `static` is the top,
reflexivity on `var n`, nothing else unconditionally.  Non-
trivial region orderings come from elaborator-supplied
hypotheses (§8.1, §6.3).

The `add` operation coalesces non-equal regions to `static` as
a deliberate Phase-1 sound over-approximation (see
Lifetime.lean docstring).  Tests here exercise that behavior
on a finite window; full coverage of the infinite carrier
cannot be decided.
-/

namespace Tests.Kernel.Grade.Lifetime

open FX.Kernel
open FX.Kernel.Region

/-! ## `add` — coalesce to `static` on non-equal pairs

This is the Phase-1 sound over-approximation (see
Lifetime.lean docstring).  Every pair of distinct region
variables joins to `static`; equal-index pairs return the
variable itself. -/

example : add static static = static := by decide
example : add static (var 0) = static := by decide
example : add (var 0) static = static := by decide
example : add (var 0) (var 0) = var 0 := by decide
example : add (var 0) (var 1) = static := by decide
example : add (var 1) (var 0) = static := by decide
example : add (var 42) (var 42) = var 42 := by decide

/-! ### Non-equal coalesce — broader sample

Every pair of distinct region variables must coalesce to
`static`; this is what makes the kernel sound despite not
knowing the elaborator's outlives order. -/

example : add (var 0) (var 2)     = static := by decide
example : add (var 2) (var 0)     = static := by decide
example : add (var 3) (var 7)     = static := by decide
example : add (var 7) (var 3)     = static := by decide
example : add (var 10) (var 99)   = static := by decide
example : add (var 100) (var 101) = static := by decide
example : add (var 1000) (var 1)  = static := by decide

/-- Universal non-equal coalesce: whenever two region
    variables have different indices, `add` produces `static`. -/
example : ∀ a b : Nat, a ≠ b → add (var a) (var b) = static := by
  intro a b h
  simp [add, if_neg h]

/-! ### `add` is a sound upper bound on the outlives preorder

Because `static` is the top, the Phase-1 coalesce-to-static
never rejects a value.  Both operands are `≤ add x y` for any
pair of regions — the sound-over-approximation property
formalized. -/

example : ∀ x y : Region, LessEq x (add x y) := by
  intro x y
  cases x with
  | static => cases y <;> exact LessEq.leStatic _
  | var a  =>
    cases y with
    | static => exact LessEq.leStatic _
    | var b  =>
      by_cases h : a = b
      · subst h; simp [add]; exact LessEq.refl _
      · simp [add, if_neg h]; exact LessEq.leStatic _

example : ∀ x y : Region, LessEq y (add x y) := by
  intro x y
  cases x with
  | static => cases y <;> exact LessEq.leStatic _
  | var a  =>
    cases y with
    | static => exact LessEq.leStatic _
    | var b  =>
      by_cases h : a = b
      · subst h; simp [add]; exact LessEq.refl _
      · simp [add, if_neg h]; exact LessEq.leStatic _

/-! ## `mul` = `add` — identical behavior -/

example : mul static static = static := by decide
example : mul (var 0) (var 0) = var 0 := by decide
example : mul (var 0) (var 1) = static := by decide
example : ∀ x y : Region,
    x = static → mul x y = static := by
  intro x y h; subst h; cases y <;> rfl

/-! ## `static` is absorbing from both sides -/

example : ∀ x : Region, add static x = static := by
  intro x; cases x <;> rfl

example : ∀ x : Region, add x static = static := by
  intro x; cases x <;> rfl

example : ∀ x : Region, mul static x = static := by
  intro x; cases x <;> rfl

example : ∀ x : Region, mul x static = static := by
  intro x; cases x <;> rfl

/-! ## Idempotence on a finite window

`add_idem` holds for the full infinite carrier; check a finite
window by decide. -/

example : add static static = static := by decide
example : add (var 0) (var 0) = var 0 := by decide
example : add (var 7) (var 7) = var 7 := by decide
example : add (var 99) (var 99) = var 99 := by decide

/-! ## Commutativity on a fixed finite window

Full commutativity over the infinite carrier holds as a proved
theorem (`Region.add_comm`); the kernel already exposes it.
Here we exercise the three-element window `{static, var 0,
var 1}` exhaustively. -/

example : add static (var 0) = add (var 0) static := by decide
example : add (var 0) (var 1) = add (var 1) (var 0) := by decide
example : add (var 0) (var 0) = add (var 0) (var 0) := by decide
example : add (var 5) (var 3) = add (var 3) (var 5) := by decide

/-! ## Associativity on a finite window

`add` associativity is not exposed as a kernel theorem because
full associativity over the coalesce-to-static semantics is
trivial (both sides land on `static` whenever any two of the
three arguments disagree).  Exercise the nontrivial cases. -/

example : add (add (var 0) (var 0)) (var 0)
        = add (var 0) (add (var 0) (var 0)) := by decide

example : add (add (var 0) (var 1)) (var 2)
        = add (var 0) (add (var 1) (var 2)) := by decide

example : add (add (var 0) static) (var 1)
        = add (var 0) (add static (var 1)) := by decide

/-! ## `LessEq` — the two constructors -/

example : LessEq static static := by decide
example : LessEq (var 0) static := by decide
example : LessEq (var 0) (var 0) := by decide
example : ¬ LessEq static (var 0) := by decide
example : ¬ LessEq (var 0) (var 1) := by decide

/-! ## `static` is the top of the outlives preorder -/

example : LessEq (var 0) static := by decide
example : LessEq (var 99) static := by decide
example : ∀ x : Region, LessEq x static := by
  intro x; exact LessEq.leStatic _

/-! ## Reflexivity on the infinite carrier

`LessEq.refl` covers the full carrier; test a sample. -/

example : ∀ x : Region, LessEq x x := by
  intro x; exact LessEq.refl _

example : LessEq (var 12345) (var 12345) := by decide

/-! ## `decLe` decidability — both branches -/

example : decide (LessEq static static) = true := by decide
example : decide (LessEq (var 0) static) = true := by decide
example : decide (LessEq (var 0) (var 0)) = true := by decide
example : decide (LessEq static (var 0)) = false := by decide
example : decide (LessEq (var 0) (var 1)) = false := by decide

/-! ## `LessEq.trans` — the four legal combinations -/

-- refl ∘ refl
example : LessEq (var 0) (var 0) → LessEq (var 0) (var 0) → LessEq (var 0) (var 0) :=
  fun _ _ => LessEq.refl _

-- refl ∘ leStatic
example : LessEq (var 0) (var 0) → LessEq (var 0) static → LessEq (var 0) static :=
  fun _ _ => LessEq.leStatic _

-- leStatic ∘ refl
example : LessEq (var 0) static → LessEq static static → LessEq (var 0) static :=
  fun _ _ => LessEq.leStatic _

-- leStatic ∘ leStatic
example : LessEq (var 0) static → LessEq static static → LessEq (var 0) static :=
  fun _ _ => LessEq.leStatic _

/-! ## `LessEq.trans` over the kernel proof -/

example : ∀ x y z : Region, LessEq x y → LessEq y z → LessEq x z :=
  fun _ _ _ => LessEq.trans

/-! ## Interaction between `add` and `LessEq`

The coalesce-to-static semantics of `add` makes the join an
upper bound trivially on non-equal pairs: `add x y = static`
and `LessEq x static` / `LessEq y static`.  On equal pairs, `add x x
= x`. -/

example : LessEq (var 0) (add (var 0) (var 1)) := by decide
example : LessEq (var 1) (add (var 0) (var 1)) := by decide
example : LessEq (var 0) (add (var 0) (var 0)) := by decide

end Tests.Kernel.Grade.Lifetime
