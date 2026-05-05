import LeanFX2.Foundation.Universe
import LeanFX2.Lean.Kernel.Name

/-! # Lean/Kernel/Level

Lean kernel universe levels.

## Deliverable

This module encodes Lean's six universe-level constructors and a small,
decidable syntactic preorder used by the executable checker layer.  The
preorder is intentionally conservative: it is sufficient for early checker
soundness slices, not a complete reimplementation of Lean's level constraint
solver.
-/

namespace LeanFX2
namespace LeanKernel

/-- Lean kernel universe levels. -/
inductive Level : Type
  | zero : Level
  | succ (baseLevel : Level) : Level
  | max (leftLevel rightLevel : Level) : Level
  | imax (leftLevel rightLevel : Level) : Level
  | param (paramName : Name) : Level
  | mvar (mvarName : Name) : Level

namespace Level

/-- Structural Boolean equality for universe levels.

This avoids generated recursive `DecidableEq` instances, which can pull in
Lean equality infrastructure outside the project's zero-axiom discipline. -/
def beq : Level → Level → Bool
  | zero, zero => true
  | zero, succ _rightBase => false
  | zero, max _rightLeft _rightRight => false
  | zero, imax _rightLeft _rightRight => false
  | zero, param _rightName => false
  | zero, mvar _rightName => false
  | succ _leftBase, zero => false
  | succ leftBase, succ rightBase => beq leftBase rightBase
  | succ _leftBase, max _rightLeft _rightRight => false
  | succ _leftBase, imax _rightLeft _rightRight => false
  | succ _leftBase, param _rightName => false
  | succ _leftBase, mvar _rightName => false
  | max _leftLeft _leftRight, zero => false
  | max _leftLeft _leftRight, succ _rightBase => false
  | max leftLeft leftRight, max rightLeft rightRight =>
      beq leftLeft rightLeft && beq leftRight rightRight
  | max _leftLeft _leftRight, imax _rightLeft _rightRight => false
  | max _leftLeft _leftRight, param _rightName => false
  | max _leftLeft _leftRight, mvar _rightName => false
  | imax _leftLeft _leftRight, zero => false
  | imax _leftLeft _leftRight, succ _rightBase => false
  | imax _leftLeft _leftRight, max _rightLeft _rightRight => false
  | imax leftLeft leftRight, imax rightLeft rightRight =>
      beq leftLeft rightLeft && beq leftRight rightRight
  | imax _leftLeft _leftRight, param _rightName => false
  | imax _leftLeft _leftRight, mvar _rightName => false
  | param _leftName, zero => false
  | param _leftName, succ _rightBase => false
  | param _leftName, max _rightLeft _rightRight => false
  | param _leftName, imax _rightLeft _rightRight => false
  | param leftName, param rightName =>
      decide (leftName = rightName)
  | param _leftName, mvar _rightName => false
  | mvar _leftName, zero => false
  | mvar _leftName, succ _rightBase => false
  | mvar _leftName, max _rightLeft _rightRight => false
  | mvar _leftName, imax _rightLeft _rightRight => false
  | mvar _leftName, param _rightName => false
  | mvar leftName, mvar rightName =>
      decide (leftName = rightName)

/-- Normalize Lean universe levels structurally.

This first slice deliberately avoids smart algebraic simplification.  Earlier
attempts to simplify `max`/`imax` with overlapping wildcard tables pulled
unwanted equality axioms through Lean's match compiler.  Full level
simplification belongs in a later, fully enumerated constraint-solver module. -/
def normalize : Level → Level
  | zero => zero
  | succ baseLevel => succ (normalize baseLevel)
  | max leftLevel rightLevel => max (normalize leftLevel) (normalize rightLevel)
  | imax leftLevel rightLevel => imax (normalize leftLevel) (normalize rightLevel)
  | param paramName => param paramName
  | mvar mvarName => mvar mvarName

/-- Count universe-level syntax nodes. -/
def nodeCount : Level → Nat
  | zero => 1
  | succ baseLevel => 1 + nodeCount baseLevel
  | max leftLevel rightLevel => 1 + nodeCount leftLevel + nodeCount rightLevel
  | imax leftLevel rightLevel => 1 + nodeCount leftLevel + nodeCount rightLevel
  | param _paramName => 1
  | mvar _mvarName => 1

/-- Fuel-indexed syntactic level ordering.

The fuel argument keeps recursion structural on `Nat`; without it, Lean
accepts the mutually shrinking left/right comparisons through well-founded
recursion, which is too strong for this zero-axiom kernel slice. -/
def leBoolWithFuel : Nat → Level → Level → Bool
  | 0, leftLevel, rightLevel =>
      beq (normalize leftLevel) (normalize rightLevel)
  | _fuel + 1, zero, zero => true
  | _fuel + 1, zero, succ _rightBase => true
  | _fuel + 1, zero, max _rightA _rightB => true
  | _fuel + 1, zero, imax _rightA _rightB => true
  | _fuel + 1, zero, param _rightName => true
  | _fuel + 1, zero, mvar _rightName => true
  | fuel + 1, succ leftBase, zero =>
      leBoolWithFuel fuel (succ leftBase) zero
  | fuel + 1, succ leftBase, succ rightBase =>
      leBoolWithFuel fuel leftBase rightBase
  | fuel + 1, succ leftBase, max rightA rightB =>
      leBoolWithFuel fuel (succ leftBase) rightA ||
        leBoolWithFuel fuel (succ leftBase) rightB
  | fuel + 1, succ leftBase, imax rightA rightB =>
      leBoolWithFuel fuel (succ leftBase) (imax rightA rightB)
  | fuel + 1, succ leftBase, param rightName =>
      leBoolWithFuel fuel (succ leftBase) (param rightName)
  | fuel + 1, succ leftBase, mvar rightName =>
      leBoolWithFuel fuel (succ leftBase) (mvar rightName)
  | fuel + 1, max leftA leftB, zero =>
      leBoolWithFuel fuel leftA zero && leBoolWithFuel fuel leftB zero
  | fuel + 1, max leftA leftB, succ rightBase =>
      leBoolWithFuel fuel leftA (succ rightBase) &&
        leBoolWithFuel fuel leftB (succ rightBase)
  | fuel + 1, max leftA leftB, max rightA rightB =>
      leBoolWithFuel fuel leftA (max rightA rightB) &&
        leBoolWithFuel fuel leftB (max rightA rightB)
  | fuel + 1, max leftA leftB, imax rightA rightB =>
      leBoolWithFuel fuel leftA (imax rightA rightB) &&
        leBoolWithFuel fuel leftB (imax rightA rightB)
  | fuel + 1, max leftA leftB, param rightName =>
      leBoolWithFuel fuel leftA (param rightName) &&
        leBoolWithFuel fuel leftB (param rightName)
  | fuel + 1, max leftA leftB, mvar rightName =>
      leBoolWithFuel fuel leftA (mvar rightName) &&
        leBoolWithFuel fuel leftB (mvar rightName)
  | fuel + 1, imax leftA leftB, zero =>
      leBoolWithFuel fuel (imax leftA leftB) zero
  | fuel + 1, imax leftA leftB, succ rightBase =>
      leBoolWithFuel fuel (imax leftA leftB) (succ rightBase)
  | fuel + 1, imax leftA leftB, max rightA rightB =>
      leBoolWithFuel fuel (imax leftA leftB) rightA ||
        leBoolWithFuel fuel (imax leftA leftB) rightB
  | fuel + 1, imax leftA leftB, imax rightA rightB =>
      leBoolWithFuel fuel (imax leftA leftB) (imax rightA rightB)
  | fuel + 1, imax leftA leftB, param rightName =>
      leBoolWithFuel fuel (imax leftA leftB) (param rightName)
  | fuel + 1, imax leftA leftB, mvar rightName =>
      leBoolWithFuel fuel (imax leftA leftB) (mvar rightName)
  | fuel + 1, param leftName, zero =>
      leBoolWithFuel fuel (param leftName) zero
  | fuel + 1, param leftName, succ rightBase =>
      leBoolWithFuel fuel (param leftName) (succ rightBase)
  | fuel + 1, param leftName, max rightA rightB =>
      leBoolWithFuel fuel (param leftName) rightA ||
        leBoolWithFuel fuel (param leftName) rightB
  | fuel + 1, param leftName, imax rightA rightB =>
      leBoolWithFuel fuel (param leftName) (imax rightA rightB)
  | fuel + 1, param leftName, param rightName =>
      leBoolWithFuel fuel (param leftName) (param rightName)
  | fuel + 1, param leftName, mvar rightName =>
      leBoolWithFuel fuel (param leftName) (mvar rightName)
  | fuel + 1, mvar leftName, zero =>
      leBoolWithFuel fuel (mvar leftName) zero
  | fuel + 1, mvar leftName, succ rightBase =>
      leBoolWithFuel fuel (mvar leftName) (succ rightBase)
  | fuel + 1, mvar leftName, max rightA rightB =>
      leBoolWithFuel fuel (mvar leftName) rightA ||
        leBoolWithFuel fuel (mvar leftName) rightB
  | fuel + 1, mvar leftName, imax rightA rightB =>
      leBoolWithFuel fuel (mvar leftName) (imax rightA rightB)
  | fuel + 1, mvar leftName, param rightName =>
      leBoolWithFuel fuel (mvar leftName) (param rightName)
  | fuel + 1, mvar leftName, mvar rightName =>
      leBoolWithFuel fuel (mvar leftName) (mvar rightName)

/-- Decidable syntactic level ordering used by the encoded checker.

The relation is conservative and structural:

* `zero` is below every level;
* `succ` compares recursively against `succ`;
* `max a b ≤ c` requires both sides below `c`;
* `a ≤ max b c` accepts either branch;
* otherwise normalized syntactic equality is required.
-/
def leBool : Level → Level → Bool
  | leftLevel, rightLevel =>
      leBoolWithFuel (nodeCount leftLevel + nodeCount rightLevel)
        leftLevel rightLevel

/-- Propositional wrapper around `leBool`. -/
def le (leftLevel rightLevel : Level) : Prop :=
  leBool leftLevel rightLevel = true

instance (leftLevel rightLevel : Level) : Decidable (le leftLevel rightLevel) :=
  by
    unfold le
    infer_instance

/-- Normalizing `zero` is computation. -/
theorem normalize_zero :
    normalize zero = zero := rfl

end Level

end LeanKernel
end LeanFX2
