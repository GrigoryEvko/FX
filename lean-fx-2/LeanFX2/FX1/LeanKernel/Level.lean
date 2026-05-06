prelude
import LeanFX2.FX1.LeanKernel.Name

/-! # FX1/LeanKernel/Level

Lean kernel universe levels.

## Deliverable

This module encodes Lean's six universe-level constructors and a small,
decidable syntactic preorder used by the executable checker layer.  The
preorder is intentionally conservative: it is sufficient for early checker
soundness slices, not a complete reimplementation of Lean's level constraint
solver.
-/

namespace LeanFX2
namespace FX1.LeanKernel

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
def beq : Level -> Level -> Bool
  | Level.zero, Level.zero => true
  | Level.zero, Level.succ _rightBase => false
  | Level.zero, Level.max _rightLeft _rightRight => false
  | Level.zero, Level.imax _rightLeft _rightRight => false
  | Level.zero, Level.param _rightName => false
  | Level.zero, Level.mvar _rightName => false
  | Level.succ _leftBase, Level.zero => false
  | Level.succ leftBase, Level.succ rightBase => beq leftBase rightBase
  | Level.succ _leftBase, Level.max _rightLeft _rightRight => false
  | Level.succ _leftBase, Level.imax _rightLeft _rightRight => false
  | Level.succ _leftBase, Level.param _rightName => false
  | Level.succ _leftBase, Level.mvar _rightName => false
  | Level.max _leftLeft _leftRight, Level.zero => false
  | Level.max _leftLeft _leftRight, Level.succ _rightBase => false
  | Level.max leftLeft leftRight, Level.max rightLeft rightRight =>
      Bool.and (beq leftLeft rightLeft) (beq leftRight rightRight)
  | Level.max _leftLeft _leftRight, Level.imax _rightLeft _rightRight => false
  | Level.max _leftLeft _leftRight, Level.param _rightName => false
  | Level.max _leftLeft _leftRight, Level.mvar _rightName => false
  | Level.imax _leftLeft _leftRight, Level.zero => false
  | Level.imax _leftLeft _leftRight, Level.succ _rightBase => false
  | Level.imax _leftLeft _leftRight, Level.max _rightLeft _rightRight => false
  | Level.imax leftLeft leftRight, Level.imax rightLeft rightRight =>
      Bool.and (beq leftLeft rightLeft) (beq leftRight rightRight)
  | Level.imax _leftLeft _leftRight, Level.param _rightName => false
  | Level.imax _leftLeft _leftRight, Level.mvar _rightName => false
  | Level.param _leftName, Level.zero => false
  | Level.param _leftName, Level.succ _rightBase => false
  | Level.param _leftName, Level.max _rightLeft _rightRight => false
  | Level.param _leftName, Level.imax _rightLeft _rightRight => false
  | Level.param leftName, Level.param rightName =>
      Name.beq leftName rightName
  | Level.param _leftName, Level.mvar _rightName => false
  | Level.mvar _leftName, Level.zero => false
  | Level.mvar _leftName, Level.succ _rightBase => false
  | Level.mvar _leftName, Level.max _rightLeft _rightRight => false
  | Level.mvar _leftName, Level.imax _rightLeft _rightRight => false
  | Level.mvar _leftName, Level.param _rightName => false
  | Level.mvar leftName, Level.mvar rightName =>
      Name.beq leftName rightName

/-- Normalize Lean universe levels structurally.

This first slice deliberately avoids smart algebraic simplification.  Earlier
attempts to simplify `max`/`imax` with overlapping wildcard tables pulled
unwanted equality axioms through Lean's match compiler.  Full level
simplification belongs in a later, fully enumerated constraint-solver module. -/
def normalize : Level -> Level
  | Level.zero => Level.zero
  | Level.succ baseLevel => Level.succ (normalize baseLevel)
  | Level.max leftLevel rightLevel =>
      Level.max (normalize leftLevel) (normalize rightLevel)
  | Level.imax leftLevel rightLevel =>
      Level.imax (normalize leftLevel) (normalize rightLevel)
  | Level.param paramName => Level.param paramName
  | Level.mvar mvarName => Level.mvar mvarName

/-- Count universe-level syntax nodes. -/
def nodeCount : Level -> Nat
  | Level.zero => 1
  | Level.succ baseLevel => Nat.succ (nodeCount baseLevel)
  | Level.max leftLevel rightLevel =>
      Nat.succ (Nat.add (nodeCount leftLevel) (nodeCount rightLevel))
  | Level.imax leftLevel rightLevel =>
      Nat.succ (Nat.add (nodeCount leftLevel) (nodeCount rightLevel))
  | Level.param _paramName => 1
  | Level.mvar _mvarName => 1

/-- Fuel-indexed syntactic level ordering.

The fuel argument keeps recursion structural on `Nat`; without it, Lean
accepts the mutually shrinking left/right comparisons through well-founded
recursion, which is too strong for this zero-axiom kernel slice. -/
def leBoolWithFuel : Nat -> Level -> Level -> Bool
  | Nat.zero, leftLevel, rightLevel =>
      beq (normalize leftLevel) (normalize rightLevel)
  | Nat.succ _fuel, Level.zero, Level.zero => true
  | Nat.succ _fuel, Level.zero, Level.succ _rightBase => true
  | Nat.succ _fuel, Level.zero, Level.max _rightA _rightB => true
  | Nat.succ _fuel, Level.zero, Level.imax _rightA _rightB => true
  | Nat.succ _fuel, Level.zero, Level.param _rightName => true
  | Nat.succ _fuel, Level.zero, Level.mvar _rightName => true
  | Nat.succ fuel, Level.succ leftBase, Level.zero =>
      leBoolWithFuel fuel (Level.succ leftBase) Level.zero
  | Nat.succ fuel, Level.succ leftBase, Level.succ rightBase =>
      leBoolWithFuel fuel leftBase rightBase
  | Nat.succ fuel, Level.succ leftBase, Level.max rightA rightB =>
      Bool.or
        (leBoolWithFuel fuel (Level.succ leftBase) rightA)
        (leBoolWithFuel fuel (Level.succ leftBase) rightB)
  | Nat.succ fuel, Level.succ leftBase, Level.imax rightA rightB =>
      leBoolWithFuel fuel (Level.succ leftBase) (Level.imax rightA rightB)
  | Nat.succ fuel, Level.succ leftBase, Level.param rightName =>
      leBoolWithFuel fuel (Level.succ leftBase) (Level.param rightName)
  | Nat.succ fuel, Level.succ leftBase, Level.mvar rightName =>
      leBoolWithFuel fuel (Level.succ leftBase) (Level.mvar rightName)
  | Nat.succ fuel, Level.max leftA leftB, Level.zero =>
      Bool.and
        (leBoolWithFuel fuel leftA Level.zero)
        (leBoolWithFuel fuel leftB Level.zero)
  | Nat.succ fuel, Level.max leftA leftB, Level.succ rightBase =>
      Bool.and
        (leBoolWithFuel fuel leftA (Level.succ rightBase))
        (leBoolWithFuel fuel leftB (Level.succ rightBase))
  | Nat.succ fuel, Level.max leftA leftB, Level.max rightA rightB =>
      Bool.and
        (leBoolWithFuel fuel leftA (Level.max rightA rightB))
        (leBoolWithFuel fuel leftB (Level.max rightA rightB))
  | Nat.succ fuel, Level.max leftA leftB, Level.imax rightA rightB =>
      Bool.and
        (leBoolWithFuel fuel leftA (Level.imax rightA rightB))
        (leBoolWithFuel fuel leftB (Level.imax rightA rightB))
  | Nat.succ fuel, Level.max leftA leftB, Level.param rightName =>
      Bool.and
        (leBoolWithFuel fuel leftA (Level.param rightName))
        (leBoolWithFuel fuel leftB (Level.param rightName))
  | Nat.succ fuel, Level.max leftA leftB, Level.mvar rightName =>
      Bool.and
        (leBoolWithFuel fuel leftA (Level.mvar rightName))
        (leBoolWithFuel fuel leftB (Level.mvar rightName))
  | Nat.succ fuel, Level.imax leftA leftB, Level.zero =>
      leBoolWithFuel fuel (Level.imax leftA leftB) Level.zero
  | Nat.succ fuel, Level.imax leftA leftB, Level.succ rightBase =>
      leBoolWithFuel fuel (Level.imax leftA leftB) (Level.succ rightBase)
  | Nat.succ fuel, Level.imax leftA leftB, Level.max rightA rightB =>
      Bool.or
        (leBoolWithFuel fuel (Level.imax leftA leftB) rightA)
        (leBoolWithFuel fuel (Level.imax leftA leftB) rightB)
  | Nat.succ fuel, Level.imax leftA leftB, Level.imax rightA rightB =>
      leBoolWithFuel fuel (Level.imax leftA leftB) (Level.imax rightA rightB)
  | Nat.succ fuel, Level.imax leftA leftB, Level.param rightName =>
      leBoolWithFuel fuel (Level.imax leftA leftB) (Level.param rightName)
  | Nat.succ fuel, Level.imax leftA leftB, Level.mvar rightName =>
      leBoolWithFuel fuel (Level.imax leftA leftB) (Level.mvar rightName)
  | Nat.succ fuel, Level.param leftName, Level.zero =>
      leBoolWithFuel fuel (Level.param leftName) Level.zero
  | Nat.succ fuel, Level.param leftName, Level.succ rightBase =>
      leBoolWithFuel fuel (Level.param leftName) (Level.succ rightBase)
  | Nat.succ fuel, Level.param leftName, Level.max rightA rightB =>
      Bool.or
        (leBoolWithFuel fuel (Level.param leftName) rightA)
        (leBoolWithFuel fuel (Level.param leftName) rightB)
  | Nat.succ fuel, Level.param leftName, Level.imax rightA rightB =>
      leBoolWithFuel fuel (Level.param leftName) (Level.imax rightA rightB)
  | Nat.succ fuel, Level.param leftName, Level.param rightName =>
      leBoolWithFuel fuel (Level.param leftName) (Level.param rightName)
  | Nat.succ fuel, Level.param leftName, Level.mvar rightName =>
      leBoolWithFuel fuel (Level.param leftName) (Level.mvar rightName)
  | Nat.succ fuel, Level.mvar leftName, Level.zero =>
      leBoolWithFuel fuel (Level.mvar leftName) Level.zero
  | Nat.succ fuel, Level.mvar leftName, Level.succ rightBase =>
      leBoolWithFuel fuel (Level.mvar leftName) (Level.succ rightBase)
  | Nat.succ fuel, Level.mvar leftName, Level.max rightA rightB =>
      Bool.or
        (leBoolWithFuel fuel (Level.mvar leftName) rightA)
        (leBoolWithFuel fuel (Level.mvar leftName) rightB)
  | Nat.succ fuel, Level.mvar leftName, Level.imax rightA rightB =>
      leBoolWithFuel fuel (Level.mvar leftName) (Level.imax rightA rightB)
  | Nat.succ fuel, Level.mvar leftName, Level.param rightName =>
      leBoolWithFuel fuel (Level.mvar leftName) (Level.param rightName)
  | Nat.succ fuel, Level.mvar leftName, Level.mvar rightName =>
      leBoolWithFuel fuel (Level.mvar leftName) (Level.mvar rightName)

/-- Decidable syntactic level ordering used by the encoded checker.

The relation is conservative and structural:

* `zero` is below every level;
* `succ` compares recursively against `succ`;
* `max a b ≤ c` requires both sides below `c`;
* `a ≤ max b c` accepts either branch;
* otherwise normalized syntactic equality is required.
-/
def leBool : Level -> Level -> Bool
  | leftLevel, rightLevel =>
      leBoolWithFuel
        (Nat.add (nodeCount leftLevel) (nodeCount rightLevel))
        leftLevel
        rightLevel

/-- Propositional wrapper around `leBool`. -/
def le (leftLevel rightLevel : Level) : Prop :=
  Eq (leBool leftLevel rightLevel) true

/-- Normalizing `zero` is computation. -/
theorem normalize_zero :
    Eq (normalize Level.zero) Level.zero := Eq.refl Level.zero

end Level

end FX1.LeanKernel
end LeanFX2
