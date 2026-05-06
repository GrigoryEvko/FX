prelude
import LeanFX2.FX1.Core.Name

/-! # FX1/Core/Level

Root status: Root-FX1 syntax scaffold.

Universe levels for the minimal FX1 root calculus.  This is deliberately
smaller than Lean's full level language: no universe metavariables and no
normalizer are introduced in this M1 slice.  Later checker work can add
normalization with full constructor enumeration if it becomes load-bearing.
-/

namespace LeanFX2.FX1

/-- Universe levels for the minimal FX1 lambda-Pi root calculus. -/
inductive Level : Type
  | zero : Level
  | succ (baseLevel : Level) : Level
  | max (leftLevel rightLevel : Level) : Level
  | imax (leftLevel rightLevel : Level) : Level
  | param (paramName : Name) : Level

namespace Level

/-- Structural executable equality for FX1 universe levels.

This is intentionally a full constructor-pair table rather than a wildcard
fallback, matching the project's zero-axiom match discipline. -/
def beq : Level -> Level -> Bool
  | Level.zero, Level.zero => true
  | Level.zero, Level.succ _ => false
  | Level.zero, Level.max _ _ => false
  | Level.zero, Level.imax _ _ => false
  | Level.zero, Level.param _ => false
  | Level.succ _, Level.zero => false
  | Level.succ leftBaseLevel, Level.succ rightBaseLevel =>
      Level.beq leftBaseLevel rightBaseLevel
  | Level.succ _, Level.max _ _ => false
  | Level.succ _, Level.imax _ _ => false
  | Level.succ _, Level.param _ => false
  | Level.max _ _, Level.zero => false
  | Level.max _ _, Level.succ _ => false
  | Level.max leftLeftLevel leftRightLevel,
      Level.max rightLeftLevel rightRightLevel =>
      Bool.and
        (Level.beq leftLeftLevel rightLeftLevel)
        (Level.beq leftRightLevel rightRightLevel)
  | Level.max _ _, Level.imax _ _ => false
  | Level.max _ _, Level.param _ => false
  | Level.imax _ _, Level.zero => false
  | Level.imax _ _, Level.succ _ => false
  | Level.imax _ _, Level.max _ _ => false
  | Level.imax leftLeftLevel leftRightLevel,
      Level.imax rightLeftLevel rightRightLevel =>
      Bool.and
        (Level.beq leftLeftLevel rightLeftLevel)
        (Level.beq leftRightLevel rightRightLevel)
  | Level.imax _ _, Level.param _ => false
  | Level.param _, Level.zero => false
  | Level.param _, Level.succ _ => false
  | Level.param _, Level.max _ _ => false
  | Level.param _, Level.imax _ _ => false
  | Level.param leftName, Level.param rightName =>
      Name.beq leftName rightName

/-- Structural size of an FX1 universe level. -/
def nodeCount : Level -> Nat
  | Level.zero => 1
  | Level.succ baseLevel => Nat.succ (Level.nodeCount baseLevel)
  | Level.max leftLevel rightLevel =>
      Nat.succ (Nat.add (Level.nodeCount leftLevel) (Level.nodeCount rightLevel))
  | Level.imax leftLevel rightLevel =>
      Nat.succ (Nat.add (Level.nodeCount leftLevel) (Level.nodeCount rightLevel))
  | Level.param _ => 1

end Level

end LeanFX2.FX1
