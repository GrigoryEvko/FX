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
