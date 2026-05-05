import LeanFX2.Lean.Kernel.Reduction

/-! # Lean/Kernel/Inductive

Lean kernel declaration and inductive specifications.

## Deliverable

This module encodes the declaration data needed before the executable checker
can model delta and iota reduction:

* constant declarations with optional bodies;
* constructor declarations for inductive types;
* inductive declarations with parameters and indices;
* a small environment with structural lookup.

Strict positivity, recursor synthesis, and iota computation are deliberately
not claimed in this slice.
-/

namespace LeanFX2
namespace LeanKernel

/-- A Lean constant declaration in the encoded environment. -/
structure ConstantSpec (level : Nat) : Type where
  constantName : Name
  typeExpr : Expr level 0
  valueExpr? : Option (Expr level 0)

/-- A constructor declaration belonging to an inductive type. -/
structure ConstructorSpec (level : Nat) : Type where
  constructorName : Name
  constructorType : Expr level 0
  constructorArity : Nat

/-- Encoded inductive declaration data.

This is syntax and metadata only.  Later slices must add strict positivity and
recursor synthesis before iota reduction can be soundly represented. -/
structure InductiveSpec (level : Nat) : Type where
  inductiveName : Name
  typeExpr : Expr level 0
  parameterCount : Nat
  indexCount : Nat
  constructors : List (ConstructorSpec level)

/-- Encoded Lean-kernel environment fragment. -/
structure Environment (level : Nat) : Type where
  constants : List (ConstantSpec level)
  inductives : List (InductiveSpec level)

namespace Environment

/-- Empty environment. -/
def empty {level : Nat} : Environment level where
  constants := []
  inductives := []

/-- Find a constant declaration by name. -/
def findConstant? {level : Nat}
    (environment : Environment level)
    (targetName : Name) : Option (ConstantSpec level) :=
  environment.constants.find? fun constantSpec =>
    decide (constantSpec.constantName = targetName)

/-- Find an inductive declaration by name. -/
def findInductive? {level : Nat}
    (environment : Environment level)
    (targetName : Name) : Option (InductiveSpec level) :=
  environment.inductives.find? fun inductiveSpec =>
    decide (inductiveSpec.inductiveName = targetName)

/-- The empty environment contains no constants. -/
theorem findConstant?_empty {level : Nat} (targetName : Name) :
    findConstant? (empty (level := level)) targetName = none := rfl

/-- The empty environment contains no inductives. -/
theorem findInductive?_empty {level : Nat} (targetName : Name) :
    findInductive? (empty (level := level)) targetName = none := rfl

end Environment

end LeanKernel
end LeanFX2
