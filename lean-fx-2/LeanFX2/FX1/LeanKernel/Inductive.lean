prelude
import LeanFX2.FX1.LeanKernel.Reduction

/-! # FX1/LeanKernel/Inductive

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
namespace FX1.LeanKernel

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
  constants := List.nil
  inductives := List.nil

/-- Find a constant declaration in a declaration list. -/
def findConstantInList? {level : Nat}
    (targetName : Name) : List (ConstantSpec level) -> Option (ConstantSpec level)
  | List.nil => Option.none
  | List.cons constantSpec remainingConstants =>
      match Name.beq constantSpec.constantName targetName with
      | true => Option.some constantSpec
      | false => findConstantInList? targetName remainingConstants

/-- Find an inductive declaration in a declaration list. -/
def findInductiveInList? {level : Nat}
    (targetName : Name) : List (InductiveSpec level) -> Option (InductiveSpec level)
  | List.nil => Option.none
  | List.cons inductiveSpec remainingInductives =>
      match Name.beq inductiveSpec.inductiveName targetName with
      | true => Option.some inductiveSpec
      | false => findInductiveInList? targetName remainingInductives

/-- Find a constant declaration by name. -/
def findConstant? {level : Nat}
    (environment : Environment level)
    (targetName : Name) : Option (ConstantSpec level) :=
  findConstantInList? targetName environment.constants

/-- Find an inductive declaration by name. -/
def findInductive? {level : Nat}
    (environment : Environment level)
    (targetName : Name) : Option (InductiveSpec level) :=
  findInductiveInList? targetName environment.inductives

/-- The empty environment contains no constants. -/
theorem findConstant?_empty {level : Nat} (targetName : Name) :
    Eq (findConstant? (empty (level := level)) targetName) Option.none :=
  Eq.refl Option.none

/-- The empty environment contains no inductives. -/
theorem findInductive?_empty {level : Nat} (targetName : Name) :
    Eq (findInductive? (empty (level := level)) targetName) Option.none :=
  Eq.refl Option.none

end Environment

end FX1.LeanKernel
end LeanFX2
