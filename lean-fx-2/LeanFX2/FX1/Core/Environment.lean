prelude
import LeanFX2.FX1.Core.Declaration

/-! # FX1/Core/Environment

Root status: Root-FX1 syntax scaffold.

A minimal declaration environment for FX1.  This layer is intentionally a plain
list with explicit lookup predicates: name equality and duplicate-name
discipline will be introduced with the checker spine, not smuggled in through
host-heavy maps.
-/

namespace LeanFX2.FX1

/-- FX1 declaration environment.

Newest declarations are stored at the head so extension is structurally cheap
and later lookup semantics can choose the first matching declaration. -/
structure Environment : Type where
  declarations : List Declaration

namespace Environment

/-- The empty FX1 environment. -/
def empty : Environment :=
  { declarations := List.nil }

/-- Extend an FX1 environment with one newest declaration. -/
def extend (environment : Environment) (declaration : Declaration) :
    Environment :=
  { declarations := List.cons declaration environment.declarations }

/-- Count declarations in a raw declaration list. -/
def declarationCountInList : List Declaration -> Nat
  | List.nil => 0
  | List.cons _ remainingDeclarations =>
      Nat.succ (Environment.declarationCountInList remainingDeclarations)

/-- Count declarations in the environment. -/
def declarationCount (environment : Environment) : Nat :=
  Environment.declarationCountInList environment.declarations

/-- Find the first declaration in a list satisfying a caller-provided predicate. -/
def findInDeclarations?
    (matchesDeclaration : Declaration -> Bool) :
    List Declaration -> Option Declaration
  | List.nil => none
  | List.cons declaration remainingDeclarations =>
      match matchesDeclaration declaration with
      | true => some declaration
      | false =>
          Environment.findInDeclarations? matchesDeclaration remainingDeclarations

/-- Find the newest declaration satisfying a caller-provided predicate. -/
def findWhere?
    (environment : Environment)
    (matchesDeclaration : Declaration -> Bool) :
    Option Declaration :=
  Environment.findInDeclarations? matchesDeclaration environment.declarations

/-- Whether any declaration satisfies a caller-provided predicate. -/
def hasDeclarationWhere
    (environment : Environment)
    (matchesDeclaration : Declaration -> Bool) :
    Bool :=
  match Environment.findWhere? environment matchesDeclaration with
  | some _ => true
  | none => false

/-- Find the newest declaration with the queried FX1 name. -/
def findByName? (environment : Environment) (queryName : Name) :
    Option Declaration :=
  Environment.findWhere? environment (Declaration.hasName queryName)

/-- Whether the environment contains a declaration with the queried FX1 name. -/
def hasName (environment : Environment) (queryName : Name) : Bool :=
  Environment.hasDeclarationWhere environment (Declaration.hasName queryName)

/-- Whether the environment currently contains an axiom placeholder. -/
def hasAxiomDeclaration (environment : Environment) : Bool :=
  Environment.hasDeclarationWhere environment Declaration.isAxiomDeclaration

end Environment

end LeanFX2.FX1
