prelude
import LeanFX2.FX1.LeanKernel.Inductive

/-! # FX1/LeanKernel/HasType

Day 0 scaffold for the Lean kernel typing relation.

## Deliverable

This module defines the first encoded `HasType` judgment for Lean expressions:
sorts, bound variables, and constants.  It is deliberately a fragment.  Lean
lambda, forall, let, inductive, projection, literal, metavariable, and
free-variable typing belong to later LeanKernel-FX1 slices.
-/

namespace LeanFX2
namespace FX1.LeanKernel

namespace Environment

/-- Relational constant membership in the encoded Lean-kernel environment. -/
inductive HasConstantInList {level : Nat} :
    List (ConstantSpec level) -> Name -> ConstantSpec level -> Prop
  /-- The newest constant declaration is available under its own name. -/
  | newest
      (constantSpec : ConstantSpec level)
      (remainingConstants : List (ConstantSpec level)) :
      HasConstantInList
        (List.cons constantSpec remainingConstants)
        constantSpec.constantName
        constantSpec
  /-- Older constants remain available past newer declarations. -/
  | older
      {remainingConstants : List (ConstantSpec level)}
      {queryName : Name}
      {constantSpec : ConstantSpec level}
      (newerConstant : ConstantSpec level)
      (olderConstant :
        HasConstantInList remainingConstants queryName constantSpec) :
      HasConstantInList
        (List.cons newerConstant remainingConstants)
        queryName
        constantSpec

/-- Relational constant membership for the full encoded environment. -/
def HasConstant {level : Nat}
    (environment : Environment level)
    (queryName : Name)
    (constantSpec : ConstantSpec level) : Prop :=
  HasConstantInList environment.constants queryName constantSpec

namespace HasConstantInList

/-- Constant membership is stable under one newer constant declaration. -/
theorem weaken {level : Nat}
    {constants : List (ConstantSpec level)}
    {queryName : Name}
    {constantSpec : ConstantSpec level}
    (newerConstant : ConstantSpec level)
    (olderConstant : HasConstantInList constants queryName constantSpec) :
    HasConstantInList
      (List.cons newerConstant constants)
      queryName
      constantSpec :=
  HasConstantInList.older newerConstant olderConstant

end HasConstantInList

end Environment

/-- Lean-kernel local context for the first checker slice.

Entries are stored newest-to-oldest and already live at the current expression
scope.  Dependent local declarations and fvar typing are later LeanKernel-FX1
obligations. -/
structure Context (level scope : Nat) : Type where
  entries : List (Expr level scope)

namespace Context

/-- Empty Lean-kernel local context. -/
def empty {level scope : Nat} : Context level scope where
  entries := List.nil

/-- Extend a Lean-kernel local context with one newest binder type. -/
def extend {level scope : Nat}
    (context : Context level scope)
    (typeExpr : Expr level scope) : Context level scope where
  entries := List.cons typeExpr context.entries

/-- Relational lookup for bound-variable types. -/
inductive HasTypeAt {level scope : Nat} :
    Context level scope -> Nat -> Expr level scope -> Prop
  /-- The newest context entry is available at de Bruijn index zero. -/
  | newest
      (context : Context level scope)
      (typeExpr : Expr level scope) :
      HasTypeAt (extend context typeExpr) Nat.zero typeExpr
  /-- Older entries remain available past a newer binder. -/
  | older
      {context : Context level scope}
      {position : Nat}
      {typeExpr : Expr level scope}
      (newerTypeExpr : Expr level scope)
      (olderType : HasTypeAt context position typeExpr) :
      HasTypeAt
        (extend context newerTypeExpr)
        (Nat.succ position)
        typeExpr

namespace HasTypeAt

/-- Context lookup is stable under one newer binder. -/
theorem weaken {level scope : Nat}
    {context : Context level scope}
    {position : Nat}
    {typeExpr : Expr level scope}
    (newerTypeExpr : Expr level scope)
    (olderType : HasTypeAt context position typeExpr) :
    HasTypeAt
      (extend context newerTypeExpr)
      (Nat.succ position)
      typeExpr :=
  HasTypeAt.older newerTypeExpr olderType

end HasTypeAt

end Context

/-- Encoded Lean-kernel typing judgment for the current closed/checkable
fragment. -/
inductive HasType {level scope : Nat}
    (environment : Environment level)
    (context : Context level scope) :
    Expr level scope -> Expr level scope -> Prop
  /-- Lean kernel sorts are typed by their successor sort. -/
  | sort
      (sortLevel : Level) :
      HasType
        environment
        context
        (Expr.sort sortLevel)
        (Expr.sort (Level.succ sortLevel))
  /-- Bound variables are typed by local-context lookup. -/
  | bvar
      {position : Nat}
      {typeExpr : Expr level scope}
      (typeAtPosition : Context.HasTypeAt context position typeExpr) :
      HasType environment context (Expr.bvar position) typeExpr
  /-- Constants are typed by relational environment membership.

  Constant declarations store closed type payloads at scope zero.  The first
  LeanKernel-FX1 checker slice reindexes that closed payload into the current
  scope; a later environment well-formedness pass must prove those payloads are
  actually closed and well typed. -/
  | const
      {constName : Name}
      {levels : List Level}
      {constantSpec : ConstantSpec level}
      (constantMember :
        Environment.HasConstant environment constName constantSpec) :
      HasType
        environment
        context
        (Expr.const constName levels)
        (Expr.recontextualize constantSpec.typeExpr)

end FX1.LeanKernel
end LeanFX2
