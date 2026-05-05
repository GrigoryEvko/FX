prelude
import LeanFX2.FX1.Core.Environment
import LeanFX2.FX1.Core.Context
import LeanFX2.FX1.Core.Reduction

/-! # FX1/Core/HasType

Root status: Root-FX1 metatheory scaffold.

Typing relation for the minimal FX1 lambda-Pi core.  This file uses relational
environment and context membership instead of host maps or decidable name
equality.  Environment well-formedness, duplicate-name rejection, conversion,
and preservation are subsequent M3/M4 obligations.
-/

namespace LeanFX2.FX1

namespace Environment

/-- Relational declaration membership for FX1 environments.

This avoids trusting host-side name equality during the first typing slice.
Duplicate-name discipline is a later environment well-formedness obligation. -/
inductive HasDeclaration : Environment -> Name -> Declaration -> Prop
  /-- The newest declaration is available under its own name. -/
  | newest
      (environment : Environment) (declaration : Declaration) :
      HasDeclaration
        (Environment.extend environment declaration)
        (Declaration.name declaration)
        declaration
  /-- Older declarations remain available after extending the environment. -/
  | older
      {environment : Environment}
      {queryName : Name}
      {declaration : Declaration}
      (newDeclaration : Declaration)
      (olderDeclaration : HasDeclaration environment queryName declaration) :
      HasDeclaration
        (Environment.extend environment newDeclaration)
        queryName
        declaration

end Environment

namespace Context

/-- Relational lookup for de Bruijn variables.

The older-variable rule weakens the stored type as it passes through a newer
binder.  This is the dependent-context behavior missing from plain
`Context.lookup?`, which is intentionally only a syntactic index probe. -/
inductive HasTypeAt : Context -> Nat -> Expr -> Prop
  /-- The newest binder has exactly the type used to extend the context. -/
  | newest
      (context : Context) (typeExpr : Expr) :
      HasTypeAt
        (Context.extend context typeExpr)
        Nat.zero
        typeExpr
  /-- An older binder's type is weakened through the newer binder. -/
  | older
      {context : Context}
      {index : Nat}
      {typeExpr : Expr}
      (newTypeExpr : Expr)
      (olderType : HasTypeAt context index typeExpr) :
      HasTypeAt
        (Context.extend context newTypeExpr)
        (Nat.succ index)
        (Expr.weaken typeExpr)

end Context

/-- FX1 typing judgment for the minimal lambda-Pi core. -/
inductive HasType (environment : Environment) : Context -> Expr -> Expr -> Prop
  /-- A sort is typed by its successor sort. -/
  | sort
      (context : Context) (sortLevel : Level) :
      HasType
        environment
        context
        (Expr.sort sortLevel)
        (Expr.sort (Level.succ sortLevel))
  /-- Variables are typed by dependent-context lookup. -/
  | var
      {context : Context}
      {index : Nat}
      {typeExpr : Expr}
      (variableType : Context.HasTypeAt context index typeExpr) :
      HasType environment context (Expr.bvar index) typeExpr
  /-- Constants are typed by relational environment membership. -/
  | const
      {context : Context}
      {constName : Name}
      {declaration : Declaration}
      (declarationMember :
        Environment.HasDeclaration environment constName declaration) :
      HasType
        environment
        context
        (Expr.const constName)
        (Declaration.typeExpr declaration)
  /-- Pi formation. -/
  | pi
      {context : Context}
      {domainExpr bodyExpr : Expr}
      {domainLevel bodyLevel : Level}
      (domainHasSort :
        HasType environment context domainExpr (Expr.sort domainLevel))
      (bodyHasSort :
        HasType
          environment
          (Context.extend context domainExpr)
          bodyExpr
          (Expr.sort bodyLevel)) :
      HasType
        environment
        context
        (Expr.pi domainExpr bodyExpr)
        (Expr.sort (Level.max domainLevel bodyLevel))
  /-- Lambda introduction against an explicit Pi type. -/
  | lam
      {context : Context}
      {domainExpr bodyExpr bodyTypeExpr : Expr}
      {domainLevel : Level}
      (domainHasSort :
        HasType environment context domainExpr (Expr.sort domainLevel))
      (bodyHasType :
        HasType
          environment
          (Context.extend context domainExpr)
          bodyExpr
          bodyTypeExpr) :
      HasType
        environment
        context
        (Expr.lam domainExpr bodyExpr)
        (Expr.pi domainExpr bodyTypeExpr)
  /-- Function application eliminates a Pi type by substituting the argument
  into the codomain. -/
  | app
      {context : Context}
      {functionExpr argumentExpr domainExpr bodyTypeExpr : Expr}
      (functionHasPi :
        HasType
          environment
          context
          functionExpr
          (Expr.pi domainExpr bodyTypeExpr))
      (argumentHasDomain :
        HasType environment context argumentExpr domainExpr) :
      HasType
        environment
        context
        (Expr.app functionExpr argumentExpr)
        (Expr.subst0 argumentExpr bodyTypeExpr)

namespace HasType

/-- The empty-context identity over `Sort 0` has the expected Pi type. -/
theorem sortZeroIdentity
    (environment : Environment) :
    HasType
      environment
      Context.empty
      (Expr.lam (Expr.sort Level.zero) (Expr.bvar Nat.zero))
      (Expr.pi (Expr.sort Level.zero) (Expr.sort Level.zero)) :=
  HasType.lam
    (HasType.sort Context.empty Level.zero)
    (HasType.var
      (Context.HasTypeAt.newest Context.empty (Expr.sort Level.zero)))

end HasType

end LeanFX2.FX1
