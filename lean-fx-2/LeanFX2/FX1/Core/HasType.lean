prelude
import LeanFX2.FX1.Core.Context
import LeanFX2.FX1.Core.Reduction

/-! # FX1/Core/HasType

Root status: Root-FX1 metatheory scaffold.

Typing relation for the minimal FX1 lambda-Pi core.  This file uses relational
environment and context membership instead of host maps or decidable name
equality.  Environment well-formedness, duplicate-name rejection, and
preservation are subsequent M3/M4 obligations.
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

namespace HasDeclaration

/-- Environment weakening: an existing declaration remains available after
adding one newer declaration. -/
theorem weaken
    {environment : Environment}
    {queryName : Name}
    {declaration : Declaration}
    (newDeclaration : Declaration)
    (olderDeclaration : HasDeclaration environment queryName declaration) :
    HasDeclaration
      (Environment.extend environment newDeclaration)
      queryName
      declaration :=
  HasDeclaration.older newDeclaration olderDeclaration

end HasDeclaration

end Environment

namespace Context

/-- Relational lookup for de Bruijn variables.

The older-variable rule weakens the stored type as it passes through a newer
binder.  This is the dependent-context behavior missing from plain
`Context.lookup?`, which is intentionally only a syntactic index probe. -/
inductive HasTypeAt : Context -> Nat -> Expr -> Prop
  /-- The newest binder has the extending type weakened into the extended
  context.  Without this shift, a dependent binder type such as `bvar 0` would
  incorrectly point at the new variable itself rather than the previous
  binder. -/
  | newest
      (context : Context) (typeExpr : Expr) :
      HasTypeAt
        (Context.extend context typeExpr)
        Nat.zero
        (Expr.weaken typeExpr)
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

namespace HasTypeAt

/-- Regression check for dependent context lookup: if the newest binder's type
refers to the previous binder, lookup must shift that reference from `bvar 0`
to `bvar 1` under the new binder. -/
theorem newest_weakened_dependency :
    HasTypeAt
      (Context.extend
        (Context.extend Context.empty (Expr.sort Level.zero))
        (Expr.bvar Nat.zero))
      Nat.zero
      (Expr.bvar (Nat.succ Nat.zero)) :=
  HasTypeAt.newest
    (Context.extend Context.empty (Expr.sort Level.zero))
    (Expr.bvar Nat.zero)

/-- Context weakening for lookup witnesses: an older binder remains available
under a newly added binder, and its type is shifted into the extended context. -/
theorem weaken
    {context : Context}
    {index : Nat}
    {typeExpr : Expr}
    (newTypeExpr : Expr)
    (olderType : HasTypeAt context index typeExpr) :
    HasTypeAt
      (Context.extend context newTypeExpr)
      (Nat.succ index)
      (Expr.weaken typeExpr) :=
  HasTypeAt.older newTypeExpr olderType

end HasTypeAt

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
  /-- Conversion changes the target type along common-reduct definitional
  equality. -/
  | conv
      {context : Context}
      {expression sourceTypeExpr targetTypeExpr : Expr}
      (expressionHasSourceType :
        HasType environment context expression sourceTypeExpr)
      (typesDefEq : DefEq environment sourceTypeExpr targetTypeExpr) :
      HasType
        environment
        context
        expression
        targetTypeExpr

namespace HasType

/-- Typing is stable when the environment is extended by one newer
declaration. -/
theorem weaken_environment
    {environment : Environment}
    {context : Context}
    {expression typeExpr : Expr}
    (newDeclaration : Declaration)
    (typingDerivation :
      HasType environment context expression typeExpr) :
    HasType
      (Environment.extend environment newDeclaration)
      context
      expression
      typeExpr :=
  match typingDerivation with
  | HasType.sort context sortLevel =>
      HasType.sort context sortLevel
  | HasType.var variableType =>
      HasType.var variableType
  | HasType.const declarationMember =>
      HasType.const
        (Environment.HasDeclaration.weaken newDeclaration declarationMember)
  | HasType.pi domainHasSort bodyHasSort =>
      HasType.pi
        (weaken_environment newDeclaration domainHasSort)
        (weaken_environment newDeclaration bodyHasSort)
  | HasType.lam domainHasSort bodyHasType =>
      HasType.lam
        (weaken_environment newDeclaration domainHasSort)
        (weaken_environment newDeclaration bodyHasType)
  | HasType.app functionHasPi argumentHasDomain =>
      HasType.app
        (weaken_environment newDeclaration functionHasPi)
        (weaken_environment newDeclaration argumentHasDomain)
  | HasType.conv expressionHasSourceType typesDefEq =>
      HasType.conv
        (weaken_environment newDeclaration expressionHasSourceType)
        (DefEq.weaken_environment newDeclaration typesDefEq)

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

/-- In a one-variable context, the identity function over `Sort 0` applied to
the newest variable has type `Sort 0`.

This is a small beta-preservation regression for the M3 spine: the source term
uses lambda introduction, application elimination, de Bruijn lookup, and the
`subst0` codomain computation. -/
theorem identityAppNewestVar_sourceHasType
    (environment : Environment) :
    HasType
      environment
      (Context.extend Context.empty (Expr.sort Level.zero))
      (Expr.app
        (Expr.lam (Expr.sort Level.zero) (Expr.bvar Nat.zero))
        (Expr.bvar Nat.zero))
      (Expr.sort Level.zero) :=
  HasType.app
    (functionHasPi :=
      HasType.lam
        (HasType.sort
          (Context.extend Context.empty (Expr.sort Level.zero))
          Level.zero)
        (HasType.var
          (Context.HasTypeAt.newest
            (Context.extend Context.empty (Expr.sort Level.zero))
            (Expr.sort Level.zero))))
    (argumentHasDomain :=
      HasType.var
        (Context.HasTypeAt.newest Context.empty (Expr.sort Level.zero)))

/-- The beta target of `identityAppNewestVar_sourceHasType` has the same
`Sort 0` type in the same context. -/
theorem identityAppNewestVar_targetHasType
    (environment : Environment) :
    HasType
      environment
      (Context.extend Context.empty (Expr.sort Level.zero))
      (Expr.bvar Nat.zero)
      (Expr.sort Level.zero) :=
  HasType.var
    (Context.HasTypeAt.newest Context.empty (Expr.sort Level.zero))

/-- The source term in `identityAppNewestVar_sourceHasType` beta-reduces to
the target term in `identityAppNewestVar_targetHasType`. -/
theorem identityAppNewestVar_betaStep :
    Step
      (Expr.app
        (Expr.lam (Expr.sort Level.zero) (Expr.bvar Nat.zero))
        (Expr.bvar Nat.zero))
      (Expr.bvar Nat.zero) :=
  Step.beta_newest_bvar
    (Expr.sort Level.zero)
    (Expr.bvar Nat.zero)

end HasType

end LeanFX2.FX1
