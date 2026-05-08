prelude
import LeanFX2.FX1.LeanKernel.Inductive

/-! # FX1/LeanKernel/HasType

Day 0 scaffold for the Lean kernel typing relation.

## Deliverable

This module defines the encoded `HasType` judgment for the current LeanKernel
checker fragment.  It covers sorts, bound variables, constants, forall
formation, and lambda introduction.  Lean application, let, inductive,
projection, literal, metavariable, and free-variable typing belong to later
LeanKernel-FX1 slices.
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

/-- Weaken a list of context entries under one fresh newest binder. -/
def weakenEntries {level scope : Nat} :
    List (Expr level scope) -> List (Expr level (Nat.succ scope))
  | List.nil => List.nil
  | List.cons typeExpr remainingEntries =>
      List.cons (Expr.weaken typeExpr) (weakenEntries remainingEntries)

/-- Weaken every type in a local context under one fresh newest binder. -/
def weaken {level scope : Nat}
    (context : Context level scope) : Context level (Nat.succ scope) where
  entries := weakenEntries context.entries

/-- Extend a context for checking the body under a new Lean binder.

The new binder's type and all older entries are weakened into the body scope,
then the new binder is placed at de Bruijn index zero.
-/
def extendForBinder {level scope : Nat}
    (context : Context level scope)
    (typeExpr : Expr level scope) : Context level (Nat.succ scope) :=
  extend (weaken context) (Expr.weaken typeExpr)

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
fragment.

The local scope is an index, not a fixed parameter, so binder rules can recurse
under the one-binder body scope without leaving the intrinsic judgment.
-/
inductive HasType {level : Nat} :
    {scope : Nat} ->
    (environment : Environment level) ->
    (context : Context level scope) ->
    Expr level scope -> Expr level scope -> Prop
  /-- Lean kernel sorts are typed by their successor sort. -/
  | sort
      {scope : Nat}
      {environment : Environment level}
      {context : Context level scope}
      (sortLevel : Level) :
      HasType
        environment
        context
        (Expr.sort sortLevel)
        (Expr.sort (Level.succ sortLevel))
  /-- Bound variables are typed by local-context lookup. -/
  | bvar
      {scope : Nat}
      {environment : Environment level}
      {context : Context level scope}
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
      {scope : Nat}
      {environment : Environment level}
      {context : Context level scope}
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
  /-- Lean `forallE` formation. -/
  | forallE
      {scope : Nat}
      {environment : Environment level}
      {context : Context level scope}
      {binderName : Name}
      {domainExpr : Expr level scope}
      {bodyExpr : Expr level (Nat.succ scope)}
      {binderInfo : BinderInfo}
      {domainLevel bodyLevel : Level}
      (domainHasSort :
        HasType environment context domainExpr (Expr.sort domainLevel))
      (bodyHasSort :
        HasType
          environment
          (Context.extendForBinder context domainExpr)
          bodyExpr
          (Expr.sort bodyLevel)) :
      HasType
        environment
        context
        (Expr.forallE binderName domainExpr bodyExpr binderInfo)
        (Expr.sort (Level.imax domainLevel bodyLevel))
  /-- Lean lambda introduction against the inferred `forallE` type. -/
  | lam
      {scope : Nat}
      {environment : Environment level}
      {context : Context level scope}
      {binderName : Name}
      {domainExpr : Expr level scope}
      {bodyExpr bodyTypeExpr : Expr level (Nat.succ scope)}
      {binderInfo : BinderInfo}
      {domainLevel : Level}
      (domainHasSort :
        HasType environment context domainExpr (Expr.sort domainLevel))
      (bodyHasType :
        HasType
          environment
          (Context.extendForBinder context domainExpr)
          bodyExpr
          bodyTypeExpr) :
      HasType
        environment
        context
        (Expr.lam binderName domainExpr bodyExpr binderInfo)
        (Expr.forallE binderName domainExpr bodyTypeExpr binderInfo)
  /-- Lean function application instantiates the codomain with the argument.

  The function position has Pi type `forallE binderName domainExpr bodyTypeExpr
  binderInfo`; the argument is checked against `domainExpr`; the application's
  type is the body with the newest bound variable instantiated by the argument.
  This is the standard Lean-kernel application rule, mechanised intrinsically:
  the codomain instantiation uses `Expr.instantiate` rather than a side
  condition on the substitution metafunction. -/
  | app
      {scope : Nat}
      {environment : Environment level}
      {context : Context level scope}
      {functionExpr argumentExpr : Expr level scope}
      {binderName : Name}
      {domainExpr : Expr level scope}
      {bodyTypeExpr : Expr level (Nat.succ scope)}
      {binderInfo : BinderInfo}
      (functionHasPi :
        HasType
          environment
          context
          functionExpr
          (Expr.forallE binderName domainExpr bodyTypeExpr binderInfo))
      (argumentHasDomain :
        HasType environment context argumentExpr domainExpr) :
      HasType
        environment
        context
        (Expr.app functionExpr argumentExpr)
        (Expr.instantiate bodyTypeExpr argumentExpr)
  /-- Lean `letE` introduction.

  The ascribed type must inhabit a sort, the bound value must match it, and the
  body is checked under one fresh binder typed by the ascribed type.  The
  resulting type is the body type with the newest bound variable instantiated
  by the bound value, mirroring application's codomain reduction.  This keeps
  `letE` a sound surface form for definitional unfolding without introducing a
  separate definitional reduction rule at this slice. -/
  | letE
      {scope : Nat}
      {environment : Environment level}
      {context : Context level scope}
      {declName : Name}
      {ascribedTypeExpr valueExpr : Expr level scope}
      {bodyExpr bodyTypeExpr : Expr level (Nat.succ scope)}
      {ascribedTypeLevel : Level}
      {nondep : Bool}
      (ascribedTypeHasSort :
        HasType
          environment
          context
          ascribedTypeExpr
          (Expr.sort ascribedTypeLevel))
      (valueHasAscribedType :
        HasType environment context valueExpr ascribedTypeExpr)
      (bodyHasType :
        HasType
          environment
          (Context.extendForBinder context ascribedTypeExpr)
          bodyExpr
          bodyTypeExpr) :
      HasType
        environment
        context
        (Expr.letE declName ascribedTypeExpr valueExpr bodyExpr nondep)
        (Expr.instantiate bodyTypeExpr valueExpr)
  /-- Metadata-wrapped expressions are typed by their inner body.

  Lean's `mdata` is a transparent annotation node that carries reviewer hints
  but contributes no operational meaning.  This rule mirrors Lean's kernel by
  forwarding the inner derivation unchanged. -/
  | mdata
      {scope : Nat}
      {environment : Environment level}
      {context : Context level scope}
      {metadata : MData}
      {bodyExpr typeExpr : Expr level scope}
      (bodyHasType : HasType environment context bodyExpr typeExpr) :
      HasType
        environment
        context
        (Expr.mdata metadata bodyExpr)
        typeExpr
  /-- Natural-number literals are typed by the canonical `Nat` constant.

  This rule pins the canonical primitive name rather than performing an
  environment lookup so the soundness theorem stays definitionally pinned.
  A later environment well-formedness pass must require `Expr.natTypeName` to
  resolve to a primitive `Nat` declaration with the expected shape. -/
  | litNat
      {scope : Nat}
      {environment : Environment level}
      {context : Context level scope}
      (literalValue : Nat) :
      HasType
        environment
        context
        (Expr.lit (Literal.natVal literalValue))
        (Expr.const Expr.natTypeName List.nil)
  /-- String-atom literals are typed by the canonical `String` constant.

  Like `litNat`, this rule pins a canonical primitive name (`Expr.stringTypeName`)
  rather than performing an environment lookup; environment well-formedness
  enforcement is deferred. -/
  | litStrAtom
      {scope : Nat}
      {environment : Environment level}
      {context : Context level scope}
      (literalAtomId : Nat) :
      HasType
        environment
        context
        (Expr.lit (Literal.strAtomVal literalAtomId))
        (Expr.const Expr.stringTypeName List.nil)

end FX1.LeanKernel
end LeanFX2
