prelude
import LeanFX2.FX1.LeanKernel.HasType
/-! # FX1/LeanKernel/Check

First executable Lean-kernel checker fragment.

## Deliverable

This module implements the proof-carrying checker slice for sorts, bound
variables, and constants.  Constructors for functions, lets, projections,
metadata-erasure, inductives, and quotient primitives remain later
LeanKernel-FX1 work.
-/

namespace LeanFX2
namespace FX1.LeanKernel

namespace Environment

/-- Proof-carrying executable constant lookup in a declaration list. -/
structure ConstantLookupResult {level : Nat}
    (constants : List (ConstantSpec level))
    (targetName : Name) : Type where
  constantSpec : ConstantSpec level
  constantMember : HasConstantInList constants targetName constantSpec

/-- Find a constant declaration with a relational membership witness. -/
def findConstantResultInList? {level : Nat}
    (targetName : Name) :
    (constants : List (ConstantSpec level)) ->
      Option (ConstantLookupResult constants targetName)
  | List.nil => Option.none
  | List.cons constantSpec remainingConstants =>
      match Name.eqResult constantSpec.constantName targetName with
      | EqualityResult.equal nameEquality =>
          Option.some {
            constantSpec := constantSpec
            constantMember :=
              nameEquality ▸
                (HasConstantInList.newest constantSpec remainingConstants)
          }
      | EqualityResult.notEqual =>
          match findConstantResultInList? targetName remainingConstants with
          | Option.none => Option.none
          | Option.some olderResult =>
              Option.some {
                constantSpec := olderResult.constantSpec
                constantMember :=
                  HasConstantInList.older constantSpec
                    olderResult.constantMember
              }

/-- Find a constant declaration in an environment with a membership witness. -/
def findConstantResult? {level : Nat}
    (environment : Environment level)
    (targetName : Name) :
    Option (ConstantLookupResult environment.constants targetName) :=
  findConstantResultInList? targetName environment.constants

end Environment

namespace Context

/-- Proof-carrying executable lookup for a de Bruijn index. -/
structure LookupTypeResult {level scope : Nat}
    (context : Context level scope)
    (position : Nat) : Type where
  typeExpr : Expr level scope
  typeAtPosition : HasTypeAt context position typeExpr

/-- Find a local type in a context-entry list with a relational lookup witness. -/
def lookupTypeResultInEntries? {level scope : Nat} :
    (entries : List (Expr level scope)) ->
    (position : Nat) ->
      Option
        (LookupTypeResult
          ({ entries := entries } : Context level scope)
          position)
  | List.nil, _position => Option.none
  | List.cons typeExpr remainingEntries, Nat.zero =>
      Option.some {
        typeExpr := typeExpr
        typeAtPosition :=
          HasTypeAt.newest
            ({ entries := remainingEntries } : Context level scope)
            typeExpr
      }
  | List.cons newerTypeExpr remainingEntries, Nat.succ olderPosition =>
      match lookupTypeResultInEntries? remainingEntries olderPosition with
      | Option.none => Option.none
      | Option.some olderResult =>
          Option.some {
            typeExpr := olderResult.typeExpr
            typeAtPosition :=
              HasTypeAt.older newerTypeExpr olderResult.typeAtPosition
          }

/-- Find a local type in a context with a relational lookup witness. -/
def lookupTypeResult? {level scope : Nat}
    (context : Context level scope)
    (position : Nat) : Option (LookupTypeResult context position) :=
  match context with
  | { entries := entries } => lookupTypeResultInEntries? entries position

end Context

namespace Expr

/-- Proof-carrying inference result for the current Lean-kernel fragment. -/
structure InferResult {level scope : Nat}
    (environment : Environment level)
    (context : Context level scope)
    (expression : Expr level scope) : Type where
  typeExpr : Expr level scope
  typeDerivation : HasType environment context expression typeExpr

/-- Forget the proof payload of a proof-carrying inference result. -/
def inferTypeFromResult? {level scope : Nat}
    {environment : Environment level}
    {context : Context level scope}
    {expression : Expr level scope} :
    Option (InferResult environment context expression) ->
      Option (Expr level scope)
  | Option.none => Option.none
  | Option.some result => Option.some result.typeExpr

/-- Infer the type of the current Lean-kernel checker fragment.

All unsupported expression forms are rejected.  This is intentionally
conservative: accepting fewer expressions is sound, while accepting an
unjustified Lean expression would enlarge the trusted kernel claim. -/
def inferResult? {level scope : Nat}
    (environment : Environment level)
    (context : Context level scope) :
    (expression : Expr level scope) ->
      Option (InferResult environment context expression)
  | Expr.bvar position =>
      match Context.lookupTypeResult? context position with
      | Option.none => Option.none
      | Option.some lookupResult =>
          Option.some {
            typeExpr := lookupResult.typeExpr
            typeDerivation := HasType.bvar lookupResult.typeAtPosition
          }
  | Expr.fvar _fvarId => Option.none
  | Expr.mvar _mvarId => Option.none
  | Expr.sort sortLevel =>
      Option.some {
        typeExpr := Expr.sort (Level.succ sortLevel)
        typeDerivation := HasType.sort sortLevel
      }
  | Expr.const constName levels =>
      match Environment.findConstantResult? environment constName with
      | Option.none => Option.none
      | Option.some lookupResult =>
          Option.some {
            typeExpr :=
              Expr.recontextualize lookupResult.constantSpec.typeExpr
            typeDerivation :=
              HasType.const
                (levels := levels)
                lookupResult.constantMember
          }
  | Expr.app _functionExpr _argumentExpr => Option.none
  | Expr.lam _binderName _domainExpr _bodyExpr _binderInfo => Option.none
  | Expr.forallE _binderName _domainExpr _bodyExpr _binderInfo => Option.none
  | Expr.letE _declName _typeExpr _valueExpr _bodyExpr _nondep => Option.none
  | Expr.lit _literal => Option.none
  | Expr.mdata _metadata _bodyExpr => Option.none
  | Expr.proj _structName _fieldIndex _targetExpr => Option.none

/-- Infer a type, erasing the proof-carrying payload. -/
def infer? {level scope : Nat}
    (environment : Environment level)
    (context : Context level scope)
    (expression : Expr level scope) : Option (Expr level scope) :=
  inferTypeFromResult? (inferResult? environment context expression)

/-- Soundness of proof-erasure for inference results. -/
theorem inferTypeFromResult?_sound {level scope : Nat}
    {environment : Environment level}
    {context : Context level scope}
    {expression typeExpr : Expr level scope}
    {maybeResult : Option (InferResult environment context expression)}
    (inferredType :
      Eq (inferTypeFromResult? maybeResult) (Option.some typeExpr)) :
    HasType environment context expression typeExpr :=
  match maybeResult with
  | Option.none => nomatch inferredType
  | Option.some result =>
      match inferredType with
      | Eq.refl _ => result.typeDerivation

/-- Soundness of the current Lean-kernel type inference fragment. -/
theorem infer?_sound {level scope : Nat}
    {environment : Environment level}
    {context : Context level scope}
    {expression typeExpr : Expr level scope}
    (inferredType :
      Eq (infer? environment context expression) (Option.some typeExpr)) :
    HasType environment context expression typeExpr :=
  inferTypeFromResult?_sound inferredType

/-- The current checker is inference for its accepted fragment. -/
def check? {level scope : Nat}
    (environment : Environment level)
    (context : Context level scope)
    (expression : Expr level scope) : Option (Expr level scope) :=
  infer? environment context expression

/-- Soundness of the current Lean-kernel checker fragment. -/
theorem check?_sound {level scope : Nat}
    {environment : Environment level}
    {context : Context level scope}
    {expression typeExpr : Expr level scope}
    (checkedType :
      Eq (check? environment context expression) (Option.some typeExpr)) :
    HasType environment context expression typeExpr :=
  infer?_sound checkedType

end Expr

/-- Public checker entrypoint for the current Lean-kernel fragment. -/
def check {level scope : Nat}
    (environment : Environment level)
    (context : Context level scope)
    (expression : Expr level scope) : Option (Expr level scope) :=
  Expr.check? environment context expression

end FX1.LeanKernel
end LeanFX2
