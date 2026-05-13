prelude
import LeanFX2.FX1.Core.Check.CheckInferApp
import LeanFX2.FX1.Core.Check.CheckInferApp

/-! # LeanFX2.FX1.Core.Check.CheckEntry

FX1 runtime-facing checker entry points: `checkCore?` plus its variable
and sort soundness lemmas, the proof-carrying `inferResult?` /
`infer?` / `check?` drivers with aggregate soundness, and a closed
beta-redex smoke battery exercising conversion through the public API.

## Root status

Root-FX1 checker entry slice. -/

namespace LeanFX2.FX1

namespace Expr

/-- Executable checking against an expected type without proof payloads. -/
def checkCore? (environment : Environment) (context : Context)
    (expression expectedTypeExpr : Expr) : Bool :=
  Expr.checkBoolFromCoreType?
    environment
    expectedTypeExpr
    (Expr.inferCore? environment context expression)

/-- Runtime-facing checking is sound whenever the accepted runtime-facing
inference result is already known sound. -/
theorem checkCore_of_inferCore_sound
    {environment : Environment}
    {context : Context}
    {expression inferredTypeExpr expectedTypeExpr : Expr}
    (inferenceSucceeded :
      Eq
        (Expr.inferCore? environment context expression)
        (some inferredTypeExpr))
    (inferredTypeDerivation :
      HasType environment context expression inferredTypeExpr)
    (checkingSucceeded :
      Eq
        (Expr.checkCore?
          environment
          context
          expression
          expectedTypeExpr)
        true) :
    HasType environment context expression expectedTypeExpr :=
  let projectedEquality :
      Eq (Expr.isDefEq environment inferredTypeExpr expectedTypeExpr) true :=
    Eq.trans
      (Eq.symm
        (congrArg
          (Expr.checkBoolFromCoreType? environment expectedTypeExpr)
          inferenceSucceeded))
      checkingSucceeded
  HasType.conv
    inferredTypeDerivation
    (Expr.isDefEq_sound_defEq projectedEquality)

/-- Soundness of runtime-facing checking for the accepted no-constant
fragment. -/
theorem checkCore_sound
    {environment : Environment}
    {context : Context}
    {expression expectedTypeExpr : Expr}
    (checkingSucceeded :
      Eq
        (Expr.checkCore?
          environment
          context
          expression
          expectedTypeExpr)
        true) :
    HasType environment context expression expectedTypeExpr :=
  match inferenceSucceeded :
      Expr.inferCore? environment context expression with
  | some _ =>
      Expr.checkCore_of_inferCore_sound
        inferenceSucceeded
        (Expr.inferCore_sound
          (environment := environment)
          (context := context)
          expression
          inferenceSucceeded)
        checkingSucceeded
  | none =>
      let falseEqualsTrue : Eq false true :=
        Eq.trans
          (Eq.symm
            (congrArg
              (Expr.checkBoolFromCoreType? environment expectedTypeExpr)
              inferenceSucceeded))
          checkingSucceeded
      nomatch falseEqualsTrue

/-- Direct soundness for runtime-facing variable checking. -/
theorem checkCore_bvar_sound
    {environment : Environment}
    {context : Context}
    {index : Nat}
    {expectedTypeExpr : Expr}
    (checkingSucceeded :
      Eq
        (Expr.checkCore?
          environment
          context
          (Expr.bvar index)
          expectedTypeExpr)
        true) :
    HasType environment context (Expr.bvar index) expectedTypeExpr :=
  match lookupSucceeded : Context.lookupType? context index with
  | some _ =>
      Expr.checkCore_of_inferCore_sound
        lookupSucceeded
        (Expr.inferCore_bvar_sound lookupSucceeded)
        checkingSucceeded
  | none =>
      let falseEqualsTrue : Eq false true :=
        Eq.trans
          (Eq.symm
            (congrArg
              (Expr.checkBoolFromCoreType? environment expectedTypeExpr)
              lookupSucceeded))
          checkingSucceeded
      nomatch falseEqualsTrue

/-- Direct soundness for runtime-facing sort checking. -/
theorem checkCore_sort_sound
    {environment : Environment}
    {context : Context}
    {sortLevel : Level}
    {expectedTypeExpr : Expr}
    (checkingSucceeded :
      Eq
        (Expr.checkCore?
          environment
          context
          (Expr.sort sortLevel)
          expectedTypeExpr)
        true) :
    HasType environment context (Expr.sort sortLevel) expectedTypeExpr :=
  let inferenceSucceeded :
      Eq
        (Expr.inferCore? environment context (Expr.sort sortLevel))
        (some (Expr.sort (Level.succ sortLevel))) :=
    Eq.refl (some (Expr.sort (Level.succ sortLevel)))
  Expr.checkCore_of_inferCore_sound
    inferenceSucceeded
    (Expr.inferCore_sort_sound inferenceSucceeded)
    checkingSucceeded

/-- Proof-carrying inference for the initial checker fragment. -/
def inferResult?
    (environment : Environment) (context : Context) :
    (expression : Expr) -> Option (InferResult environment context expression)
  | Expr.bvar index =>
      match Context.lookupTypeResult? context index with
      | some lookupResult =>
          some {
            typeExpr := lookupResult.typeExpr
            typeDerivation := HasType.var lookupResult.typeAtIndex
          }
      | none => none
  | Expr.sort sortLevel =>
      some {
        typeExpr := Expr.sort (Level.succ sortLevel)
        typeDerivation := HasType.sort context sortLevel
      }
  | Expr.const constName =>
      match Environment.findByNameResult? environment constName with
      | some lookupResult =>
          some {
            typeExpr := Declaration.typeExpr lookupResult.declaration
            typeDerivation := HasType.const lookupResult.declarationMember
          }
      | none => none
  | Expr.pi domainExpr bodyExpr =>
      match Expr.inferResult? environment context domainExpr with
      | some {
          typeExpr := domainTypeExpr
          typeDerivation := domainTypeDerivation
        } =>
          match domainTypeExpr with
          | Expr.sort domainLevel =>
              match Expr.inferResult?
                  environment
                  (Context.extend context domainExpr)
                  bodyExpr with
              | some {
                  typeExpr := bodyTypeExpr
                  typeDerivation := bodyTypeDerivation
                } =>
                  match bodyTypeExpr with
                  | Expr.sort bodyLevel =>
                      some {
                        typeExpr := Expr.sort
                          (Level.max domainLevel bodyLevel)
                        typeDerivation :=
                          HasType.pi
                            domainTypeDerivation
                            bodyTypeDerivation
                      }
                  | Expr.bvar _ => none
                  | Expr.const _ => none
                  | Expr.pi _ _ => none
                  | Expr.lam _ _ => none
                  | Expr.app _ _ => none
              | none => none
          | Expr.bvar _ => none
          | Expr.const _ => none
          | Expr.pi _ _ => none
          | Expr.lam _ _ => none
          | Expr.app _ _ => none
      | none => none
  | Expr.lam domainExpr bodyExpr =>
      match Expr.inferResult? environment context domainExpr with
      | some {
          typeExpr := domainTypeExpr
          typeDerivation := domainTypeDerivation
        } =>
          match domainTypeExpr with
          | Expr.sort _ =>
              match Expr.inferResult?
                  environment
                  (Context.extend context domainExpr)
                  bodyExpr with
              | some bodyResult =>
                  some {
                    typeExpr := Expr.pi domainExpr bodyResult.typeExpr
                    typeDerivation :=
                      HasType.lam
                        domainTypeDerivation
                        bodyResult.typeDerivation
                  }
              | none => none
          | Expr.bvar _ => none
          | Expr.const _ => none
          | Expr.pi _ _ => none
          | Expr.lam _ _ => none
          | Expr.app _ _ => none
      | none => none
  | Expr.app functionExpr argumentExpr =>
      match Expr.inferResult? environment context functionExpr with
      | some {
          typeExpr := functionTypeExpr
          typeDerivation := functionTypeDerivation
        } =>
          match functionTypeExpr with
          | Expr.pi domainExpr bodyTypeExpr =>
              match Expr.inferResult? environment context argumentExpr with
              | some argumentResult =>
                  match h :
                      Expr.isDefEq
                        environment
                        argumentResult.typeExpr
                        domainExpr with
                  | true =>
                      let argumentHasDomain :
                          HasType
                            environment
                            context
                            argumentExpr
                            domainExpr :=
                        HasType.conv
                          argumentResult.typeDerivation
                          (Expr.isDefEq_sound_defEq h)
                      some {
                        typeExpr :=
                          Expr.subst0 argumentExpr bodyTypeExpr
                        typeDerivation :=
                          HasType.app
                            functionTypeDerivation
                            argumentHasDomain
                      }
                  | false => none
              | none => none
          | Expr.bvar _ => none
          | Expr.sort _ => none
          | Expr.const _ => none
          | Expr.lam _ _ => none
          | Expr.app _ _ => none
      | none => none

/-- Infer the type of an FX1 expression in the initial no-constant checker
fragment. -/
def infer? (environment : Environment) (context : Context)
    (expression : Expr) : Option Expr :=
  Expr.inferTypeFromResult?
    (Expr.inferResult? environment context expression)

/-- Soundness of executable inference. -/
theorem infer?_sound
    {environment : Environment}
    {context : Context}
    {expression inferredTypeExpr : Expr}
    (inferenceSucceeded :
      Eq
        (Expr.infer? environment context expression)
        (some inferredTypeExpr)) :
    HasType environment context expression inferredTypeExpr :=
  match h :
      Expr.inferResult? environment context expression with
  | some inferenceResult =>
      let projectedEquality :
          Eq (some inferenceResult.typeExpr) (some inferredTypeExpr) :=
        Eq.trans
          (Eq.symm
            (congrArg
              Expr.inferTypeFromResult?
              h))
          inferenceSucceeded
      let typeEquality :=
        CheckOption.some_injective projectedEquality
      match typeEquality with
      | Eq.refl _ => inferenceResult.typeDerivation
  | none =>
      let noneEqualsSome :
          Eq (none : Option Expr) (some inferredTypeExpr) :=
        Eq.trans
          (Eq.symm
            (congrArg
              Expr.inferTypeFromResult?
              h))
          inferenceSucceeded
      nomatch noneEqualsSome

/-- Check an expression against an expected type using weak-head
definitional equality. -/
def check? (environment : Environment) (context : Context)
    (expression expectedTypeExpr : Expr) : Bool :=
  Expr.checkBoolFromResult?
    expectedTypeExpr
    (Expr.inferResult? environment context expression)

/-- Soundness of executable checking. -/
theorem check?_sound
    {environment : Environment}
    {context : Context}
    {expression expectedTypeExpr : Expr}
    (checkingSucceeded :
      Eq
        (Expr.check? environment context expression expectedTypeExpr)
        true) :
    HasType environment context expression expectedTypeExpr :=
  match h :
      Expr.inferResult? environment context expression with
  | some inferenceResult =>
      let projectedEquality :
          Eq
            (Expr.isDefEq
              environment
              inferenceResult.typeExpr
              expectedTypeExpr)
            true :=
        Eq.trans
          (Eq.symm
            (congrArg
              (Expr.checkBoolFromResult? expectedTypeExpr)
              h))
          checkingSucceeded
      HasType.conv
        inferenceResult.typeDerivation
        (Expr.isDefEq_sound_defEq projectedEquality)
  | none =>
      let falseEqualsTrue : Eq false true :=
        Eq.trans
          (Eq.symm
            (congrArg
              (Expr.checkBoolFromResult? expectedTypeExpr)
              h))
          checkingSucceeded
      nomatch falseEqualsTrue

/-- A closed type-level beta-redex reducing to `Sort 0`.

This fixture is intentionally syntactically different from `Sort 0`, so it
detects accidental fallback to structural equality in checker conversion. -/
def betaConvertibleSortZeroType : Expr :=
  Expr.app
    (Expr.lam
      (Expr.sort (Level.succ Level.zero))
      (Expr.bvar Nat.zero))
    (Expr.sort Level.zero)

/-- A one-variable context whose newest variable has a beta-convertible type. -/
def betaConvertibleArgumentContext : Context :=
  Context.extend Context.empty Expr.betaConvertibleSortZeroType

/-- Identity application whose argument type is beta-convertible to the
function domain but not syntactically equal to it. -/
def betaConvertibleIdentityApp : Expr :=
  Expr.app
    (Expr.lam (Expr.sort Level.zero) (Expr.bvar Nat.zero))
    (Expr.bvar Nat.zero)

/-- The WHNF equality procedure recognizes the beta-redex fixture as `Sort 0`.
-/
theorem isDefEq_betaConvertibleSortZeroType :
    Eq
      (Expr.isDefEq
        Environment.empty
        Expr.betaConvertibleSortZeroType
        (Expr.sort Level.zero))
      true :=
  Eq.refl true

/-- Runtime inference accepts an application whose argument type is only
beta-convertible to the function domain. -/
theorem inferCore_accepts_betaConvertibleArgumentDomain :
    Eq
      (Expr.inferCore?
        Environment.empty
        Expr.betaConvertibleArgumentContext
        Expr.betaConvertibleIdentityApp)
      (some (Expr.sort Level.zero)) :=
  Eq.refl (some (Expr.sort Level.zero))

/-- Runtime checking accepts a beta-convertible expected type. -/
theorem checkCore_accepts_betaConvertibleExpectedType :
    Eq
      (Expr.checkCore?
        Environment.empty
        Expr.betaConvertibleArgumentContext
        Expr.betaConvertibleIdentityApp
        Expr.betaConvertibleSortZeroType)
      true :=
  Eq.refl true

/-- Proof-carrying inference accepts the same beta-convertible app-domain
case. -/
theorem infer_accepts_betaConvertibleArgumentDomain :
    Eq
      (Expr.infer?
        Environment.empty
        Expr.betaConvertibleArgumentContext
        Expr.betaConvertibleIdentityApp)
      (some (Expr.sort Level.zero)) :=
  Eq.refl (some (Expr.sort Level.zero))

/-- Proof-carrying checking accepts the same beta-convertible expected type
case. -/
theorem check_accepts_betaConvertibleExpectedType :
    Eq
      (Expr.check?
        Environment.empty
        Expr.betaConvertibleArgumentContext
        Expr.betaConvertibleIdentityApp
        Expr.betaConvertibleSortZeroType)
      true :=
  Eq.refl true

end Expr

end LeanFX2.FX1
