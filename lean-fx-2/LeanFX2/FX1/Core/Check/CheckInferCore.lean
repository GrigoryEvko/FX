prelude
import LeanFX2.FX1.Core.Check.CheckReduction

/-! # LeanFX2.FX1.Core.Check.CheckInferCore

FX1 executable core type-inference: `InferResult` envelope, the
`inferCore?` driver, and per-constructor branch soundness for variables,
sorts, constants, Pi types, and lambdas.

## Root status

Root-FX1 checker inferCore slice. -/

namespace LeanFX2.FX1

namespace Expr

/-- A successful checker inference paired with the relational typing
derivation it justifies. -/
structure InferResult
    (environment : Environment) (context : Context) (expression : Expr) :
    Type where
  typeExpr : Expr
  typeDerivation : HasType environment context expression typeExpr

/-- Project a proof-carrying inference result to the executable inferred
type. -/
def inferTypeFromResult?
    {environment : Environment} {context : Context} {expression : Expr} :
    Option (InferResult environment context expression) -> Option Expr
  | some inferenceResult => some inferenceResult.typeExpr
  | none => none

/-- Project a proof-carrying inference result to the executable check result
against an expected type. -/
def checkBoolFromResult?
    {environment : Environment} {context : Context} {expression : Expr}
    (expectedTypeExpr : Expr) :
    Option (InferResult environment context expression) -> Bool
  | some inferenceResult =>
      Expr.isDefEq environment inferenceResult.typeExpr expectedTypeExpr
  | none => false

/-- Project a runtime-facing optional inferred type to the executable check
result against an expected type. -/
def checkBoolFromCoreType?
    (environment : Environment) (expectedTypeExpr : Expr) :
    Option Expr -> Bool
  | some inferredTypeExpr =>
      Expr.isDefEq environment inferredTypeExpr expectedTypeExpr
  | none => false

/-- Executable inference without proof payloads.

This is the runtime-facing checker path: it is intentionally separate from
`inferResult?`, whose dependent result carries typing derivations and currently
uses Lean-generated dependent-recursion infrastructure. -/
def inferCore? (environment : Environment) (context : Context) :
    Expr -> Option Expr
  | Expr.bvar index =>
      Context.lookupType? context index
  | Expr.sort sortLevel =>
      some (Expr.sort (Level.succ sortLevel))
  | Expr.const constName =>
      Environment.findTypeByName? environment constName
  | Expr.pi domainExpr bodyExpr =>
      match Expr.inferCore? environment context domainExpr with
      | some (Expr.sort domainLevel) =>
          match Expr.inferCore?
              environment
              (Context.extend context domainExpr)
              bodyExpr with
          | some (Expr.sort bodyLevel) =>
              some (Expr.sort (Level.max domainLevel bodyLevel))
          | some (Expr.bvar _) => none
          | some (Expr.const _) => none
          | some (Expr.pi _ _) => none
          | some (Expr.lam _ _) => none
          | some (Expr.app _ _) => none
          | none => none
      | some (Expr.bvar _) => none
      | some (Expr.const _) => none
      | some (Expr.pi _ _) => none
      | some (Expr.lam _ _) => none
      | some (Expr.app _ _) => none
      | none => none
  | Expr.lam domainExpr bodyExpr =>
      match Expr.inferCore? environment context domainExpr with
      | some (Expr.sort _) =>
          match Expr.inferCore?
              environment
              (Context.extend context domainExpr)
              bodyExpr with
          | some bodyTypeExpr =>
              some (Expr.pi domainExpr bodyTypeExpr)
          | none => none
      | some (Expr.bvar _) => none
      | some (Expr.const _) => none
      | some (Expr.pi _ _) => none
      | some (Expr.lam _ _) => none
      | some (Expr.app _ _) => none
      | none => none
  | Expr.app functionExpr argumentExpr =>
      match Expr.inferCore? environment context functionExpr with
      | some (Expr.pi domainExpr bodyTypeExpr) =>
          match Expr.inferCore? environment context argumentExpr with
          | some argumentTypeExpr =>
              match Expr.isDefEq environment argumentTypeExpr domainExpr with
              | true => some (Expr.subst0 argumentExpr bodyTypeExpr)
              | false => none
          | none => none
      | some (Expr.bvar _) => none
      | some (Expr.sort _) => none
      | some (Expr.const _) => none
      | some (Expr.lam _ _) => none
      | some (Expr.app _ _) => none
      | none => none

/-- Direct soundness for runtime-facing variable inference. -/
theorem inferCore_bvar_sound
    {environment : Environment}
    {context : Context}
    {index : Nat}
    {inferredTypeExpr : Expr}
    (inferenceSucceeded :
      Eq
        (Expr.inferCore? environment context (Expr.bvar index))
        (some inferredTypeExpr)) :
    HasType environment context (Expr.bvar index) inferredTypeExpr :=
  HasType.var
    (Context.lookupType_sound inferenceSucceeded)

/-- Direct soundness for runtime-facing sort inference. -/
theorem inferCore_sort_sound
    {environment : Environment}
    {context : Context}
    {sortLevel : Level}
    {inferredTypeExpr : Expr}
    (inferenceSucceeded :
      Eq
        (Expr.inferCore? environment context (Expr.sort sortLevel))
        (some inferredTypeExpr)) :
    HasType environment context (Expr.sort sortLevel) inferredTypeExpr :=
  let typeEquality :=
    CheckOption.some_injective inferenceSucceeded
  match typeEquality with
  | Eq.refl _ => HasType.sort context sortLevel

/-- Direct soundness for runtime-facing constant inference. -/
theorem inferCore_const_sound
    {environment : Environment}
    {context : Context}
    {constName : Name}
    {inferredTypeExpr : Expr}
    (inferenceSucceeded :
      Eq
        (Expr.inferCore? environment context (Expr.const constName))
        (some inferredTypeExpr)) :
    HasType environment context (Expr.const constName) inferredTypeExpr :=
  let lookupSound :=
    Environment.findTypeByName_sound inferenceSucceeded
  let declaredTypeExpr := Declaration.typeExpr lookupSound.declaration
  let constHasDeclaredType :
      HasType environment context (Expr.const constName) declaredTypeExpr :=
    HasType.const lookupSound.declarationMember
  let typeEquality : Eq declaredTypeExpr inferredTypeExpr :=
    lookupSound.typeEquality
  Eq.ndrec
    (motive := fun currentTypeExpr =>
      HasType environment context (Expr.const constName) currentTypeExpr)
    constHasDeclaredType
    typeEquality

/-- Branch soundness for runtime-facing Pi inference.

This is the constructor-local part of full `inferCore?` soundness: the caller
must still provide soundness for the recursive domain and body inferences. -/
theorem inferCore_pi_from_branch_sound
    {environment : Environment}
    {context : Context}
    {domainExpr bodyExpr inferredTypeExpr : Expr}
    {domainLevel bodyLevel : Level}
    (domainInference :
      Eq
        (Expr.inferCore? environment context domainExpr)
        (some (Expr.sort domainLevel)))
    (bodyInference :
      Eq
        (Expr.inferCore?
          environment
          (Context.extend context domainExpr)
          bodyExpr)
        (some (Expr.sort bodyLevel)))
    (domainHasSort :
      HasType environment context domainExpr (Expr.sort domainLevel))
    (bodyHasSort :
      HasType
        environment
        (Context.extend context domainExpr)
        bodyExpr
        (Expr.sort bodyLevel))
    (inferenceSucceeded :
      Eq
        (Expr.inferCore?
          environment
          context
          (Expr.pi domainExpr bodyExpr))
        (some inferredTypeExpr)) :
    HasType
      environment
      context
      (Expr.pi domainExpr bodyExpr)
      inferredTypeExpr :=
  let branchEquality :
      Eq
        (Expr.inferCore?
          environment
          context
          (Expr.pi domainExpr bodyExpr))
        (some (Expr.sort (Level.max domainLevel bodyLevel))) :=
    let bodyCase : Option Expr -> Option Expr
      | some (Expr.sort currentBodyLevel) =>
          some (Expr.sort (Level.max domainLevel currentBodyLevel))
      | some (Expr.bvar _) => none
      | some (Expr.const _) => none
      | some (Expr.pi _ _) => none
      | some (Expr.lam _ _) => none
      | some (Expr.app _ _) => none
      | none => none
    let domainCase : Option Expr -> Option Expr
      | some (Expr.sort currentDomainLevel) =>
          match Expr.inferCore?
              environment
              (Context.extend context domainExpr)
              bodyExpr with
          | some (Expr.sort currentBodyLevel) =>
              some
                (Expr.sort
                  (Level.max currentDomainLevel currentBodyLevel))
          | some (Expr.bvar _) => none
          | some (Expr.const _) => none
          | some (Expr.pi _ _) => none
          | some (Expr.lam _ _) => none
          | some (Expr.app _ _) => none
          | none => none
      | some (Expr.bvar _) => none
      | some (Expr.const _) => none
      | some (Expr.pi _ _) => none
      | some (Expr.lam _ _) => none
      | some (Expr.app _ _) => none
      | none => none
    let domainCaseEquality :
        Eq
          (Expr.inferCore?
            environment
            context
            (Expr.pi domainExpr bodyExpr))
          (domainCase
            (Expr.inferCore? environment context domainExpr)) :=
      Eq.refl
        (Expr.inferCore?
          environment
          context
          (Expr.pi domainExpr bodyExpr))
    let domainCaseProjected :=
      congrArg domainCase domainInference
    let bodyCaseEquality :
        Eq
          (domainCase (some (Expr.sort domainLevel)))
          (bodyCase
            (Expr.inferCore?
              environment
              (Context.extend context domainExpr)
              bodyExpr)) :=
      Eq.refl
        (bodyCase
          (Expr.inferCore?
            environment
            (Context.extend context domainExpr)
            bodyExpr))
    let bodyCaseProjected :=
      congrArg bodyCase bodyInference
    Eq.trans
      domainCaseEquality
      (Eq.trans
        domainCaseProjected
        (Eq.trans bodyCaseEquality bodyCaseProjected))
  let typeEquality :=
    CheckOption.some_injective
      (Eq.trans (Eq.symm branchEquality) inferenceSucceeded)
  match typeEquality with
  | Eq.refl _ => HasType.pi domainHasSort bodyHasSort

/-- Branch soundness for runtime-facing lambda inference.

This proves the lambda branch once the domain sort and body type recursive
inferences have already been justified. -/
theorem inferCore_lam_from_branch_sound
    {environment : Environment}
    {context : Context}
    {domainExpr bodyExpr bodyTypeExpr inferredTypeExpr : Expr}
    {domainLevel : Level}
    (domainInference :
      Eq
        (Expr.inferCore? environment context domainExpr)
        (some (Expr.sort domainLevel)))
    (bodyInference :
      Eq
        (Expr.inferCore?
          environment
          (Context.extend context domainExpr)
          bodyExpr)
        (some bodyTypeExpr))
    (domainHasSort :
      HasType environment context domainExpr (Expr.sort domainLevel))
    (bodyHasType :
      HasType
        environment
        (Context.extend context domainExpr)
        bodyExpr
        bodyTypeExpr)
    (inferenceSucceeded :
      Eq
        (Expr.inferCore?
          environment
          context
          (Expr.lam domainExpr bodyExpr))
        (some inferredTypeExpr)) :
    HasType
      environment
      context
      (Expr.lam domainExpr bodyExpr)
      inferredTypeExpr :=
  let branchEquality :
      Eq
        (Expr.inferCore?
          environment
          context
          (Expr.lam domainExpr bodyExpr))
        (some (Expr.pi domainExpr bodyTypeExpr)) :=
    let bodyCase : Option Expr -> Option Expr
      | some currentBodyTypeExpr =>
          some (Expr.pi domainExpr currentBodyTypeExpr)
      | none => none
    let domainCase : Option Expr -> Option Expr
      | some (Expr.sort _) =>
          bodyCase
            (Expr.inferCore?
              environment
              (Context.extend context domainExpr)
              bodyExpr)
      | some (Expr.bvar _) => none
      | some (Expr.const _) => none
      | some (Expr.pi _ _) => none
      | some (Expr.lam _ _) => none
      | some (Expr.app _ _) => none
      | none => none
    let domainCaseEquality :
        Eq
          (Expr.inferCore?
            environment
            context
            (Expr.lam domainExpr bodyExpr))
          (domainCase
            (Expr.inferCore? environment context domainExpr)) :=
      Eq.refl
        (Expr.inferCore?
          environment
          context
          (Expr.lam domainExpr bodyExpr))
    let domainCaseProjected :=
      congrArg domainCase domainInference
    let bodyCaseEquality :
        Eq
          (domainCase (some (Expr.sort domainLevel)))
          (bodyCase
            (Expr.inferCore?
              environment
              (Context.extend context domainExpr)
              bodyExpr)) :=
      Eq.refl
        (bodyCase
          (Expr.inferCore?
            environment
            (Context.extend context domainExpr)
            bodyExpr))
    let bodyCaseProjected :=
      congrArg bodyCase bodyInference
    Eq.trans
      domainCaseEquality
      (Eq.trans
        domainCaseProjected
        (Eq.trans bodyCaseEquality bodyCaseProjected))
  let typeEquality :=
    CheckOption.some_injective
      (Eq.trans (Eq.symm branchEquality) inferenceSucceeded)
  match typeEquality with
  | Eq.refl _ => HasType.lam domainHasSort bodyHasType


end Expr

end LeanFX2.FX1
