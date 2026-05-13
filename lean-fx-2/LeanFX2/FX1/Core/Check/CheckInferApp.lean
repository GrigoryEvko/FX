prelude
import LeanFX2.FX1.Core.Check.CheckInferCore

/-! # LeanFX2.FX1.Core.Check.CheckInferApp

FX1 executable core inference for the application case: the heaviest
branch (function inference + Pi destructuring + argument compatibility),
the impossible-branch lemma `inferCore_none_absurd`, and the aggregate
soundness theorem `inferCore_sound`.

## Root status

Root-FX1 checker app-inference slice. -/

namespace LeanFX2.FX1

namespace Expr

/-- Branch soundness for runtime-facing application inference.

This proves the application branch once recursive inference has established a
Pi-typed function and a checker-equal argument type. -/
theorem inferCore_app_from_branch_sound
    {environment : Environment}
    {context : Context}
    {functionExpr argumentExpr domainExpr bodyTypeExpr argumentTypeExpr
      inferredTypeExpr : Expr}
    (functionInference :
      Eq
        (Expr.inferCore? environment context functionExpr)
        (some (Expr.pi domainExpr bodyTypeExpr)))
    (argumentInference :
      Eq
        (Expr.inferCore? environment context argumentExpr)
        (some argumentTypeExpr))
    (argumentTypeCheck :
      Eq (Expr.isDefEq environment argumentTypeExpr domainExpr) true)
    (functionHasPi :
      HasType
        environment
        context
        functionExpr
        (Expr.pi domainExpr bodyTypeExpr))
    (argumentHasInferredType :
      HasType environment context argumentExpr argumentTypeExpr)
    (inferenceSucceeded :
      Eq
        (Expr.inferCore?
          environment
          context
          (Expr.app functionExpr argumentExpr))
        (some inferredTypeExpr)) :
    HasType
      environment
      context
      (Expr.app functionExpr argumentExpr)
      inferredTypeExpr :=
  let argumentHasDomain :
      HasType environment context argumentExpr domainExpr :=
    HasType.conv
      argumentHasInferredType
      (Expr.isDefEq_sound_defEq argumentTypeCheck)
  let branchEquality :
      Eq
        (Expr.inferCore?
          environment
          context
          (Expr.app functionExpr argumentExpr))
        (some (Expr.subst0 argumentExpr bodyTypeExpr)) :=
    let checkCase : Bool -> Option Expr
      | true => some (Expr.subst0 argumentExpr bodyTypeExpr)
      | false => none
    let argumentCase : Option Expr -> Option Expr
      | some currentArgumentTypeExpr =>
          checkCase
            (Expr.isDefEq environment currentArgumentTypeExpr domainExpr)
      | none => none
    let functionCase : Option Expr -> Option Expr
      | some (Expr.pi currentDomainExpr currentBodyTypeExpr) =>
          match Expr.inferCore? environment context argumentExpr with
          | some currentArgumentTypeExpr =>
              match Expr.isDefEq
                  environment
                  currentArgumentTypeExpr
                  currentDomainExpr with
              | true =>
                  some (Expr.subst0 argumentExpr currentBodyTypeExpr)
              | false => none
          | none => none
      | some (Expr.bvar _) => none
      | some (Expr.sort _) => none
      | some (Expr.const _) => none
      | some (Expr.lam _ _) => none
      | some (Expr.app _ _) => none
      | none => none
    let functionCaseEquality :
        Eq
          (Expr.inferCore?
            environment
            context
            (Expr.app functionExpr argumentExpr))
          (functionCase
            (Expr.inferCore? environment context functionExpr)) :=
      Eq.refl
        (Expr.inferCore?
          environment
          context
          (Expr.app functionExpr argumentExpr))
    let functionCaseProjected :=
      congrArg functionCase functionInference
    let argumentCaseEquality :
        Eq
          (functionCase (some (Expr.pi domainExpr bodyTypeExpr)))
          (argumentCase
            (Expr.inferCore? environment context argumentExpr)) :=
      Eq.refl
        (argumentCase
          (Expr.inferCore? environment context argumentExpr))
    let argumentCaseProjected :=
      congrArg argumentCase argumentInference
    let checkCaseEquality :
        Eq
          (argumentCase (some argumentTypeExpr))
          (checkCase
            (Expr.isDefEq environment argumentTypeExpr domainExpr)) :=
      Eq.refl
        (checkCase
          (Expr.isDefEq environment argumentTypeExpr domainExpr))
    let checkCaseProjected :=
      congrArg checkCase argumentTypeCheck
    Eq.trans
      functionCaseEquality
      (Eq.trans
        functionCaseProjected
        (Eq.trans
          argumentCaseEquality
          (Eq.trans argumentCaseProjected
            (Eq.trans checkCaseEquality checkCaseProjected))))
  let typeEquality :=
    CheckOption.some_injective
      (Eq.trans (Eq.symm branchEquality) inferenceSucceeded)
  match typeEquality with
  | Eq.refl _ => HasType.app functionHasPi argumentHasDomain

/-- Turn an impossible runtime-facing inference failure into the requested
typing result.  All callers must provide both the computed `none` branch and
the contradictory accepted `some` result. -/
theorem inferCore_none_absurd
    {environment : Environment}
    {context : Context}
    {expression inferredTypeExpr : Expr}
    (inferenceFailed :
      Eq (Expr.inferCore? environment context expression) none)
    (inferenceSucceeded :
      Eq
        (Expr.inferCore? environment context expression)
        (some inferredTypeExpr)) :
    HasType environment context expression inferredTypeExpr :=
  let noneEqualsSome :=
    Eq.trans (Eq.symm inferenceFailed) inferenceSucceeded
  nomatch noneEqualsSome

/-- Soundness of runtime-facing core inference for the accepted no-constant
fragment. -/
theorem inferCore_sound
    {environment : Environment}
    {context : Context} :
    (expression : Expr) -> {inferredTypeExpr : Expr} ->
      Eq
        (Expr.inferCore? environment context expression)
        (some inferredTypeExpr) ->
      HasType environment context expression inferredTypeExpr
  | Expr.bvar _, _, inferenceSucceeded =>
      inferCore_bvar_sound inferenceSucceeded
  | Expr.sort _, _, inferenceSucceeded =>
      inferCore_sort_sound inferenceSucceeded
  | Expr.const _, _, inferenceSucceeded =>
      inferCore_const_sound inferenceSucceeded
  | Expr.pi domainExpr bodyExpr, inferredTypeExpr, inferenceSucceeded =>
      let piBodyCase (domainLevel : Level) : Option Expr -> Option Expr
        | some (Expr.sort currentBodyLevel) =>
            some (Expr.sort (Level.max domainLevel currentBodyLevel))
        | some (Expr.bvar _) => none
        | some (Expr.const _) => none
        | some (Expr.pi _ _) => none
        | some (Expr.lam _ _) => none
        | some (Expr.app _ _) => none
        | none => none
      let piDomainCase : Option Expr -> Option Expr
        | some (Expr.sort currentDomainLevel) =>
            piBodyCase currentDomainLevel
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
      let piDomainCaseEquality :
          Eq
            (Expr.inferCore?
              environment
              context
              (Expr.pi domainExpr bodyExpr))
            (piDomainCase
              (Expr.inferCore? environment context domainExpr)) :=
        Eq.refl
          (Expr.inferCore?
            environment
            context
            (Expr.pi domainExpr bodyExpr))
      let failFromDomainCase
          {domainResult : Option Expr}
          (domainInference :
            Eq
              (Expr.inferCore? environment context domainExpr)
              domainResult)
          (domainCaseFailed : Eq (piDomainCase domainResult) none) :
          HasType
            environment
            context
            (Expr.pi domainExpr bodyExpr)
            inferredTypeExpr :=
        inferCore_none_absurd
          (Eq.trans
            piDomainCaseEquality
            (Eq.trans
              (congrArg piDomainCase domainInference)
              domainCaseFailed))
          inferenceSucceeded
      match domainInference :
          Expr.inferCore? environment context domainExpr with
      | some (Expr.sort domainLevel) =>
          let domainHasSort :
              HasType environment context domainExpr (Expr.sort domainLevel) :=
            inferCore_sound
              (environment := environment)
              (context := context)
              domainExpr
              domainInference
          let bodyCaseEquality :
              Eq
                (piDomainCase (some (Expr.sort domainLevel)))
                (piBodyCase domainLevel
                  (Expr.inferCore?
                    environment
                    (Context.extend context domainExpr)
                    bodyExpr)) :=
            Eq.refl
              (piBodyCase domainLevel
                (Expr.inferCore?
                  environment
                  (Context.extend context domainExpr)
                  bodyExpr))
          let failFromBodyCase
              {bodyResult : Option Expr}
              (bodyInference :
                Eq
                  (Expr.inferCore?
                    environment
                    (Context.extend context domainExpr)
                    bodyExpr)
                  bodyResult)
              (bodyCaseFailed :
                Eq (piBodyCase domainLevel bodyResult) none) :
              HasType
                environment
                context
                (Expr.pi domainExpr bodyExpr)
                inferredTypeExpr :=
            inferCore_none_absurd
              (Eq.trans
                piDomainCaseEquality
                (Eq.trans
                  (congrArg piDomainCase domainInference)
                  (Eq.trans
                    bodyCaseEquality
                    (Eq.trans
                      (congrArg (piBodyCase domainLevel) bodyInference)
                      bodyCaseFailed))))
              inferenceSucceeded
          match bodyInference :
              Expr.inferCore?
                environment
                (Context.extend context domainExpr)
                bodyExpr with
          | some (Expr.sort bodyLevel) =>
              let bodyHasSort :
                  HasType
                    environment
                    (Context.extend context domainExpr)
                    bodyExpr
                    (Expr.sort bodyLevel) :=
                inferCore_sound
                  (environment := environment)
                  (context := Context.extend context domainExpr)
                  bodyExpr
                  bodyInference
              inferCore_pi_from_branch_sound
                domainInference
                bodyInference
                domainHasSort
                bodyHasSort
                inferenceSucceeded
          | some (Expr.bvar _) =>
              failFromBodyCase bodyInference (Eq.refl none)
          | some (Expr.const _) =>
              failFromBodyCase bodyInference (Eq.refl none)
          | some (Expr.pi _ _) =>
              failFromBodyCase bodyInference (Eq.refl none)
          | some (Expr.lam _ _) =>
              failFromBodyCase bodyInference (Eq.refl none)
          | some (Expr.app _ _) =>
              failFromBodyCase bodyInference (Eq.refl none)
          | none =>
              failFromBodyCase bodyInference (Eq.refl none)
      | some (Expr.bvar _) =>
          failFromDomainCase domainInference (Eq.refl none)
      | some (Expr.const _) =>
          failFromDomainCase domainInference (Eq.refl none)
      | some (Expr.pi _ _) =>
          failFromDomainCase domainInference (Eq.refl none)
      | some (Expr.lam _ _) =>
          failFromDomainCase domainInference (Eq.refl none)
      | some (Expr.app _ _) =>
          failFromDomainCase domainInference (Eq.refl none)
      | none =>
          failFromDomainCase domainInference (Eq.refl none)
  | Expr.lam domainExpr bodyExpr, inferredTypeExpr, inferenceSucceeded =>
      let lamBodyCase : Option Expr -> Option Expr
        | some currentBodyTypeExpr =>
            some (Expr.pi domainExpr currentBodyTypeExpr)
        | none => none
      let lamDomainCase : Option Expr -> Option Expr
        | some (Expr.sort _) =>
            lamBodyCase
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
      let lamDomainCaseEquality :
          Eq
            (Expr.inferCore?
              environment
              context
              (Expr.lam domainExpr bodyExpr))
            (lamDomainCase
              (Expr.inferCore? environment context domainExpr)) :=
        Eq.refl
          (Expr.inferCore?
            environment
            context
            (Expr.lam domainExpr bodyExpr))
      let failFromDomainCase
          {domainResult : Option Expr}
          (domainInference :
            Eq
              (Expr.inferCore? environment context domainExpr)
              domainResult)
          (domainCaseFailed : Eq (lamDomainCase domainResult) none) :
          HasType
            environment
            context
            (Expr.lam domainExpr bodyExpr)
            inferredTypeExpr :=
        inferCore_none_absurd
          (Eq.trans
            lamDomainCaseEquality
            (Eq.trans
              (congrArg lamDomainCase domainInference)
              domainCaseFailed))
          inferenceSucceeded
      match domainInference :
          Expr.inferCore? environment context domainExpr with
      | some (Expr.sort domainLevel) =>
          let domainHasSort :
              HasType environment context domainExpr (Expr.sort domainLevel) :=
            inferCore_sound
              (environment := environment)
              (context := context)
              domainExpr
              domainInference
          let bodyCaseEquality :
              Eq
                (lamDomainCase (some (Expr.sort domainLevel)))
                (lamBodyCase
                  (Expr.inferCore?
                    environment
                    (Context.extend context domainExpr)
                    bodyExpr)) :=
            Eq.refl
              (lamBodyCase
                (Expr.inferCore?
                  environment
                  (Context.extend context domainExpr)
                  bodyExpr))
          let failFromBodyCase
              {bodyResult : Option Expr}
              (bodyInference :
                Eq
                  (Expr.inferCore?
                    environment
                    (Context.extend context domainExpr)
                    bodyExpr)
                  bodyResult)
              (bodyCaseFailed : Eq (lamBodyCase bodyResult) none) :
              HasType
                environment
                context
                (Expr.lam domainExpr bodyExpr)
                inferredTypeExpr :=
            inferCore_none_absurd
              (Eq.trans
                lamDomainCaseEquality
                (Eq.trans
                  (congrArg lamDomainCase domainInference)
                  (Eq.trans
                    bodyCaseEquality
                    (Eq.trans
                      (congrArg lamBodyCase bodyInference)
                      bodyCaseFailed))))
              inferenceSucceeded
          match bodyInference :
              Expr.inferCore?
                environment
                (Context.extend context domainExpr)
                bodyExpr with
          | some bodyTypeExpr =>
              let bodyHasType :
                  HasType
                    environment
                    (Context.extend context domainExpr)
                    bodyExpr
                    bodyTypeExpr :=
                inferCore_sound
                  (environment := environment)
                  (context := Context.extend context domainExpr)
                  bodyExpr
                  bodyInference
              inferCore_lam_from_branch_sound
                domainInference
                bodyInference
                domainHasSort
                bodyHasType
                inferenceSucceeded
          | none =>
              failFromBodyCase bodyInference (Eq.refl none)
      | some (Expr.bvar _) =>
          failFromDomainCase domainInference (Eq.refl none)
      | some (Expr.const _) =>
          failFromDomainCase domainInference (Eq.refl none)
      | some (Expr.pi _ _) =>
          failFromDomainCase domainInference (Eq.refl none)
      | some (Expr.lam _ _) =>
          failFromDomainCase domainInference (Eq.refl none)
      | some (Expr.app _ _) =>
          failFromDomainCase domainInference (Eq.refl none)
      | none =>
          failFromDomainCase domainInference (Eq.refl none)
  | Expr.app functionExpr argumentExpr, inferredTypeExpr, inferenceSucceeded =>
      let appCheckCase (bodyTypeExpr : Expr) : Bool -> Option Expr
        | true => some (Expr.subst0 argumentExpr bodyTypeExpr)
        | false => none
      let appArgumentCase
          (domainExpr bodyTypeExpr : Expr) :
          Option Expr -> Option Expr
        | some argumentTypeExpr =>
            appCheckCase bodyTypeExpr
              (Expr.isDefEq environment argumentTypeExpr domainExpr)
        | none => none
      let appFunctionCase : Option Expr -> Option Expr
        | some (Expr.pi domainExpr bodyTypeExpr) =>
            appArgumentCase domainExpr bodyTypeExpr
              (Expr.inferCore? environment context argumentExpr)
        | some (Expr.bvar _) => none
        | some (Expr.sort _) => none
        | some (Expr.const _) => none
        | some (Expr.lam _ _) => none
        | some (Expr.app _ _) => none
        | none => none
      let appFunctionCaseEquality :
          Eq
            (Expr.inferCore?
              environment
              context
              (Expr.app functionExpr argumentExpr))
            (appFunctionCase
              (Expr.inferCore? environment context functionExpr)) :=
        Eq.refl
          (Expr.inferCore?
            environment
            context
            (Expr.app functionExpr argumentExpr))
      let failFromFunctionCase
          {functionResult : Option Expr}
          (functionInference :
            Eq
              (Expr.inferCore? environment context functionExpr)
              functionResult)
          (functionCaseFailed :
            Eq (appFunctionCase functionResult) none) :
          HasType
            environment
            context
            (Expr.app functionExpr argumentExpr)
            inferredTypeExpr :=
        inferCore_none_absurd
          (Eq.trans
            appFunctionCaseEquality
            (Eq.trans
              (congrArg appFunctionCase functionInference)
              functionCaseFailed))
          inferenceSucceeded
      match functionInference :
          Expr.inferCore? environment context functionExpr with
      | some (Expr.pi domainExpr bodyTypeExpr) =>
          let functionHasPi :
              HasType
                environment
                context
                functionExpr
                (Expr.pi domainExpr bodyTypeExpr) :=
            inferCore_sound
              (environment := environment)
              (context := context)
              functionExpr
              functionInference
          let argumentCaseEquality :
              Eq
                (appFunctionCase (some (Expr.pi domainExpr bodyTypeExpr)))
                (appArgumentCase domainExpr bodyTypeExpr
                  (Expr.inferCore? environment context argumentExpr)) :=
            Eq.refl
              (appArgumentCase domainExpr bodyTypeExpr
                (Expr.inferCore? environment context argumentExpr))
          let failFromArgumentCase
              {argumentResult : Option Expr}
              (argumentInference :
                Eq
                  (Expr.inferCore? environment context argumentExpr)
                  argumentResult)
              (argumentCaseFailed :
                Eq (appArgumentCase domainExpr bodyTypeExpr argumentResult)
                  none) :
              HasType
                environment
                context
                (Expr.app functionExpr argumentExpr)
                inferredTypeExpr :=
            inferCore_none_absurd
              (Eq.trans
                appFunctionCaseEquality
                (Eq.trans
                  (congrArg appFunctionCase functionInference)
                  (Eq.trans
                    argumentCaseEquality
                    (Eq.trans
                      (congrArg
                        (appArgumentCase domainExpr bodyTypeExpr)
                        argumentInference)
                      argumentCaseFailed))))
              inferenceSucceeded
          match argumentInference :
              Expr.inferCore? environment context argumentExpr with
          | some argumentTypeExpr =>
              let argumentHasInferredType :
                  HasType
                    environment
                    context
                    argumentExpr
                    argumentTypeExpr :=
                inferCore_sound
                  (environment := environment)
                  (context := context)
                  argumentExpr
                  argumentInference
              let checkCaseEquality :
                  Eq
                    (appArgumentCase
                      domainExpr
                      bodyTypeExpr
                      (some argumentTypeExpr))
                    (appCheckCase
                      bodyTypeExpr
                      (Expr.isDefEq environment argumentTypeExpr domainExpr)) :=
                Eq.refl
                  (appCheckCase
                    bodyTypeExpr
                    (Expr.isDefEq environment argumentTypeExpr domainExpr))
              let failFromCheckCase
                  {checkResult : Bool}
                  (argumentTypeCheck :
                    Eq
                      (Expr.isDefEq environment argumentTypeExpr domainExpr)
                      checkResult)
                  (checkCaseFailed :
                    Eq
                      (appCheckCase bodyTypeExpr checkResult)
                      none) :
                  HasType
                    environment
                    context
                    (Expr.app functionExpr argumentExpr)
                    inferredTypeExpr :=
                inferCore_none_absurd
                  (Eq.trans
                    appFunctionCaseEquality
                    (Eq.trans
                      (congrArg appFunctionCase functionInference)
                      (Eq.trans
                        argumentCaseEquality
                        (Eq.trans
                          (congrArg
                            (appArgumentCase domainExpr bodyTypeExpr)
                            argumentInference)
                          (Eq.trans
                            checkCaseEquality
                            (Eq.trans
                              (congrArg
                                (appCheckCase bodyTypeExpr)
                                argumentTypeCheck)
                              checkCaseFailed))))))
                  inferenceSucceeded
              match argumentTypeCheck :
                  Expr.isDefEq environment argumentTypeExpr domainExpr with
              | true =>
                  inferCore_app_from_branch_sound
                    functionInference
                    argumentInference
                    argumentTypeCheck
                    functionHasPi
                    argumentHasInferredType
                    inferenceSucceeded
              | false =>
                  failFromCheckCase argumentTypeCheck (Eq.refl none)
          | none =>
              failFromArgumentCase argumentInference (Eq.refl none)
      | some (Expr.bvar _) =>
          failFromFunctionCase functionInference (Eq.refl none)
      | some (Expr.sort _) =>
          failFromFunctionCase functionInference (Eq.refl none)
      | some (Expr.const _) =>
          failFromFunctionCase functionInference (Eq.refl none)
      | some (Expr.lam _ _) =>
          failFromFunctionCase functionInference (Eq.refl none)
      | some (Expr.app _ _) =>
          failFromFunctionCase functionInference (Eq.refl none)
      | none =>
          failFromFunctionCase functionInference (Eq.refl none)


end Expr

end LeanFX2.FX1
