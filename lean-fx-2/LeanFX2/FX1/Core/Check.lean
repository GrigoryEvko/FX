prelude
import LeanFX2.FX1.Core.HasType

/-! # FX1/Core/Check

Root status: Root-FX1 checker slice.

This module adds the first executable checker slice for the minimal FX1
lambda-Pi core.  It is intentionally incomplete:

* variables, sorts, Pi types, lambdas, and applications are checked;
* constants return `none` until executable environment lookup has a proved
  zero-axiom membership theorem;
* equality used by application checking is structural and FX1-native.

The incompleteness is deliberate.  The executable checker is sound for the
fragment it accepts.  Accepting fewer programs is the conservative direction;
accepting constants before executable environment lookup is proved would widen
the TCB.
-/

namespace LeanFX2.FX1

namespace CheckOption

/-- Constructor injectivity for `Option.some`, kept local to avoid depending
on a host library theorem in the FX1 checker story. -/
theorem some_injective {elementType : Type}
    {leftValue rightValue : elementType}
    (someValuesEqual : Eq (some leftValue) (some rightValue)) :
    Eq leftValue rightValue :=
  match someValuesEqual with
  | Eq.refl _ => Eq.refl leftValue

end CheckOption

namespace Level

/-- Checker equality for the FX1 root universe fragment.

Universe parameters are compared with FX1-native name equality, not host
`String` equality. -/
def checkerBeq : Level -> Level -> Bool
  | Level.zero, Level.zero => true
  | Level.zero, Level.succ _ => false
  | Level.zero, Level.max _ _ => false
  | Level.zero, Level.imax _ _ => false
  | Level.zero, Level.param _ => false
  | Level.succ _, Level.zero => false
  | Level.succ leftBaseLevel, Level.succ rightBaseLevel =>
      Level.checkerBeq leftBaseLevel rightBaseLevel
  | Level.succ _, Level.max _ _ => false
  | Level.succ _, Level.imax _ _ => false
  | Level.succ _, Level.param _ => false
  | Level.max _ _, Level.zero => false
  | Level.max _ _, Level.succ _ => false
  | Level.max leftLeftLevel leftRightLevel,
      Level.max rightLeftLevel rightRightLevel =>
      Bool.and
        (Level.checkerBeq leftLeftLevel rightLeftLevel)
        (Level.checkerBeq leftRightLevel rightRightLevel)
  | Level.max _ _, Level.imax _ _ => false
  | Level.max _ _, Level.param _ => false
  | Level.imax _ _, Level.zero => false
  | Level.imax _ _, Level.succ _ => false
  | Level.imax _ _, Level.max _ _ => false
  | Level.imax leftLeftLevel leftRightLevel,
      Level.imax rightLeftLevel rightRightLevel =>
      Bool.and
        (Level.checkerBeq leftLeftLevel rightLeftLevel)
        (Level.checkerBeq leftRightLevel rightRightLevel)
  | Level.imax _ _, Level.param _ => false
  | Level.param _, Level.zero => false
  | Level.param _, Level.succ _ => false
  | Level.param _, Level.max _ _ => false
  | Level.param _, Level.imax _ _ => false
  | Level.param leftName, Level.param rightName =>
      Name.beq leftName rightName

/-- Soundness of FX1 checker-level universe comparison. -/
theorem checkerBeq_sound
    : forall leftLevel rightLevel : Level,
      Eq (Level.checkerBeq leftLevel rightLevel) true ->
      Eq leftLevel rightLevel
  | Level.zero, Level.zero, _ => Eq.refl Level.zero
  | Level.zero, Level.succ _, equalityIsTrue => nomatch equalityIsTrue
  | Level.zero, Level.max _ _, equalityIsTrue => nomatch equalityIsTrue
  | Level.zero, Level.imax _ _, equalityIsTrue => nomatch equalityIsTrue
  | Level.zero, Level.param _, equalityIsTrue => nomatch equalityIsTrue
  | Level.succ _, Level.zero, equalityIsTrue => nomatch equalityIsTrue
  | Level.succ leftBaseLevel, Level.succ rightBaseLevel, equalityIsTrue =>
      congrArg Level.succ
        (checkerBeq_sound leftBaseLevel rightBaseLevel equalityIsTrue)
  | Level.succ _, Level.max _ _, equalityIsTrue => nomatch equalityIsTrue
  | Level.succ _, Level.imax _ _, equalityIsTrue => nomatch equalityIsTrue
  | Level.succ _, Level.param _, equalityIsTrue => nomatch equalityIsTrue
  | Level.max _ _, Level.zero, equalityIsTrue => nomatch equalityIsTrue
  | Level.max _ _, Level.succ _, equalityIsTrue => nomatch equalityIsTrue
  | Level.max leftLeftLevel leftRightLevel,
      Level.max rightLeftLevel rightRightLevel,
      equalityIsTrue =>
      let leftEquality :=
        checkerBeq_sound
          leftLeftLevel
          rightLeftLevel
          (Boolean.and_true_left equalityIsTrue)
      let rightEquality :=
        checkerBeq_sound
          leftRightLevel
          rightRightLevel
          (Boolean.and_true_right equalityIsTrue)
      Eq.trans
        (congrArg
          (fun rewrittenLeftLevel =>
            Level.max rewrittenLeftLevel leftRightLevel)
          leftEquality)
        (congrArg
          (fun rewrittenRightLevel =>
            Level.max rightLeftLevel rewrittenRightLevel)
          rightEquality)
  | Level.max _ _, Level.imax _ _, equalityIsTrue => nomatch equalityIsTrue
  | Level.max _ _, Level.param _, equalityIsTrue => nomatch equalityIsTrue
  | Level.imax _ _, Level.zero, equalityIsTrue => nomatch equalityIsTrue
  | Level.imax _ _, Level.succ _, equalityIsTrue => nomatch equalityIsTrue
  | Level.imax _ _, Level.max _ _, equalityIsTrue => nomatch equalityIsTrue
  | Level.imax leftLeftLevel leftRightLevel,
      Level.imax rightLeftLevel rightRightLevel,
      equalityIsTrue =>
      let leftEquality :=
        checkerBeq_sound
          leftLeftLevel
          rightLeftLevel
          (Boolean.and_true_left equalityIsTrue)
      let rightEquality :=
        checkerBeq_sound
          leftRightLevel
          rightRightLevel
          (Boolean.and_true_right equalityIsTrue)
      Eq.trans
        (congrArg
          (fun rewrittenLeftLevel =>
            Level.imax rewrittenLeftLevel leftRightLevel)
          leftEquality)
        (congrArg
          (fun rewrittenRightLevel =>
            Level.imax rightLeftLevel rewrittenRightLevel)
          rightEquality)
  | Level.imax _ _, Level.param _, equalityIsTrue => nomatch equalityIsTrue
  | Level.param _, Level.zero, equalityIsTrue => nomatch equalityIsTrue
  | Level.param _, Level.succ _, equalityIsTrue => nomatch equalityIsTrue
  | Level.param _, Level.max _ _, equalityIsTrue => nomatch equalityIsTrue
  | Level.param _, Level.imax _ _, equalityIsTrue => nomatch equalityIsTrue
  | Level.param leftName, Level.param rightName, equalityIsTrue =>
      congrArg Level.param
        (Name.beq_sound leftName rightName equalityIsTrue)

end Level

namespace Expr

/-- Checker equality for the initial FX1 expression fragment. -/
def checkerBeq : Expr -> Expr -> Bool
  | Expr.bvar leftIndex, Expr.bvar rightIndex =>
      NaturalNumber.beq leftIndex rightIndex
  | Expr.bvar _, Expr.sort _ => false
  | Expr.bvar _, Expr.const _ => false
  | Expr.bvar _, Expr.pi _ _ => false
  | Expr.bvar _, Expr.lam _ _ => false
  | Expr.bvar _, Expr.app _ _ => false
  | Expr.sort _, Expr.bvar _ => false
  | Expr.sort leftLevel, Expr.sort rightLevel =>
      Level.checkerBeq leftLevel rightLevel
  | Expr.sort _, Expr.const _ => false
  | Expr.sort _, Expr.pi _ _ => false
  | Expr.sort _, Expr.lam _ _ => false
  | Expr.sort _, Expr.app _ _ => false
  | Expr.const _, Expr.bvar _ => false
  | Expr.const _, Expr.sort _ => false
  | Expr.const leftName, Expr.const rightName =>
      Name.beq leftName rightName
  | Expr.const _, Expr.pi _ _ => false
  | Expr.const _, Expr.lam _ _ => false
  | Expr.const _, Expr.app _ _ => false
  | Expr.pi _ _, Expr.bvar _ => false
  | Expr.pi _ _, Expr.sort _ => false
  | Expr.pi _ _, Expr.const _ => false
  | Expr.pi leftDomain leftBody, Expr.pi rightDomain rightBody =>
      Bool.and
        (Expr.checkerBeq leftDomain rightDomain)
        (Expr.checkerBeq leftBody rightBody)
  | Expr.pi _ _, Expr.lam _ _ => false
  | Expr.pi _ _, Expr.app _ _ => false
  | Expr.lam _ _, Expr.bvar _ => false
  | Expr.lam _ _, Expr.sort _ => false
  | Expr.lam _ _, Expr.const _ => false
  | Expr.lam _ _, Expr.pi _ _ => false
  | Expr.lam leftDomain leftBody, Expr.lam rightDomain rightBody =>
      Bool.and
        (Expr.checkerBeq leftDomain rightDomain)
        (Expr.checkerBeq leftBody rightBody)
  | Expr.lam _ _, Expr.app _ _ => false
  | Expr.app _ _, Expr.bvar _ => false
  | Expr.app _ _, Expr.sort _ => false
  | Expr.app _ _, Expr.const _ => false
  | Expr.app _ _, Expr.pi _ _ => false
  | Expr.app _ _, Expr.lam _ _ => false
  | Expr.app leftFunction leftArgument,
      Expr.app rightFunction rightArgument =>
      Bool.and
        (Expr.checkerBeq leftFunction rightFunction)
        (Expr.checkerBeq leftArgument rightArgument)

/-- Soundness of checker-level expression comparison. -/
theorem checkerBeq_sound
    : forall leftExpr rightExpr : Expr,
      Eq (Expr.checkerBeq leftExpr rightExpr) true ->
      Eq leftExpr rightExpr
  | Expr.bvar leftIndex, Expr.bvar rightIndex, equalityIsTrue =>
      congrArg Expr.bvar
        (NaturalNumber.beq_sound leftIndex rightIndex equalityIsTrue)
  | Expr.bvar _, Expr.sort _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.bvar _, Expr.const _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.bvar _, Expr.pi _ _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.bvar _, Expr.lam _ _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.bvar _, Expr.app _ _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.sort _, Expr.bvar _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.sort leftLevel, Expr.sort rightLevel, equalityIsTrue =>
      congrArg Expr.sort
        (Level.checkerBeq_sound leftLevel rightLevel equalityIsTrue)
  | Expr.sort _, Expr.const _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.sort _, Expr.pi _ _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.sort _, Expr.lam _ _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.sort _, Expr.app _ _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.const _, Expr.bvar _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.const _, Expr.sort _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.const leftName, Expr.const rightName, equalityIsTrue =>
      congrArg Expr.const
        (Name.beq_sound leftName rightName equalityIsTrue)
  | Expr.const _, Expr.pi _ _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.const _, Expr.lam _ _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.const _, Expr.app _ _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.pi _ _, Expr.bvar _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.pi _ _, Expr.sort _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.pi _ _, Expr.const _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.pi leftDomain leftBody, Expr.pi rightDomain rightBody,
      equalityIsTrue =>
      Expr.pi_congr
        (checkerBeq_sound
          leftDomain
          rightDomain
          (Boolean.and_true_left equalityIsTrue))
        (checkerBeq_sound
          leftBody
          rightBody
          (Boolean.and_true_right equalityIsTrue))
  | Expr.pi _ _, Expr.lam _ _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.pi _ _, Expr.app _ _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.lam _ _, Expr.bvar _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.lam _ _, Expr.sort _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.lam _ _, Expr.const _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.lam _ _, Expr.pi _ _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.lam leftDomain leftBody, Expr.lam rightDomain rightBody,
      equalityIsTrue =>
      Expr.lam_congr
        (checkerBeq_sound
          leftDomain
          rightDomain
          (Boolean.and_true_left equalityIsTrue))
        (checkerBeq_sound
          leftBody
          rightBody
          (Boolean.and_true_right equalityIsTrue))
  | Expr.lam _ _, Expr.app _ _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.app _ _, Expr.bvar _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.app _ _, Expr.sort _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.app _ _, Expr.const _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.app _ _, Expr.pi _ _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.app _ _, Expr.lam _ _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.app leftFunction leftArgument,
      Expr.app rightFunction rightArgument,
      equalityIsTrue =>
      Expr.app_congr
        (checkerBeq_sound
          leftFunction
          rightFunction
          (Boolean.and_true_left equalityIsTrue))
        (checkerBeq_sound
          leftArgument
          rightArgument
          (Boolean.and_true_right equalityIsTrue))

end Expr

namespace Context

/-- A successful executable lookup paired with the relational lookup witness
it justifies. -/
structure LookupTypeResult (entries : List Expr) (index : Nat) : Type where
  typeExpr : Expr
  typeAtIndex : Context.HasTypeAt { entries := entries } index typeExpr

/-- Witness-producing lookup for the shifted de Bruijn context lookup used by
the checker. -/
def lookupTypeResultInEntries? :
    (entries : List Expr) -> (index : Nat) ->
      Option (LookupTypeResult entries index)
  | List.nil, _ => none
  | List.cons newestTypeExpr remainingEntries, Nat.zero =>
      some {
        typeExpr := Expr.weaken newestTypeExpr
        typeAtIndex :=
          Context.HasTypeAt.newest
            { entries := remainingEntries }
            newestTypeExpr
      }
  | List.cons newestTypeExpr remainingEntries, Nat.succ remainingIndex =>
      match lookupTypeResultInEntries? remainingEntries remainingIndex with
      | some olderLookup =>
          some {
            typeExpr := Expr.weaken olderLookup.typeExpr
            typeAtIndex :=
              Context.HasTypeAt.older
                newestTypeExpr
                olderLookup.typeAtIndex
          }
      | none => none

/-- Project a proof-carrying context lookup result to the executable type
payload. -/
def lookupTypeFromResult?
    {entries : List Expr} {index : Nat} :
    Option (LookupTypeResult entries index) -> Option Expr
  | some lookupResult => some lookupResult.typeExpr
  | none => none

/-- Lookup a de Bruijn index and return the binder type shifted into the
current context, matching `Context.HasTypeAt`. -/
def lookupTypeInEntries? : List Expr -> Nat -> Option Expr
  | entries, index =>
      Context.lookupTypeFromResult?
        (Context.lookupTypeResultInEntries? entries index)

/-- Context-level wrapper for `lookupTypeInEntries?`. -/
def lookupType? (context : Context) (index : Nat) : Option Expr :=
  Context.lookupTypeInEntries? context.entries index

/-- Context-level wrapper for witness-producing lookup. -/
def lookupTypeResult? (context : Context) (index : Nat) :
    Option (LookupTypeResult context.entries index) :=
  Context.lookupTypeResultInEntries? context.entries index

/-- Soundness of executable shifted de Bruijn lookup. -/
theorem lookupType_sound
    {context : Context}
    {index : Nat}
    {typeExpr : Expr}
    (lookupSucceeded :
      Eq (Context.lookupType? context index) (some typeExpr)) :
    Context.HasTypeAt context index typeExpr :=
  match h : Context.lookupTypeResult? context index with
  | some lookupResult =>
      let projectedEquality :
          Eq (some lookupResult.typeExpr) (some typeExpr) :=
        Eq.trans
          (Eq.symm
            (congrArg
              (Context.lookupTypeFromResult?
                (entries := context.entries)
                (index := index))
              h))
          lookupSucceeded
      let typeEquality :=
        CheckOption.some_injective projectedEquality
      match typeEquality with
      | Eq.refl _ => lookupResult.typeAtIndex
  | none =>
      let noneEqualsSome :
          Eq (none : Option Expr) (some typeExpr) :=
        Eq.trans
          (Eq.symm
            (congrArg
              (Context.lookupTypeFromResult?
                (entries := context.entries)
                (index := index))
              h))
          lookupSucceeded
      nomatch noneEqualsSome

end Context

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
      Expr.checkerBeq inferenceResult.typeExpr expectedTypeExpr
  | none => false

/-- Project a runtime-facing optional inferred type to the executable check
result against an expected type. -/
def checkBoolFromCoreType? (expectedTypeExpr : Expr) :
    Option Expr -> Bool
  | some inferredTypeExpr =>
      Expr.checkerBeq inferredTypeExpr expectedTypeExpr
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
  | Expr.const _ =>
      none
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
              match Expr.checkerBeq argumentTypeExpr domainExpr with
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

/-- Executable checking against an expected type without proof payloads. -/
def checkCore? (environment : Environment) (context : Context)
    (expression expectedTypeExpr : Expr) : Bool :=
  Expr.checkBoolFromCoreType?
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
      Eq (Expr.checkerBeq inferredTypeExpr expectedTypeExpr) true :=
    Eq.trans
      (Eq.symm
        (congrArg
          (Expr.checkBoolFromCoreType? expectedTypeExpr)
          inferenceSucceeded))
      checkingSucceeded
  let inferredTypeEquality :=
    Expr.checkerBeq_sound
      inferredTypeExpr
      expectedTypeExpr
      projectedEquality
  match inferredTypeEquality with
  | Eq.refl _ => inferredTypeDerivation

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
              (Expr.checkBoolFromCoreType? expectedTypeExpr)
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

/-- Proof-carrying inference for the initial no-constant checker fragment. -/
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
  | Expr.const _ => none
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
                      Expr.checkerBeq argumentResult.typeExpr domainExpr with
                  | true =>
                      let argumentTypeEquality :=
                        Expr.checkerBeq_sound
                          argumentResult.typeExpr
                          domainExpr
                          h
                      let argumentHasDomain :
                          HasType
                            environment
                            context
                            argumentExpr
                            domainExpr :=
                        match argumentTypeEquality with
                        | Eq.refl _ => argumentResult.typeDerivation
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

/-- Check an expression against an expected type using checker equality. -/
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
            (Expr.checkerBeq inferenceResult.typeExpr expectedTypeExpr)
            true :=
        Eq.trans
          (Eq.symm
            (congrArg
              (Expr.checkBoolFromResult? expectedTypeExpr)
              h))
          checkingSucceeded
      let inferredTypeEquality :=
        Expr.checkerBeq_sound
          inferenceResult.typeExpr
          expectedTypeExpr
          projectedEquality
      match inferredTypeEquality with
      | Eq.refl _ => inferenceResult.typeDerivation
  | none =>
      let falseEqualsTrue : Eq false true :=
        Eq.trans
          (Eq.symm
            (congrArg
              (Expr.checkBoolFromResult? expectedTypeExpr)
              h))
          checkingSucceeded
      nomatch falseEqualsTrue

end Expr

end LeanFX2.FX1
