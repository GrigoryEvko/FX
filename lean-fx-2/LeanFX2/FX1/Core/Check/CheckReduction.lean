prelude
import LeanFX2.FX1.Core.Check.CheckLookup

/-! # LeanFX2.FX1.Core.Check.CheckReduction

FX1 checker-level weak-head normalization and weak-head definitional
equality, with proof-carrying and runtime-facing variants plus soundness.

## Root status

Root-FX1 checker reduction slice. -/

namespace LeanFX2.FX1

namespace Expr

/-- A successful executable head reduction paired with its `EnvStep`
certificate. -/
structure HeadStepResult
    (environment : Environment) (sourceExpr : Expr) : Type where
  targetExpr : Expr
  reductionStep : EnvStep environment sourceExpr targetExpr

/-- Executable weak-head step search with proof payload.

This reduces transparent constants, beta-redexes, and the function position of
applications.  It deliberately does not reduce lambda bodies, Pi bodies, or
application arguments; those belong to stronger conversion routines. -/
def headStepResult? (environment : Environment) :
    (sourceExpr : Expr) -> Option (HeadStepResult environment sourceExpr)
  | Expr.const constName =>
      match Environment.findTransparentDefinitionResult? environment constName with
      | some lookupResult =>
          some {
            targetExpr := lookupResult.valueExpr
            reductionStep :=
              EnvStep.delta lookupResult.transparentDefinition
          }
      | none => none
  | Expr.app (Expr.lam domainExpr bodyExpr) argumentExpr =>
      some {
        targetExpr := Expr.subst0 argumentExpr bodyExpr
        reductionStep := EnvStep.beta domainExpr bodyExpr argumentExpr
      }
  | Expr.app sourceFunction argumentExpr =>
      match Expr.headStepResult? environment sourceFunction with
      | some functionStep =>
          some {
            targetExpr := Expr.app functionStep.targetExpr argumentExpr
            reductionStep := EnvStep.appFunction functionStep.reductionStep
          }
      | none => none
  | Expr.bvar _ => none
  | Expr.sort _ => none
  | Expr.pi _ _ => none
  | Expr.lam _ _ => none

/-- Project a proof-carrying head-step result to the executable target. -/
def headStepFromResult?
    {environment : Environment} {sourceExpr : Expr} :
    Option (HeadStepResult environment sourceExpr) -> Option Expr
  | some stepResult => some stepResult.targetExpr
  | none => none

/-- Runtime-facing executable head-step search. -/
def headStep? (environment : Environment) (sourceExpr : Expr) : Option Expr :=
  Expr.headStepFromResult?
    (Expr.headStepResult? environment sourceExpr)

/-- Soundness of executable head-step search. -/
def headStep?_sound
    {environment : Environment}
    {sourceExpr targetExpr : Expr}
    (headStepSucceeded :
      Eq (Expr.headStep? environment sourceExpr) (some targetExpr)) :
    EnvStep environment sourceExpr targetExpr :=
  match h : Expr.headStepResult? environment sourceExpr with
  | some stepResult =>
      let projectedEquality :
          Eq (some stepResult.targetExpr) (some targetExpr) :=
        Eq.trans
          (Eq.symm
            (congrArg
              (Expr.headStepFromResult?
                (environment := environment)
                (sourceExpr := sourceExpr))
              h))
          headStepSucceeded
      let targetEquality :=
        CheckOption.some_injective projectedEquality
      match targetEquality with
      | Eq.refl _ => stepResult.reductionStep
  | none =>
      let noneEqualsSome :
          Eq (none : Option Expr) (some targetExpr) :=
        Eq.trans
          (Eq.symm
            (congrArg
              (Expr.headStepFromResult?
                (environment := environment)
                (sourceExpr := sourceExpr))
              h))
          headStepSucceeded
      nomatch noneEqualsSome

/-- A fuel-bounded WHNF result paired with the reduction sequence from the
source expression to that result. -/
structure WhnfResult
    (environment : Environment) (sourceExpr : Expr) : Type where
  targetExpr : Expr
  reductions : EnvStepStar environment sourceExpr targetExpr

/-- Fuel-bounded weak-head normalization with its proof payload.

Fuel exhaustion is conservative: it returns the current expression with a
reflexive proof.  Callers that need more unfolding can provide more fuel; the
soundness theorem below holds for every budget. -/
def whnfResultWithFuel (environment : Environment) :
    Nat -> (sourceExpr : Expr) -> WhnfResult environment sourceExpr
  | Nat.zero, sourceExpr => {
      targetExpr := sourceExpr
      reductions := EnvStepStar.refl sourceExpr
    }
  | Nat.succ remainingFuel, sourceExpr =>
      match Expr.headStepResult? environment sourceExpr with
      | some headStepResult =>
          let tailResult :=
            Expr.whnfResultWithFuel
              environment
              remainingFuel
              headStepResult.targetExpr
          {
            targetExpr := tailResult.targetExpr
            reductions :=
              EnvStepStar.step
                headStepResult.reductionStep
                tailResult.reductions
          }
      | none => {
          targetExpr := sourceExpr
          reductions := EnvStepStar.refl sourceExpr
        }

/-- Project a proof-carrying WHNF result to the executable expression. -/
def whnfFromResult
    {environment : Environment} {sourceExpr : Expr} :
    WhnfResult environment sourceExpr -> Expr
  | whnfResult => whnfResult.targetExpr

/-- Runtime-facing fuel-bounded weak-head normalizer. -/
def whnfWithFuel
    (environment : Environment) (fuel : Nat) (sourceExpr : Expr) : Expr :=
  Expr.whnfFromResult
    (Expr.whnfResultWithFuel environment fuel sourceExpr)

/-- FX1-local default fuel for weak-head normalization.

The counter follows only the application spine because WHNF only reduces the
head.  It avoids `Nat.add`, keeping the default executable path free of host
extern arithmetic. -/
def weakHeadFuel : Expr -> Nat
  | Expr.app functionExpr _ => Nat.succ (Expr.weakHeadFuel functionExpr)
  | Expr.bvar _ => Nat.succ Nat.zero
  | Expr.sort _ => Nat.succ Nat.zero
  | Expr.const _ => Nat.succ Nat.zero
  | Expr.pi _ _ => Nat.succ Nat.zero
  | Expr.lam _ _ => Nat.succ Nat.zero

/-- Default weak-head normalizer budgeted by the source application spine.

This is intentionally bounded and extern-clean.  `whnfWithFuel` remains the
explicit API when callers need a larger unfolding budget, for example across a
long transparent-definition chain. -/
def whnf (environment : Environment) (sourceExpr : Expr) : Expr :=
  Expr.whnfWithFuel environment (Expr.weakHeadFuel sourceExpr) sourceExpr

/-- Soundness of fuel-bounded weak-head normalization. -/
theorem whnfWithFuel_sound
    (environment : Environment) (fuel : Nat) (sourceExpr : Expr) :
    EnvStepStar
      environment
      sourceExpr
      (Expr.whnfWithFuel environment fuel sourceExpr) :=
  (Expr.whnfResultWithFuel environment fuel sourceExpr).reductions

/-- Soundness of the default weak-head normalizer. -/
theorem whnf_sound
    (environment : Environment) (sourceExpr : Expr) :
    EnvStepStar
      environment
      sourceExpr
      (Expr.whnf environment sourceExpr) :=
  Expr.whnfWithFuel_sound
    environment
    (Expr.weakHeadFuel sourceExpr)
    sourceExpr

/-- A definitional equality witness produced by reducing both sides to a common
weak-head expression. -/
structure DefEqResult
    (environment : Environment) (leftExpr rightExpr : Expr) : Type where
  commonExpr : Expr
  leftReductions : EnvStepStar environment leftExpr commonExpr
  rightReductions : EnvStepStar environment rightExpr commonExpr

namespace DefEqResult

/-- Forget the executable payload wrapper into the typing-side common-reduct
definitional equality relation. -/
def toDefEq
    {environment : Environment}
    {leftExpr rightExpr : Expr}
    (result : DefEqResult environment leftExpr rightExpr) :
    DefEq environment leftExpr rightExpr :=
  DefEq.common
    result.commonExpr
    result.leftReductions
    result.rightReductions

end DefEqResult

/-- Extern-clean addition for fuel budgets.

This deliberately avoids host `Nat.add`, which the strict executable audit
flags as an extern dependency. -/
def weakHeadFuelAdd : Nat -> Nat -> Nat
  | Nat.zero, rightFuel => rightFuel
  | Nat.succ leftFuel, rightFuel =>
      Nat.succ (Expr.weakHeadFuelAdd leftFuel rightFuel)

/-- Default fuel for binary weak-head definitional equality. -/
def defEqFuel (leftExpr rightExpr : Expr) : Nat :=
  Expr.weakHeadFuelAdd
    (Expr.weakHeadFuel leftExpr)
    (Expr.weakHeadFuel rightExpr)

/-- Fuel-bounded WHNF-based definitional equality with proof payload.

The executable comparison is structural equality on the two weak-head forms;
the result stores the reduction sequences that justify the common reduct. -/
def defEqResultWithFuel?
    (environment : Environment) (fuel : Nat)
    (leftExpr rightExpr : Expr) :
    Option (DefEqResult environment leftExpr rightExpr) :=
  let leftResult :=
    Expr.whnfResultWithFuel environment fuel leftExpr
  let rightResult :=
    Expr.whnfResultWithFuel environment fuel rightExpr
  match equalityIsTrue :
      Expr.checkerBeq leftResult.targetExpr rightResult.targetExpr with
  | true =>
      let targetEquality :
          Eq leftResult.targetExpr rightResult.targetExpr :=
        Expr.checkerBeq_sound
          leftResult.targetExpr
          rightResult.targetExpr
          equalityIsTrue
      let rewrittenRightReductions :
          EnvStepStar environment rightExpr leftResult.targetExpr :=
        Eq.ndrec
          (motive := fun currentTargetExpr =>
            EnvStepStar environment rightExpr currentTargetExpr)
          rightResult.reductions
          (Eq.symm targetEquality)
      some {
        commonExpr := leftResult.targetExpr
        leftReductions := leftResult.reductions
        rightReductions := rewrittenRightReductions
      }
  | false => none

/-- Runtime-facing fuel-bounded weak-head definitional equality. -/
def isDefEqWithFuel
    (environment : Environment) (fuel : Nat)
    (leftExpr rightExpr : Expr) : Bool :=
  Expr.checkerBeq
    (Expr.whnfWithFuel environment fuel leftExpr)
    (Expr.whnfWithFuel environment fuel rightExpr)

/-- Runtime-facing default weak-head definitional equality.

This is bounded by an FX1-local fuel calculation.  It is intentionally a
conservative decision procedure; callers that need more unfolding should use
`isDefEqWithFuel`. -/
def isDefEq
    (environment : Environment) (leftExpr rightExpr : Expr) : Bool :=
  Expr.isDefEqWithFuel
    environment
    (Expr.defEqFuel leftExpr rightExpr)
    leftExpr
    rightExpr

/-- Soundness of fuel-bounded weak-head definitional equality. -/
def isDefEqWithFuel_sound
    {environment : Environment}
    {fuel : Nat}
    {leftExpr rightExpr : Expr}
    (defEqSucceeded :
      Eq
        (Expr.isDefEqWithFuel environment fuel leftExpr rightExpr)
        true) :
    DefEqResult environment leftExpr rightExpr :=
  let leftResult :=
    Expr.whnfResultWithFuel environment fuel leftExpr
  let rightResult :=
    Expr.whnfResultWithFuel environment fuel rightExpr
  let targetEquality :
      Eq leftResult.targetExpr rightResult.targetExpr :=
    Expr.checkerBeq_sound
      leftResult.targetExpr
      rightResult.targetExpr
      defEqSucceeded
  let rewrittenRightReductions :
      EnvStepStar environment rightExpr leftResult.targetExpr :=
    Eq.ndrec
      (motive := fun currentTargetExpr =>
        EnvStepStar environment rightExpr currentTargetExpr)
      rightResult.reductions
      (Eq.symm targetEquality)
  {
    commonExpr := leftResult.targetExpr
    leftReductions := leftResult.reductions
    rightReductions := rewrittenRightReductions
  }

/-- Soundness of default weak-head definitional equality. -/
def isDefEq_sound
    {environment : Environment}
    {leftExpr rightExpr : Expr}
    (defEqSucceeded :
      Eq (Expr.isDefEq environment leftExpr rightExpr) true) :
    DefEqResult environment leftExpr rightExpr :=
  Expr.isDefEqWithFuel_sound
    (environment := environment)
    (fuel := Expr.defEqFuel leftExpr rightExpr)
    (leftExpr := leftExpr)
    (rightExpr := rightExpr)
    defEqSucceeded

/-- Fuel-bounded weak-head definitional equality is sound for typing
conversion. -/
def isDefEqWithFuel_sound_defEq
    {environment : Environment}
    {fuel : Nat}
    {leftExpr rightExpr : Expr}
    (defEqSucceeded :
      Eq
        (Expr.isDefEqWithFuel environment fuel leftExpr rightExpr)
        true) :
    DefEq environment leftExpr rightExpr :=
  Expr.DefEqResult.toDefEq
    (Expr.isDefEqWithFuel_sound defEqSucceeded)

/-- Default weak-head definitional equality is sound for typing conversion. -/
def isDefEq_sound_defEq
    {environment : Environment}
    {leftExpr rightExpr : Expr}
    (defEqSucceeded :
      Eq (Expr.isDefEq environment leftExpr rightExpr) true) :
    DefEq environment leftExpr rightExpr :=
  Expr.DefEqResult.toDefEq
    (Expr.isDefEq_sound defEqSucceeded)

end Expr

end LeanFX2.FX1
