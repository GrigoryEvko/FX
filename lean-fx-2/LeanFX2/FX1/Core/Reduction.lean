prelude
import LeanFX2.FX1.Core.Substitution

/-! # FX1/Core/Reduction

Root status: Root-FX1 metatheory scaffold.

One-step beta reduction and its reflexive-transitive closure for the minimal
FX1 lambda-Pi core.  Delta reduction is intentionally deferred until
environment well-formedness records transparent definitions with checked
types and values.
-/

namespace LeanFX2.FX1

/-- One-step reduction for minimal FX1 expressions. -/
inductive Step : Expr -> Expr -> Prop
  /-- Lambda application beta-reduces by substituting the argument into the
  lambda body. -/
  | beta
      (domainExpr bodyExpr argumentExpr : Expr) :
      Step
        (Expr.app (Expr.lam domainExpr bodyExpr) argumentExpr)
        (Expr.subst0 argumentExpr bodyExpr)
  /-- Reduce the domain of a Pi type. -/
  | piDomain
      {sourceDomain targetDomain bodyExpr : Expr}
      (domainStep : Step sourceDomain targetDomain) :
      Step
        (Expr.pi sourceDomain bodyExpr)
        (Expr.pi targetDomain bodyExpr)
  /-- Reduce the body of a Pi type. -/
  | piBody
      {domainExpr sourceBody targetBody : Expr}
      (bodyStep : Step sourceBody targetBody) :
      Step
        (Expr.pi domainExpr sourceBody)
        (Expr.pi domainExpr targetBody)
  /-- Reduce the domain annotation of a lambda. -/
  | lamDomain
      {sourceDomain targetDomain bodyExpr : Expr}
      (domainStep : Step sourceDomain targetDomain) :
      Step
        (Expr.lam sourceDomain bodyExpr)
        (Expr.lam targetDomain bodyExpr)
  /-- Reduce the body of a lambda. -/
  | lamBody
      {domainExpr sourceBody targetBody : Expr}
      (bodyStep : Step sourceBody targetBody) :
      Step
        (Expr.lam domainExpr sourceBody)
        (Expr.lam domainExpr targetBody)
  /-- Reduce the function position of an application. -/
  | appFunction
      {sourceFunction targetFunction argumentExpr : Expr}
      (functionStep : Step sourceFunction targetFunction) :
      Step
        (Expr.app sourceFunction argumentExpr)
        (Expr.app targetFunction argumentExpr)
  /-- Reduce the argument position of an application. -/
  | appArgument
      {functionExpr sourceArgument targetArgument : Expr}
      (argumentStep : Step sourceArgument targetArgument) :
      Step
        (Expr.app functionExpr sourceArgument)
        (Expr.app functionExpr targetArgument)

namespace Step

/-- Beta reduction on the newest variable returns the argument. -/
theorem beta_newest_bvar
    (domainExpr argumentExpr : Expr) :
    Step
      (Expr.app (Expr.lam domainExpr (Expr.bvar Nat.zero)) argumentExpr)
      argumentExpr :=
  Step.beta domainExpr (Expr.bvar Nat.zero) argumentExpr

/-- Beta reduction on an older variable drops the removed binder. -/
theorem beta_succ_bvar
    (domainExpr argumentExpr : Expr) (index : Nat) :
    Step
      (Expr.app
        (Expr.lam domainExpr (Expr.bvar (Nat.succ index)))
        argumentExpr)
      (Expr.bvar index) :=
  Step.beta domainExpr (Expr.bvar (Nat.succ index)) argumentExpr

end Step

/-- Reflexive-transitive closure of FX1 one-step reduction. -/
inductive StepStar : Expr -> Expr -> Prop
  /-- Zero reduction steps. -/
  | refl (expression : Expr) :
      StepStar expression expression
  /-- One step followed by zero or more steps. -/
  | step
      {sourceExpr middleExpr targetExpr : Expr}
      (firstStep : Step sourceExpr middleExpr)
      (remainingSteps : StepStar middleExpr targetExpr) :
      StepStar sourceExpr targetExpr

namespace StepStar

/-- A single one-step reduction embeds into the reflexive-transitive
closure. -/
theorem single
    {sourceExpr targetExpr : Expr}
    (singleStep : Step sourceExpr targetExpr) :
    StepStar sourceExpr targetExpr :=
  StepStar.step singleStep (StepStar.refl targetExpr)

/-- Transitivity of reflexive-transitive reduction. -/
theorem trans
    {firstExpr secondExpr thirdExpr : Expr}
    (leftSteps : StepStar firstExpr secondExpr)
    (rightSteps : StepStar secondExpr thirdExpr) :
    StepStar firstExpr thirdExpr :=
  match leftSteps with
  | StepStar.refl _ => rightSteps
  | StepStar.step firstStep remainingSteps =>
      StepStar.step firstStep (trans remainingSteps rightSteps)

end StepStar

end LeanFX2.FX1
