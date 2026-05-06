prelude
import LeanFX2.FX1.Core.Environment
import LeanFX2.FX1.Core.Substitution

/-! # FX1/Core/Reduction

Root status: Root-FX1 metatheory scaffold.

One-step beta reduction and its reflexive-transitive closure for the minimal
FX1 lambda-Pi core.  The historical `Step` relation remains environment-free;
`EnvStep` is the environment-indexed relation that adds transparent constant
unfolding without smuggling host maps into the trusted root.
-/

namespace LeanFX2.FX1

namespace Environment

/-- A transparent definition/proof available in an FX1 environment.

This is propositional, matching `Environment.HasDeclaration`: duplicate-name
rejection is handled by environment well-formedness, not by trusting host
lookup.  Under a well-formed environment the `older` arm cannot observe a
shadowing declaration with the same name, because extension requires name
freshness. -/
inductive TransparentDefinition : Environment -> Name -> Expr -> Expr -> Prop
  /-- The newest transparent definition can be unfolded. -/
  | newestDef
      (environment : Environment)
      (declName : Name)
      (typeExpr valueExpr : Expr) :
      TransparentDefinition
        (Environment.extend environment
          (Declaration.defDecl declName typeExpr valueExpr))
        declName
        typeExpr
        valueExpr
  /-- The newest checked theorem proof can be unfolded as a transparent proof
  term. -/
  | newestTheorem
      (environment : Environment)
      (declName : Name)
      (typeExpr proofExpr : Expr) :
      TransparentDefinition
        (Environment.extend environment
          (Declaration.theoremDecl declName typeExpr proofExpr))
        declName
        typeExpr
        proofExpr
  /-- Older transparent declarations remain available after extension. -/
  | older
      {environment : Environment}
      {declName : Name}
      {typeExpr valueExpr : Expr}
      (newDeclaration : Declaration)
      (olderDefinition :
        TransparentDefinition environment declName typeExpr valueExpr) :
      TransparentDefinition
        (Environment.extend environment newDeclaration)
        declName
        typeExpr
        valueExpr

namespace TransparentDefinition

/-- Environment weakening for transparent definitions. -/
theorem weaken
    {environment : Environment}
    {declName : Name}
    {typeExpr valueExpr : Expr}
    (newDeclaration : Declaration)
    (olderDefinition :
      TransparentDefinition environment declName typeExpr valueExpr) :
    TransparentDefinition
      (Environment.extend environment newDeclaration)
      declName
      typeExpr
      valueExpr :=
  TransparentDefinition.older newDeclaration olderDefinition

end TransparentDefinition

end Environment

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

/-- Environment-indexed one-step reduction for minimal FX1 expressions.

This extends the environment-free `Step` relation with a single delta rule for
transparent definitions/proofs while preserving the same beta and congruence
rules.  Keeping it separate avoids changing the established `Step` API until
the checker and preservation spine are ready to consume environment-indexed
conversion throughout. -/
inductive EnvStep (environment : Environment) : Expr -> Expr -> Prop
  /-- Lambda application beta-reduces by substituting the argument into the
  lambda body. -/
  | beta
      (domainExpr bodyExpr argumentExpr : Expr) :
      EnvStep
        environment
        (Expr.app (Expr.lam domainExpr bodyExpr) argumentExpr)
        (Expr.subst0 argumentExpr bodyExpr)
  /-- Transparent constants delta-reduce to their checked value/proof. -/
  | delta
      {declName : Name}
      {typeExpr valueExpr : Expr}
      (transparentDefinition :
        Environment.TransparentDefinition
          environment
          declName
          typeExpr
          valueExpr) :
      EnvStep environment (Expr.const declName) valueExpr
  /-- Reduce the domain of a Pi type. -/
  | piDomain
      {sourceDomain targetDomain bodyExpr : Expr}
      (domainStep : EnvStep environment sourceDomain targetDomain) :
      EnvStep
        environment
        (Expr.pi sourceDomain bodyExpr)
        (Expr.pi targetDomain bodyExpr)
  /-- Reduce the body of a Pi type. -/
  | piBody
      {domainExpr sourceBody targetBody : Expr}
      (bodyStep : EnvStep environment sourceBody targetBody) :
      EnvStep
        environment
        (Expr.pi domainExpr sourceBody)
        (Expr.pi domainExpr targetBody)
  /-- Reduce the domain annotation of a lambda. -/
  | lamDomain
      {sourceDomain targetDomain bodyExpr : Expr}
      (domainStep : EnvStep environment sourceDomain targetDomain) :
      EnvStep
        environment
        (Expr.lam sourceDomain bodyExpr)
        (Expr.lam targetDomain bodyExpr)
  /-- Reduce the body of a lambda. -/
  | lamBody
      {domainExpr sourceBody targetBody : Expr}
      (bodyStep : EnvStep environment sourceBody targetBody) :
      EnvStep
        environment
        (Expr.lam domainExpr sourceBody)
        (Expr.lam domainExpr targetBody)
  /-- Reduce the function position of an application. -/
  | appFunction
      {sourceFunction targetFunction argumentExpr : Expr}
      (functionStep : EnvStep environment sourceFunction targetFunction) :
      EnvStep
        environment
        (Expr.app sourceFunction argumentExpr)
        (Expr.app targetFunction argumentExpr)
  /-- Reduce the argument position of an application. -/
  | appArgument
      {functionExpr sourceArgument targetArgument : Expr}
      (argumentStep : EnvStep environment sourceArgument targetArgument) :
      EnvStep
        environment
        (Expr.app functionExpr sourceArgument)
        (Expr.app functionExpr targetArgument)

namespace EnvStep

/-- Every environment-free step embeds into the environment-indexed relation. -/
theorem fromStep
    (environment : Environment)
    {sourceExpr targetExpr : Expr}
    (singleStep : Step sourceExpr targetExpr) :
    EnvStep environment sourceExpr targetExpr :=
  match singleStep with
  | Step.beta domainExpr bodyExpr argumentExpr =>
      EnvStep.beta domainExpr bodyExpr argumentExpr
  | Step.piDomain domainStep =>
      EnvStep.piDomain (fromStep environment domainStep)
  | Step.piBody bodyStep =>
      EnvStep.piBody (fromStep environment bodyStep)
  | Step.lamDomain domainStep =>
      EnvStep.lamDomain (fromStep environment domainStep)
  | Step.lamBody bodyStep =>
      EnvStep.lamBody (fromStep environment bodyStep)
  | Step.appFunction functionStep =>
      EnvStep.appFunction (fromStep environment functionStep)
  | Step.appArgument argumentStep =>
      EnvStep.appArgument (fromStep environment argumentStep)

/-- Environment weakening for one-step environment-indexed reduction. -/
theorem weaken_environment
    {environment : Environment}
    {sourceExpr targetExpr : Expr}
    (newDeclaration : Declaration)
    (singleStep : EnvStep environment sourceExpr targetExpr) :
    EnvStep
      (Environment.extend environment newDeclaration)
      sourceExpr
      targetExpr :=
  match singleStep with
  | EnvStep.beta domainExpr bodyExpr argumentExpr =>
      EnvStep.beta domainExpr bodyExpr argumentExpr
  | EnvStep.delta transparentDefinition =>
      EnvStep.delta
        (Environment.TransparentDefinition.weaken
          newDeclaration
          transparentDefinition)
  | EnvStep.piDomain domainStep =>
      EnvStep.piDomain
        (weaken_environment newDeclaration domainStep)
  | EnvStep.piBody bodyStep =>
      EnvStep.piBody
        (weaken_environment newDeclaration bodyStep)
  | EnvStep.lamDomain domainStep =>
      EnvStep.lamDomain
        (weaken_environment newDeclaration domainStep)
  | EnvStep.lamBody bodyStep =>
      EnvStep.lamBody
        (weaken_environment newDeclaration bodyStep)
  | EnvStep.appFunction functionStep =>
      EnvStep.appFunction
        (weaken_environment newDeclaration functionStep)
  | EnvStep.appArgument argumentStep =>
      EnvStep.appArgument
        (weaken_environment newDeclaration argumentStep)

/-- The newest transparent definition delta-reduces to its value. -/
theorem deltaNewestDef
    (environment : Environment)
    (declName : Name)
    (typeExpr valueExpr : Expr) :
    EnvStep
      (Environment.extend environment
        (Declaration.defDecl declName typeExpr valueExpr))
      (Expr.const declName)
      valueExpr :=
  EnvStep.delta
    (Environment.TransparentDefinition.newestDef
      environment
      declName
      typeExpr
      valueExpr)

/-- The newest checked theorem delta-reduces to its proof term. -/
theorem deltaNewestTheorem
    (environment : Environment)
    (declName : Name)
    (typeExpr proofExpr : Expr) :
    EnvStep
      (Environment.extend environment
        (Declaration.theoremDecl declName typeExpr proofExpr))
      (Expr.const declName)
      proofExpr :=
  EnvStep.delta
    (Environment.TransparentDefinition.newestTheorem
      environment
      declName
      typeExpr
      proofExpr)

/-- Beta reduction on the newest variable returns the argument. -/
theorem betaNewestBvar
    (environment : Environment)
    (domainExpr argumentExpr : Expr) :
    EnvStep
      environment
      (Expr.app (Expr.lam domainExpr (Expr.bvar Nat.zero)) argumentExpr)
      argumentExpr :=
  EnvStep.beta domainExpr (Expr.bvar Nat.zero) argumentExpr

/-- Beta reduction on an older variable drops the removed binder. -/
theorem betaSuccBvar
    (environment : Environment)
    (domainExpr argumentExpr : Expr) (index : Nat) :
    EnvStep
      environment
      (Expr.app
        (Expr.lam domainExpr (Expr.bvar (Nat.succ index)))
        argumentExpr)
      (Expr.bvar index) :=
  EnvStep.beta domainExpr (Expr.bvar (Nat.succ index)) argumentExpr

end EnvStep

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

/-- Reflexive-transitive closure of environment-indexed FX1 one-step
reduction. -/
inductive EnvStepStar (environment : Environment) : Expr -> Expr -> Prop
  /-- Zero reduction steps. -/
  | refl (expression : Expr) :
      EnvStepStar environment expression expression
  /-- One environment-indexed step followed by zero or more steps. -/
  | step
      {sourceExpr middleExpr targetExpr : Expr}
      (firstStep : EnvStep environment sourceExpr middleExpr)
      (remainingSteps : EnvStepStar environment middleExpr targetExpr) :
      EnvStepStar environment sourceExpr targetExpr

namespace EnvStepStar

/-- A single environment-indexed one-step reduction embeds into the
reflexive-transitive closure. -/
theorem single
    {environment : Environment}
    {sourceExpr targetExpr : Expr}
    (singleStep : EnvStep environment sourceExpr targetExpr) :
    EnvStepStar environment sourceExpr targetExpr :=
  EnvStepStar.step singleStep (EnvStepStar.refl targetExpr)

/-- Transitivity of environment-indexed reflexive-transitive reduction. -/
theorem trans
    {environment : Environment}
    {firstExpr secondExpr thirdExpr : Expr}
    (leftSteps : EnvStepStar environment firstExpr secondExpr)
    (rightSteps : EnvStepStar environment secondExpr thirdExpr) :
    EnvStepStar environment firstExpr thirdExpr :=
  match leftSteps with
  | EnvStepStar.refl _ => rightSteps
  | EnvStepStar.step firstStep remainingSteps =>
      EnvStepStar.step firstStep (trans remainingSteps rightSteps)

/-- Environment weakening for environment-indexed multi-step reduction. -/
theorem weaken_environment
    {environment : Environment}
    {sourceExpr targetExpr : Expr}
    (newDeclaration : Declaration)
    (multiStep : EnvStepStar environment sourceExpr targetExpr) :
    EnvStepStar
      (Environment.extend environment newDeclaration)
      sourceExpr
      targetExpr :=
  match multiStep with
  | EnvStepStar.refl expression =>
      EnvStepStar.refl expression
  | EnvStepStar.step firstStep remainingSteps =>
      EnvStepStar.step
        (EnvStep.weaken_environment newDeclaration firstStep)
        (weaken_environment newDeclaration remainingSteps)

/-- Environment-free multi-step reduction embeds into the environment-indexed
multi-step relation. -/
theorem fromStepStar
    (environment : Environment)
    {sourceExpr targetExpr : Expr}
    (multiStep : StepStar sourceExpr targetExpr) :
    EnvStepStar environment sourceExpr targetExpr :=
  match multiStep with
  | StepStar.refl expression => EnvStepStar.refl expression
  | StepStar.step firstStep remainingSteps =>
      EnvStepStar.step
        (EnvStep.fromStep environment firstStep)
        (fromStepStar environment remainingSteps)

end EnvStepStar

/-- Definitional equality as a common environment-indexed reduct.

This is the typing-side relation consumed by conversion.  Executable checkers
can produce witnesses through `Expr.isDefEq*_sound`; the relation itself lives
in the reduction layer so `HasType` can depend on it without importing the
checker. -/
inductive DefEq
    (environment : Environment) : Expr -> Expr -> Prop
  /-- Two expressions are definitionally equal when they reduce to a shared
  environment-indexed reduct. -/
  | common
      {leftExpr rightExpr : Expr}
      (commonExpr : Expr)
      (leftReductions : EnvStepStar environment leftExpr commonExpr)
      (rightReductions : EnvStepStar environment rightExpr commonExpr) :
      DefEq environment leftExpr rightExpr

namespace DefEq

/-- Reflexivity of definitional equality. -/
theorem refl
    (environment : Environment) (expression : Expr) :
    DefEq environment expression expression :=
  DefEq.common
    expression
    (EnvStepStar.refl expression)
    (EnvStepStar.refl expression)

/-- Symmetry of common-reduct definitional equality. -/
theorem symm
    {environment : Environment}
    {leftExpr rightExpr : Expr}
    (defEqWitness : DefEq environment leftExpr rightExpr) :
    DefEq environment rightExpr leftExpr :=
  match defEqWitness with
  | DefEq.common commonExpr leftReductions rightReductions =>
      DefEq.common commonExpr rightReductions leftReductions

/-- Environment weakening for common-reduct definitional equality. -/
theorem weaken_environment
    {environment : Environment}
    {leftExpr rightExpr : Expr}
    (newDeclaration : Declaration)
    (defEqWitness : DefEq environment leftExpr rightExpr) :
    DefEq
      (Environment.extend environment newDeclaration)
      leftExpr
      rightExpr :=
  match defEqWitness with
  | DefEq.common commonExpr leftReductions rightReductions =>
      DefEq.common
        commonExpr
        (EnvStepStar.weaken_environment newDeclaration leftReductions)
        (EnvStepStar.weaken_environment newDeclaration rightReductions)

end DefEq

end LeanFX2.FX1
