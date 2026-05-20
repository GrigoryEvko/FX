import LeanFX2.Term.PartialStrengthen.Constructors.ModalInterval

/-! # Term/PartialStrengthen/Constructors/ApplicationAndBinders

Typed partial-strengthening producers for non-dependent application,
dependent application, lambda binders, path lambdas, and path application.
-/

namespace LeanFX2

namespace Term

/-- Success branch for non-dependent application strengthening.

This helper keeps the computational target term out of the `Option` and
equality-recursion dispatcher used by `partialStrengthenTypedApp`, giving
the soundness proof a stable term to target. -/
def partialStrengthenTypedAppOfSuccess {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {domainType codomainType : Ty level sourceScope}
    {targetDomainType targetCodomainType : Ty level targetScope}
    {functionRaw argumentRaw : RawTerm sourceScope}
    {targetFunctionRaw targetArgumentRaw : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {functionTerm :
      Term sourceCtx (Ty.arrow domainType codomainType) functionRaw}
    {argumentTerm : Term sourceCtx domainType argumentRaw}
    (targetFunctionTerm :
      Term targetCtx (Ty.arrow targetDomainType targetCodomainType)
        targetFunctionRaw)
    (targetArgumentTerm :
      Term targetCtx targetDomainType targetArgumentRaw)
    (_domainSuccess :
      domainType.partialStrengthen? strengthening.back =
        some targetDomainType)
    (codomainSuccess :
      codomainType.partialStrengthen? strengthening.back =
        some targetCodomainType)
    (functionRawStrengthens :
      functionRaw.partialStrengthen? strengthening.back =
        some targetFunctionRaw)
    (argumentRawStrengthens :
      argumentRaw.partialStrengthen? strengthening.back =
        some targetArgumentRaw)
    (functionRawRenames :
      functionRaw = targetFunctionRaw.rename strengthening.forward)
    (argumentRawRenames :
      argumentRaw = targetArgumentRaw.rename strengthening.forward) :
    StrengtheningResult strengthening
      (Term.app functionTerm argumentTerm) := {
  targetType := targetCodomainType
  targetRaw := RawTerm.app targetFunctionRaw targetArgumentRaw
  targetTerm := Term.app targetFunctionTerm targetArgumentTerm
  typeStrengthens := codomainSuccess
  rawStrengthens := by
    change
      Option.mapTwo
        (functionRaw.partialStrengthen? strengthening.back)
        (argumentRaw.partialStrengthen? strengthening.back)
        RawTerm.app =
        some (RawTerm.app targetFunctionRaw targetArgumentRaw)
    rw [functionRawStrengthens, argumentRawStrengthens]
    rfl
  typeRenames :=
    Ty.partialStrengthen?_imp_rename codomainType
      strengthening.forward strengthening.back
      strengthening.injectsBack targetCodomainType
      codomainSuccess
  rawRenames := by
    cases functionRawRenames
    cases argumentRawRenames
    rfl
}

/-- Non-dependent function application strengthens by strengthening the
function and argument, then decomposing the strengthened arrow type. -/
def partialStrengthenTypedApp {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {domainType codomainType : Ty level sourceScope}
    {targetDomainType targetCodomainType : Ty level targetScope}
    {functionRaw argumentRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {functionTerm :
      Term sourceCtx (Ty.arrow domainType codomainType) functionRaw}
    {argumentTerm : Term sourceCtx domainType argumentRaw}
    (domainSuccess :
      domainType.partialStrengthen? strengthening.back =
        some targetDomainType)
    (codomainSuccess :
      codomainType.partialStrengthen? strengthening.back =
        some targetCodomainType)
    (functionResult : StrengtheningResult strengthening functionTerm)
    (argumentResult : StrengtheningResult strengthening argumentTerm) :
    StrengtheningResult strengthening
      (Term.app functionTerm argumentTerm) := by
  cases functionResult with
  | mk targetFunctionType targetFunctionRaw targetFunctionTerm
      functionTypeStrengthens functionRawStrengthens functionTypeRenames
      functionRawRenames =>
      change
        Option.mapTwo
          (domainType.partialStrengthen? strengthening.back)
          (codomainType.partialStrengthen? strengthening.back)
          Ty.arrow = some targetFunctionType at functionTypeStrengthens
      rw [domainSuccess, codomainSuccess] at functionTypeStrengthens
      cases functionTypeStrengthens
      cases argumentResult with
      | mk targetArgumentType targetArgumentRaw targetArgumentTerm
          argumentTypeStrengthens argumentRawStrengthens
          argumentTypeRenames argumentRawRenames =>
          rw [domainSuccess] at argumentTypeStrengthens
          cases argumentTypeStrengthens
          exact partialStrengthenTypedAppOfSuccess
            targetFunctionTerm targetArgumentTerm domainSuccess
            codomainSuccess functionRawStrengthens
            argumentRawStrengthens functionRawRenames argumentRawRenames

/-- Success branch for dependent application strengthening.

The dependent result type is computed from explicit domain/codomain and
argument strengthening successes, avoiding a proof-dependent dispatcher in
the soundness layer. -/
def partialStrengthenTypedAppPiOfSuccess {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {domainType : Ty level sourceScope}
    {codomainType : Ty level (sourceScope + 1)}
    {targetDomainType : Ty level targetScope}
    {targetCodomainType : Ty level (targetScope + 1)}
    {functionRaw argumentRaw : RawTerm sourceScope}
    {targetFunctionRaw targetArgumentRaw : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {functionTerm :
      Term sourceCtx (Ty.piTy domainType codomainType) functionRaw}
    {argumentTerm : Term sourceCtx domainType argumentRaw}
    (targetFunctionTerm :
      Term targetCtx (Ty.piTy targetDomainType targetCodomainType)
        targetFunctionRaw)
    (targetArgumentTerm : Term targetCtx targetDomainType
      targetArgumentRaw)
    (domainSuccess :
      domainType.partialStrengthen? strengthening.back =
        some targetDomainType)
    (codomainSuccess :
      codomainType.partialStrengthen? strengthening.back.lift =
        some targetCodomainType)
    (functionRawStrengthens :
      functionRaw.partialStrengthen? strengthening.back =
        some targetFunctionRaw)
    (argumentRawStrengthens :
      argumentRaw.partialStrengthen? strengthening.back =
        some targetArgumentRaw)
    (functionRawRenames :
      functionRaw = targetFunctionRaw.rename strengthening.forward)
    (argumentRawRenames :
      argumentRaw = targetArgumentRaw.rename strengthening.forward) :
    StrengtheningResult strengthening
      (Term.appPi functionTerm argumentTerm) := by
  have resultTypeStrengthens :
      (codomainType.subst0 domainType argumentRaw).partialStrengthen?
        strengthening.back =
        some (targetCodomainType.subst0 targetDomainType
          targetArgumentRaw) :=
    Ty.partialStrengthen?_subst0_of_success codomainType
      targetCodomainType domainType targetDomainType argumentRaw
      targetArgumentRaw strengthening.forward strengthening.back
      strengthening.injectsBack strengthening.back_forward codomainSuccess
      domainSuccess argumentRawStrengthens
  exact {
    targetType := targetCodomainType.subst0 targetDomainType
      targetArgumentRaw
    targetRaw := RawTerm.app targetFunctionRaw targetArgumentRaw
    targetTerm := Term.appPi targetFunctionTerm targetArgumentTerm
    typeStrengthens := resultTypeStrengthens
    rawStrengthens := by
      change
        Option.mapTwo
          (functionRaw.partialStrengthen? strengthening.back)
          (argumentRaw.partialStrengthen? strengthening.back)
          RawTerm.app =
          some (RawTerm.app targetFunctionRaw targetArgumentRaw)
      rw [functionRawStrengthens, argumentRawStrengthens]
      rfl
    typeRenames :=
      Ty.partialStrengthen?_imp_rename
        (codomainType.subst0 domainType argumentRaw)
        strengthening.forward strengthening.back strengthening.injectsBack
        (targetCodomainType.subst0 targetDomainType targetArgumentRaw)
        resultTypeStrengthens
    rawRenames := by
      cases functionRawRenames
      cases argumentRawRenames
      rfl
  }

/-- Dependent function application strengthens by strengthening the
function, the argument, and the codomain under the lifted strengthening. -/
def partialStrengthenTypedAppPi {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {domainType : Ty level sourceScope}
    {codomainType : Ty level (sourceScope + 1)}
    {targetDomainType : Ty level targetScope}
    {targetCodomainType : Ty level (targetScope + 1)}
    {functionRaw argumentRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {functionTerm :
      Term sourceCtx (Ty.piTy domainType codomainType) functionRaw}
    {argumentTerm : Term sourceCtx domainType argumentRaw}
    (domainSuccess :
      domainType.partialStrengthen? strengthening.back =
        some targetDomainType)
    (codomainSuccess :
      codomainType.partialStrengthen? strengthening.back.lift =
        some targetCodomainType)
    (functionResult : StrengtheningResult strengthening functionTerm)
    (argumentResult : StrengtheningResult strengthening argumentTerm) :
    StrengtheningResult strengthening
      (Term.appPi functionTerm argumentTerm) := by
  cases functionResult with
  | mk targetFunctionType targetFunctionRaw targetFunctionTerm
      functionTypeStrengthens functionRawStrengthens functionTypeRenames
      functionRawRenames =>
      change
        Option.mapTwo
          (domainType.partialStrengthen? strengthening.back)
          (codomainType.partialStrengthen? strengthening.back.lift)
          Ty.piTy = some targetFunctionType at functionTypeStrengthens
      rw [domainSuccess, codomainSuccess] at functionTypeStrengthens
      cases functionTypeStrengthens
      cases argumentResult with
      | mk targetArgumentType targetArgumentRaw targetArgumentTerm
          argumentTypeStrengthens argumentRawStrengthens
          argumentTypeRenames argumentRawRenames =>
          rw [domainSuccess] at argumentTypeStrengthens
          cases argumentTypeStrengthens
          exact partialStrengthenTypedAppPiOfSuccess
            targetFunctionTerm targetArgumentTerm domainSuccess
            codomainSuccess functionRawStrengthens
            argumentRawStrengthens functionRawRenames argumentRawRenames

/-- Non-dependent lambda strengthens by strengthening its domain and
codomain types, then strengthening the body under the lifted context
strengthening. -/
def partialStrengthenTypedLam {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {domainType codomainType : Ty level sourceScope}
    {targetDomainType targetCodomainType : Ty level targetScope}
    {bodyRaw : RawTerm (sourceScope + 1)}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {body :
      Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw}
    (domainTypeStrengthens :
      domainType.partialStrengthen? strengthening.back =
        some targetDomainType)
    (codomainTypeStrengthens :
      codomainType.partialStrengthen? strengthening.back =
        some targetCodomainType)
    (bodyResult : StrengtheningResult
      (strengthening.lift domainType targetDomainType
        domainTypeStrengthens) body) :
    StrengtheningResult strengthening (Term.lam body) := by
  cases bodyResult with
  | mk targetBodyType targetBodyRaw targetBodyTerm bodyTypeStrengthens
      bodyRawStrengthens bodyTypeRenames bodyRawRenames =>
      have bodyTypeStrengthensAtLift :
          codomainType.weaken.partialStrengthen? strengthening.back.lift =
            some targetBodyType := by
        simpa only [ContextStrengthening.lift] using bodyTypeStrengthens
      have bodyRawStrengthensAtLift :
          bodyRaw.partialStrengthen? strengthening.back.lift =
            some targetBodyRaw := by
        simpa only [ContextStrengthening.lift] using bodyRawStrengthens
      have expectedBodyTypeStrengthens :
          codomainType.weaken.partialStrengthen? strengthening.back.lift =
            some targetCodomainType.weaken := by
        rw [Ty.partialStrengthen?_weaken_lift codomainType
          strengthening.back, codomainTypeStrengthens]
        rfl
      rw [expectedBodyTypeStrengthens] at bodyTypeStrengthensAtLift
      cases bodyTypeStrengthensAtLift
      exact {
        targetType := Ty.arrow targetDomainType targetCodomainType
        targetRaw := RawTerm.lam targetBodyRaw
        targetTerm := Term.lam targetBodyTerm
        typeStrengthens := by
          change
            Option.mapTwo
              (domainType.partialStrengthen? strengthening.back)
              (codomainType.partialStrengthen? strengthening.back)
              Ty.arrow =
              some (Ty.arrow targetDomainType targetCodomainType)
          rw [domainTypeStrengthens, codomainTypeStrengthens]
          rfl
        rawStrengthens := by
          change
            (match bodyRaw.partialStrengthen? strengthening.back.lift with
            | some strengthenedBody => some (RawTerm.lam strengthenedBody)
            | none => none) =
              some (RawTerm.lam targetBodyRaw)
          rw [bodyRawStrengthensAtLift]
        typeRenames :=
          Ty.partialStrengthen?_imp_rename
            (Ty.arrow domainType codomainType)
            strengthening.forward strengthening.back strengthening.injectsBack
            (Ty.arrow targetDomainType targetCodomainType)
            (by
              change
                Option.mapTwo
                  (domainType.partialStrengthen? strengthening.back)
                  (codomainType.partialStrengthen? strengthening.back)
                  Ty.arrow =
                  some (Ty.arrow targetDomainType targetCodomainType)
              rw [domainTypeStrengthens, codomainTypeStrengthens]
              rfl)
        rawRenames :=
          RawTerm.partialStrengthen?_imp_rename
            (RawTerm.lam bodyRaw) strengthening.forward strengthening.back
            strengthening.injectsBack (RawTerm.lam targetBodyRaw)
            (by
              change
                (match bodyRaw.partialStrengthen?
                    strengthening.back.lift with
                | some strengthenedBody => some (RawTerm.lam strengthenedBody)
                | none => none) =
                  some (RawTerm.lam targetBodyRaw)
              rw [bodyRawStrengthensAtLift])
      }

/-- Dependent lambda strengthens by strengthening its domain type and
body under the lifted context strengthening. -/
def partialStrengthenTypedLamPi {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {domainType : Ty level sourceScope}
    {codomainType : Ty level (sourceScope + 1)}
    {targetDomainType : Ty level targetScope}
    {bodyRaw : RawTerm (sourceScope + 1)}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {body : Term (sourceCtx.cons domainType) codomainType bodyRaw}
    (domainTypeStrengthens :
      domainType.partialStrengthen? strengthening.back =
        some targetDomainType)
    (bodyResult : StrengtheningResult
      (strengthening.lift domainType targetDomainType
        domainTypeStrengthens) body) :
    StrengtheningResult strengthening (Term.lamPi body) := by
  cases bodyResult with
  | mk targetCodomainType targetBodyRaw targetBodyTerm
      codomainTypeStrengthens bodyRawStrengthens codomainTypeRenames
      bodyRawRenames =>
      have codomainTypeStrengthensAtLift :
          codomainType.partialStrengthen? strengthening.back.lift =
            some targetCodomainType := by
        simpa only [ContextStrengthening.lift] using codomainTypeStrengthens
      have bodyRawStrengthensAtLift :
          bodyRaw.partialStrengthen? strengthening.back.lift =
            some targetBodyRaw := by
        simpa only [ContextStrengthening.lift] using bodyRawStrengthens
      exact {
        targetType := Ty.piTy targetDomainType targetCodomainType
        targetRaw := RawTerm.lam targetBodyRaw
        targetTerm := Term.lamPi targetBodyTerm
        typeStrengthens := by
          change
            Option.mapTwo
              (domainType.partialStrengthen? strengthening.back)
              (codomainType.partialStrengthen? strengthening.back.lift)
              Ty.piTy =
              some (Ty.piTy targetDomainType targetCodomainType)
          rw [domainTypeStrengthens, codomainTypeStrengthensAtLift]
          rfl
        rawStrengthens := by
          change
            (match bodyRaw.partialStrengthen? strengthening.back.lift with
            | some strengthenedBody => some (RawTerm.lam strengthenedBody)
            | none => none) =
              some (RawTerm.lam targetBodyRaw)
          rw [bodyRawStrengthensAtLift]
        typeRenames :=
          Ty.partialStrengthen?_imp_rename
            (Ty.piTy domainType codomainType)
            strengthening.forward strengthening.back strengthening.injectsBack
            (Ty.piTy targetDomainType targetCodomainType)
            (by
              change
                Option.mapTwo
                  (domainType.partialStrengthen? strengthening.back)
                  (codomainType.partialStrengthen? strengthening.back.lift)
                  Ty.piTy =
                  some (Ty.piTy targetDomainType targetCodomainType)
              rw [domainTypeStrengthens, codomainTypeStrengthensAtLift]
              rfl)
        rawRenames :=
          RawTerm.partialStrengthen?_imp_rename
            (RawTerm.lam bodyRaw) strengthening.forward strengthening.back
            strengthening.injectsBack (RawTerm.lam targetBodyRaw)
            (by
              change
                (match bodyRaw.partialStrengthen?
                    strengthening.back.lift with
                | some strengthenedBody => some (RawTerm.lam strengthenedBody)
                | none => none) =
                  some (RawTerm.lam targetBodyRaw)
              rw [bodyRawStrengthensAtLift])
      }

/-- Cubical path lambda strengthens by strengthening the carrier and
endpoints, then strengthening the body under the lifted interval
context. -/
def partialStrengthenTypedPathLam {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {targetCarrierType : Ty level targetScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {targetLeftEndpoint targetRightEndpoint : RawTerm targetScope}
    {bodyRaw : RawTerm (sourceScope + 1)}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {body :
      Term (sourceCtx.cons Ty.interval) carrierType.weaken bodyRaw}
    (carrierStrengthens :
      carrierType.partialStrengthen? strengthening.back =
        some targetCarrierType)
    (leftEndpointStrengthens :
      leftEndpoint.partialStrengthen? strengthening.back =
        some targetLeftEndpoint)
    (rightEndpointStrengthens :
      rightEndpoint.partialStrengthen? strengthening.back =
        some targetRightEndpoint)
    (bodyResult : StrengtheningResult
      (strengthening.lift Ty.interval Ty.interval rfl) body) :
    StrengtheningResult strengthening
      (Term.pathLam modeIsUnivalent carrierType leftEndpoint
        rightEndpoint body) := by
  cases bodyResult with
  | mk targetBodyType targetBodyRaw targetBodyTerm bodyTypeStrengthens
      bodyRawStrengthens bodyTypeRenames bodyRawRenames =>
      have bodyTypeStrengthensAtLift :
          carrierType.weaken.partialStrengthen? strengthening.back.lift =
            some targetBodyType := by
        simpa only [ContextStrengthening.lift] using bodyTypeStrengthens
      have bodyRawStrengthensAtLift :
          bodyRaw.partialStrengthen? strengthening.back.lift =
            some targetBodyRaw := by
        simpa only [ContextStrengthening.lift] using bodyRawStrengthens
      have expectedBodyTypeStrengthens :
          carrierType.weaken.partialStrengthen? strengthening.back.lift =
            some targetCarrierType.weaken := by
        rw [Ty.partialStrengthen?_weaken_lift carrierType
          strengthening.back, carrierStrengthens]
        rfl
      rw [expectedBodyTypeStrengthens] at bodyTypeStrengthensAtLift
      cases bodyTypeStrengthensAtLift
      exact {
        targetType :=
          Ty.path targetCarrierType targetLeftEndpoint targetRightEndpoint
        targetRaw := RawTerm.pathLam targetBodyRaw
        targetTerm := Term.pathLam modeIsUnivalent targetCarrierType
          targetLeftEndpoint targetRightEndpoint targetBodyTerm
        typeStrengthens := by
          change
            Option.mapThree
              (carrierType.partialStrengthen? strengthening.back)
              (leftEndpoint.partialStrengthen? strengthening.back)
              (rightEndpoint.partialStrengthen? strengthening.back)
              Ty.path =
              some (Ty.path targetCarrierType targetLeftEndpoint
                targetRightEndpoint)
          rw [carrierStrengthens, leftEndpointStrengthens,
            rightEndpointStrengthens]
          rfl
        rawStrengthens := by
          change
            (match bodyRaw.partialStrengthen? strengthening.back.lift with
            | some strengthenedBody => some (RawTerm.pathLam strengthenedBody)
            | none => none) =
              some (RawTerm.pathLam targetBodyRaw)
          rw [bodyRawStrengthensAtLift]
        typeRenames :=
          Ty.partialStrengthen?_imp_rename
            (Ty.path carrierType leftEndpoint rightEndpoint)
            strengthening.forward strengthening.back strengthening.injectsBack
            (Ty.path targetCarrierType targetLeftEndpoint
              targetRightEndpoint)
            (by
              change
                Option.mapThree
                  (carrierType.partialStrengthen? strengthening.back)
                  (leftEndpoint.partialStrengthen? strengthening.back)
                  (rightEndpoint.partialStrengthen? strengthening.back)
                  Ty.path =
                  some (Ty.path targetCarrierType targetLeftEndpoint
                    targetRightEndpoint)
              rw [carrierStrengthens, leftEndpointStrengthens,
                rightEndpointStrengthens]
              rfl)
        rawRenames :=
          RawTerm.partialStrengthen?_imp_rename
            (RawTerm.pathLam bodyRaw) strengthening.forward
            strengthening.back strengthening.injectsBack
            (RawTerm.pathLam targetBodyRaw)
            (by
              change
                (match bodyRaw.partialStrengthen?
                    strengthening.back.lift with
                | some strengthenedBody =>
                    some (RawTerm.pathLam strengthenedBody)
                | none => none) =
                  some (RawTerm.pathLam targetBodyRaw)
              rw [bodyRawStrengthensAtLift])
      }

/-- Pre-witnessed cubical path-application strengthening.

Replaces the wrapper's dual `Option.casesOn` on
`Ty.path`'s carrier + leftEndpoint + rightEndpoint pivots with
explicit `carrierSuccess`/`leftSuccess`/`rightSuccess` witnesses.

The unused `leftSuccess`/`rightSuccess` are kept in the signature
(prefixed `_`) so the OfSuccess-sound theorem can recover the
endpoint renaming equalities used by `pathApp_HEq_congr`. -/
def partialStrengthenTypedPathAppOfSuccess
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {targetCarrierType : Ty level targetScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {targetLeftEndpoint targetRightEndpoint : RawTerm targetScope}
    {pathRaw intervalRaw : RawTerm sourceScope}
    {targetPathRaw targetIntervalRaw : RawTerm targetScope}
    {pathTerm :
      Term sourceCtx
        (Ty.path carrierType leftEndpoint rightEndpoint) pathRaw}
    {intervalTerm : Term sourceCtx Ty.interval intervalRaw}
    (targetPathTerm :
      Term targetCtx
        (Ty.path targetCarrierType targetLeftEndpoint targetRightEndpoint)
        targetPathRaw)
    (targetIntervalTerm :
      Term targetCtx Ty.interval targetIntervalRaw)
    (carrierSuccess :
      carrierType.partialStrengthen? strengthening.back =
        some targetCarrierType)
    (_leftSuccess :
      leftEndpoint.partialStrengthen? strengthening.back =
        some targetLeftEndpoint)
    (_rightSuccess :
      rightEndpoint.partialStrengthen? strengthening.back =
        some targetRightEndpoint)
    (pathRawStrengthens :
      pathRaw.partialStrengthen? strengthening.back = some targetPathRaw)
    (intervalRawStrengthens :
      intervalRaw.partialStrengthen? strengthening.back =
        some targetIntervalRaw)
    (pathRawRenames :
      pathRaw = targetPathRaw.rename strengthening.forward)
    (intervalRawRenames :
      intervalRaw = targetIntervalRaw.rename strengthening.forward) :
    StrengtheningResult strengthening
      (Term.pathApp modeIsUnivalent pathTerm intervalTerm) where
  targetType := targetCarrierType
  targetRaw := RawTerm.pathApp targetPathRaw targetIntervalRaw
  targetTerm :=
    Term.pathApp modeIsUnivalent targetPathTerm targetIntervalTerm
  typeStrengthens := carrierSuccess
  rawStrengthens := by
    change
      Option.mapTwo
        (pathRaw.partialStrengthen? strengthening.back)
        (intervalRaw.partialStrengthen? strengthening.back)
        RawTerm.pathApp =
        some (RawTerm.pathApp targetPathRaw targetIntervalRaw)
    rw [pathRawStrengthens, intervalRawStrengthens]
    rfl
  typeRenames :=
    Ty.partialStrengthen?_imp_rename carrierType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetCarrierType carrierSuccess
  rawRenames := by
    cases pathRawRenames
    cases intervalRawRenames
    rfl

/-- Cubical path application strengthens by strengthening the path and
interval argument.

App-pattern: takes `carrierSuccess`, `leftSuccess`, `rightSuccess` as
explicit parameters lifted from the dispatcher's three nested option-
splits on the path carrier type, left endpoint, and right endpoint
respectively.  Wrapper body destructures both `pathResult` and
`intervalResult`, aligns the `Ty.path` shape of the path's
`pathTypeStrengthens` via the standard `Option.mapThree` discharge
recipe, then delegates to `partialStrengthenTypedPathAppOfSuccess`.
Sister of `partialStrengthenTypedHcompPath` (Phase 42) — same
3-option-split shape applied to the second cubical path-elimination
producer. -/
def partialStrengthenTypedPathApp {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {targetCarrierType : Ty level targetScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {targetLeftEndpoint targetRightEndpoint : RawTerm targetScope}
    {pathRaw intervalRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {pathTerm : Term sourceCtx
      (Ty.path carrierType leftEndpoint rightEndpoint) pathRaw}
    {intervalTerm : Term sourceCtx Ty.interval intervalRaw}
    (carrierSuccess :
      carrierType.partialStrengthen? strengthening.back =
        some targetCarrierType)
    (leftSuccess :
      leftEndpoint.partialStrengthen? strengthening.back =
        some targetLeftEndpoint)
    (rightSuccess :
      rightEndpoint.partialStrengthen? strengthening.back =
        some targetRightEndpoint)
    (pathResult : StrengtheningResult strengthening pathTerm)
    (intervalResult : StrengtheningResult strengthening intervalTerm) :
    StrengtheningResult strengthening
      (Term.pathApp modeIsUnivalent pathTerm intervalTerm) := by
  cases pathResult with
  | mk targetPathType targetPathRaw targetPathTerm pathTypeStrengthens
      pathRawStrengthens pathTypeRenames pathRawRenames =>
      have expectedPathTypeStrengthens :
          (Ty.path carrierType leftEndpoint
              rightEndpoint).partialStrengthen?
              strengthening.back =
            some (Ty.path targetCarrierType targetLeftEndpoint
              targetRightEndpoint) := by
        change
          Option.mapThree
            (carrierType.partialStrengthen? strengthening.back)
            (leftEndpoint.partialStrengthen? strengthening.back)
            (rightEndpoint.partialStrengthen? strengthening.back)
            Ty.path =
              some (Ty.path targetCarrierType targetLeftEndpoint
                targetRightEndpoint)
        rw [carrierSuccess, leftSuccess, rightSuccess]
        rfl
      rw [expectedPathTypeStrengthens] at pathTypeStrengthens
      cases pathTypeStrengthens
      cases intervalResult with
      | mk targetIntervalType targetIntervalRaw targetIntervalTerm
          intervalTypeStrengthens intervalRawStrengthens
          intervalTypeRenames intervalRawRenames =>
          cases intervalTypeStrengthens
          exact partialStrengthenTypedPathAppOfSuccess
            modeIsUnivalent targetPathTerm targetIntervalTerm
            carrierSuccess leftSuccess rightSuccess
            pathRawStrengthens intervalRawStrengthens
            pathRawRenames intervalRawRenames

end Term

end LeanFX2
