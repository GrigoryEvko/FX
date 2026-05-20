import LeanFX2.Term.StrengtheningImage.AggregatorTotalBridgeEliminators

/-! # Term/StrengtheningImage/AggregatorTotalBridgeCasts

Bridge totality wrappers for cast-heavy snd, appPi, transp, and effect-performance constructors.
-/

namespace LeanFX2

namespace Term

/-- Bridge totality wrapper for `Term.snd`.  Source type is
`secondType.subst0 firstType (RawTerm.fst pairRaw)`; dispatcher needs
firstType.back + secondType.back.lift + pairTerm IH (Ty.sigmaTy).
Take firstType.back + secondType.back.lift as extra hypotheses. -/
theorem isAggregatorTotal_snd_with_sigma_witnesses {mode : Mode}
    {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {pairRaw : RawTerm sourceScope}
    {pairTerm : Term sourceCtx (Ty.sigmaTy firstType secondType) pairRaw}
    (pairTotal : IsAggregatorTotal pairTerm)
    (sigmaTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetSourceType : Ty level targetScope},
        (secondType.subst0 firstType
          (RawTerm.fst pairRaw)).partialStrengthen? strengthening.back =
            some targetSourceType →
        ∃ targetFirstType targetSecondType,
          firstType.partialStrengthen? strengthening.back =
              some targetFirstType ∧
          secondType.partialStrengthen? strengthening.back.lift =
              some targetSecondType) :
    IsAggregatorTotal (Term.snd pairTerm) := by
  intros _ _ strengthening _ _ typeStrengthens rawStrengthens
  unfold RawTerm.partialStrengthen? at rawStrengthens
  unfold RawTerm.partialRename? at rawStrengthens
  split at rawStrengthens
  rotate_left
  · cases rawStrengthens
  next targetPairRaw pairRawRenSuccess =>
    have pairRawSuccess :
        pairRaw.partialStrengthen? strengthening.back =
          some targetPairRaw := pairRawRenSuccess
    obtain ⟨targetFirstType, targetSecondType, firstSuccess,
      secondSuccess⟩ :=
      sigmaTotal strengthening typeStrengthens
    have sigmaTypeStrengthens :
        (Ty.sigmaTy firstType secondType).partialStrengthen?
            strengthening.back =
          some (Ty.sigmaTy targetFirstType targetSecondType) := by
      show Option.mapTwo
          (firstType.partialStrengthen? strengthening.back)
          (secondType.partialStrengthen? strengthening.back.lift)
          Ty.sigmaTy = _
      rw [firstSuccess, secondSuccess]
      rfl
    have pairTotalCall :=
      pairTotal strengthening sigmaTypeStrengthens pairRawSuccess
    unfold partialStrengthenTyped?
    split
    · next firstFails =>
        rw [firstSuccess] at firstFails
        cases firstFails
    · next _ _ =>
        split
        · next secondFails =>
            rw [secondSuccess] at secondFails
            cases secondFails
        · next _ _ =>
            split
            · next pairFails =>
                rw [pairFails] at pairTotalCall
                cases pairTotalCall
            · rfl

/-- Bridge totality wrapper for `Term.appPi`.  Source type is
`codomainType.subst0 domainType argumentRaw`; dispatcher needs
domainType.back + codomainType.back.lift + function IH (Ty.piTy) +
argument IH (domainType).  Take domain + codomain witnesses as
extra hypotheses. -/
theorem isAggregatorTotal_appPi_with_pi_witnesses {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {domainType : Ty level sourceScope}
    {codomainType : Ty level (sourceScope + 1)}
    {functionRaw argumentRaw : RawTerm sourceScope}
    {functionTerm :
      Term sourceCtx (Ty.piTy domainType codomainType) functionRaw}
    {argumentTerm : Term sourceCtx domainType argumentRaw}
    (functionTotal : IsAggregatorTotal functionTerm)
    (argumentTotal : IsAggregatorTotal argumentTerm)
    (piTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetSourceType : Ty level targetScope},
        (codomainType.subst0 domainType argumentRaw).partialStrengthen?
            strengthening.back =
            some targetSourceType →
        ∃ targetDomainType targetCodomainType,
          domainType.partialStrengthen? strengthening.back =
              some targetDomainType ∧
          codomainType.partialStrengthen? strengthening.back.lift =
              some targetCodomainType) :
    IsAggregatorTotal (Term.appPi functionTerm argumentTerm) := by
  intros _ _ strengthening _ _ typeStrengthens rawStrengthens
  change Option.mapTwo
      (functionRaw.partialStrengthen? strengthening.back)
      (argumentRaw.partialStrengthen? strengthening.back)
      RawTerm.app = some _ at rawStrengthens
  obtain ⟨_, _, functionRawSuccess, argumentRawSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  obtain ⟨targetDomainType, targetCodomainType, domainSuccess,
    codomainSuccess⟩ :=
    piTotal strengthening typeStrengthens
  -- functionTerm type: Ty.piTy domainType codomainType
  have piTypeStrengthens :
      (Ty.piTy domainType codomainType).partialStrengthen?
          strengthening.back =
        some (Ty.piTy targetDomainType targetCodomainType) := by
    show Option.mapTwo
        (domainType.partialStrengthen? strengthening.back)
        (codomainType.partialStrengthen? strengthening.back.lift)
        Ty.piTy = _
    rw [domainSuccess, codomainSuccess]
    rfl
  have functionTotalCall :=
    functionTotal strengthening piTypeStrengthens functionRawSuccess
  have argumentTotalCall :=
    argumentTotal strengthening domainSuccess argumentRawSuccess
  unfold partialStrengthenTyped?
  split
  · next domainFails =>
      rw [domainSuccess] at domainFails
      cases domainFails
  · next _ _ =>
      split
      · next codomainFails =>
          rw [codomainSuccess] at codomainFails
          cases codomainFails
      · next _ _ =>
          split
          · next functionFails =>
              rw [functionFails] at functionTotalCall
              cases functionTotalCall
          · next _ _ =>
              split
              · next argumentFails =>
                  rw [argumentFails] at argumentTotalCall
                  cases argumentTotalCall
              · rfl

/-- Bridge totality wrapper for `Term.transp`.  Source type is
`targetType`; dispatcher needs sourceType.back + targetType.back +
sourceTypeRaw.back + targetTypeRaw.back + 2 IH children.  Take the
3 missing witnesses (sourceType, sourceTypeRaw, targetTypeRaw) as
extra hypotheses. -/
theorem isAggregatorTotal_transp_with_path_witnesses {mode : Mode}
    {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType targetType : Ty level sourceScope)
    (sourceTypeRaw targetTypeRaw : RawTerm sourceScope)
    {pathRaw sourceRaw : RawTerm sourceScope}
    {typePath :
      Term sourceCtx
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw)
        pathRaw}
    {sourceValue : Term sourceCtx sourceType sourceRaw}
    (pathTotal : IsAggregatorTotal typePath)
    (sourceTotal : IsAggregatorTotal sourceValue)
    (transpWitnessesTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetTargetType : Ty level targetScope},
        targetType.partialStrengthen? strengthening.back =
            some targetTargetType →
        ∃ targetSourceType targetSourceTypeRaw targetTargetTypeRaw,
          sourceType.partialStrengthen? strengthening.back =
              some targetSourceType ∧
          sourceTypeRaw.partialStrengthen? strengthening.back =
              some targetSourceTypeRaw ∧
          targetTypeRaw.partialStrengthen? strengthening.back =
              some targetTargetTypeRaw) :
    IsAggregatorTotal
      (Term.transp modeIsUnivalent universeLevel universeLevelLt
        sourceType targetType sourceTypeRaw targetTypeRaw
        typePath sourceValue) := by
  intros _ _ strengthening targetTargetType _ typeStrengthens rawStrengthens
  change Option.mapTwo
      (pathRaw.partialStrengthen? strengthening.back)
      (sourceRaw.partialStrengthen? strengthening.back)
      RawTerm.transp = some _ at rawStrengthens
  obtain ⟨_, _, pathRawSuccess, sourceRawSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  obtain ⟨targetSourceType, targetSourceTypeRaw, targetTargetTypeRaw,
    sourceTypeSuccess, sourceTypeRawSuccess, targetTypeRawSuccess⟩ :=
    transpWitnessesTotal strengthening typeStrengthens
  -- typePath's type: Ty.path (Ty.universe ...) sourceTypeRaw targetTypeRaw
  have universeStrengthens :
      (Ty.universe universeLevel universeLevelLt :
          Ty level sourceScope).partialStrengthen?
          strengthening.back =
        some (Ty.universe universeLevel universeLevelLt) := rfl
  have pathTypeStrengthens :
      (Ty.path (Ty.universe universeLevel universeLevelLt)
        sourceTypeRaw targetTypeRaw).partialStrengthen?
          strengthening.back =
        some (Ty.path (Ty.universe universeLevel universeLevelLt)
          targetSourceTypeRaw targetTargetTypeRaw) := by
    show Option.mapThree
        ((Ty.universe universeLevel universeLevelLt :
            Ty level sourceScope).partialStrengthen?
          strengthening.back)
        (sourceTypeRaw.partialStrengthen? strengthening.back)
        (targetTypeRaw.partialStrengthen? strengthening.back)
        Ty.path = _
    rw [universeStrengthens, sourceTypeRawSuccess, targetTypeRawSuccess]
    rfl
  have pathTotalCall :=
    pathTotal strengthening pathTypeStrengthens pathRawSuccess
  have sourceTotalCall :=
    sourceTotal strengthening sourceTypeSuccess sourceRawSuccess
  unfold partialStrengthenTyped?
  split
  · next sourceTypeFails =>
      rw [sourceTypeSuccess] at sourceTypeFails
      cases sourceTypeFails
  · next _ _ =>
      split
      · next targetTypeFails =>
          rw [typeStrengthens] at targetTypeFails
          cases targetTypeFails
      · next _ _ =>
          split
          · next sourceTypeRawFails =>
              rw [sourceTypeRawSuccess] at sourceTypeRawFails
              cases sourceTypeRawFails
          · next _ _ =>
              split
              · next targetTypeRawFails =>
                  rw [targetTypeRawSuccess] at targetTypeRawFails
                  cases targetTypeRawFails
              · next _ _ =>
                  split
                  · next pathFails =>
                      rw [pathFails] at pathTotalCall
                      cases pathTotalCall
                  · next _ _ =>
                      split
                      · next sourceFails =>
                          rw [sourceFails] at sourceTotalCall
                          cases sourceTotalCall
                      · rfl

/-- Bridge totality wrapper for `Term.effectPerform`.  Source type is
`Ty.effect resultCarrier effectTag`; the dispatcher needs
`effectTag.back` + `argumentCarrier.back` + `resultCarrier.back` +
operationTag IH + arguments IH.  Decomposing the source-type
strengthening yields `effectTag.back` and `resultCarrier.back`
through `Option.mapTwo_eq_some`, but `argumentCarrier.back` is NOT
recoverable from `Ty.effect resultCarrier effectTag` alone — take
it as an explicit aux witness (parametric on strengthening). -/
theorem isAggregatorTotal_effectPerform_with_opsig_witness {mode : Mode}
    {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (effectTag : RawTerm sourceScope)
    (effectRow : Effects.EffectRow)
    (operationSignature : Effects.OperationSignature (Ty level sourceScope))
    (canPerformOperation :
      Effects.CanPerform effectRow operationSignature)
    {operationRaw argumentsRaw : RawTerm sourceScope}
    {operationTag :
      Term sourceCtx
        (Ty.effect operationSignature.argumentCarrier effectTag)
        operationRaw}
    {arguments :
      Term sourceCtx operationSignature.argumentCarrier argumentsRaw}
    (operationTotal : IsAggregatorTotal operationTag)
    (argumentsTotal : IsAggregatorTotal arguments)
    (argumentCarrierTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetEffectTag : RawTerm targetScope}
        {targetResultCarrier : Ty level targetScope},
        effectTag.partialStrengthen? strengthening.back =
            some targetEffectTag →
        operationSignature.resultCarrier.partialStrengthen?
            strengthening.back =
            some targetResultCarrier →
        ∃ targetArgumentCarrier,
          operationSignature.argumentCarrier.partialStrengthen?
              strengthening.back =
            some targetArgumentCarrier) :
    IsAggregatorTotal
      (Term.effectPerform (context := sourceCtx) effectTag effectRow
        operationSignature canPerformOperation operationTag arguments) := by
  intros _ _ strengthening _ _ typeStrengthens rawStrengthens
  -- typeStrengthens decomposes Ty.effect resultCarrier effectTag
  change Option.mapTwo
      (operationSignature.resultCarrier.partialStrengthen?
        strengthening.back)
      (effectTag.partialStrengthen? strengthening.back)
      Ty.effect = some _ at typeStrengthens
  obtain ⟨targetResultCarrier, targetEffectTag, resultCarrierSuccess,
    effectTagSuccess, _⟩ := Option.mapTwo_eq_some typeStrengthens
  -- rawStrengthens decomposes RawTerm.effectPerform operationRaw argumentsRaw
  change Option.mapTwo
      (operationRaw.partialStrengthen? strengthening.back)
      (argumentsRaw.partialStrengthen? strengthening.back)
      RawTerm.effectPerform = some _ at rawStrengthens
  obtain ⟨_, _, operationRawSuccess, argumentsRawSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  obtain ⟨targetArgumentCarrier, argumentCarrierSuccess⟩ :=
    argumentCarrierTotal strengthening effectTagSuccess
      resultCarrierSuccess
  -- operationTag's type: Ty.effect argumentCarrier effectTag
  have operationTagTypeStrengthens :
      (Ty.effect operationSignature.argumentCarrier effectTag).partialStrengthen?
          strengthening.back =
        some (Ty.effect targetArgumentCarrier targetEffectTag) := by
    show Option.mapTwo
        (operationSignature.argumentCarrier.partialStrengthen?
          strengthening.back)
        (effectTag.partialStrengthen? strengthening.back)
        Ty.effect = _
    rw [argumentCarrierSuccess, effectTagSuccess]
    rfl
  have operationTotalCall :=
    operationTotal strengthening operationTagTypeStrengthens
      operationRawSuccess
  have argumentsTotalCall :=
    argumentsTotal strengthening argumentCarrierSuccess
      argumentsRawSuccess
  unfold partialStrengthenTyped?
  split
  · next effectTagFails =>
      rw [effectTagSuccess] at effectTagFails
      cases effectTagFails
  · next _ _ =>
      split
      · next argumentCarrierFails =>
          rw [argumentCarrierSuccess] at argumentCarrierFails
          cases argumentCarrierFails
      · next _ _ =>
          split
          · next resultCarrierFails =>
              rw [resultCarrierSuccess] at resultCarrierFails
              cases resultCarrierFails
          · next _ _ =>
              split
              · next operationFails =>
                  rw [operationFails] at operationTotalCall
                  cases operationTotalCall
              · next _ _ =>
                  split
                  · next argumentsFails =>
                      rw [argumentsFails] at argumentsTotalCall
                      cases argumentsTotalCall
                  · rfl

end Term

end LeanFX2
