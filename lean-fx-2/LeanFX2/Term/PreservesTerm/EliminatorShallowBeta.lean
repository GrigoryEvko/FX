import LeanFX2.Term.PreservesTerm.InlineDestructors

/-! # LeanFX2.Term.PreservesTerm.EliminatorShallowBeta

Tier 3 eliminator lifts with shallow β: single-Term-child
eliminators whose β fires when the child is the matching canonical
introducer.  Two-arm raw inversion (cong + β-deep); the β arm uses
an inline destructor from `InlineDestructors`.

Covers the cong-arm-only variants for the β cast wall (4):
lift_transp_cong, lift_pathApp_cong, lift_appPi_cong,
lift_app_cong; plus the five full shallow-β eliminator lifts
(5): modElim, recordProj, refineElim, glueElim, codataDest.

## Root status

Zero-axiom; carved from `Term/PreservesTerm.lean`. -/

namespace LeanFX2

variable {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}


/-! ## Tier 3 — eliminator lifts with shallow β (single-child)

Single-Term-child eliminators where β fires when the child is the
matching canonical introducer.  Two-arm raw inversion: cong + β-deep.

Recipe per β-firing eliminator:
  rcases <head>_inv rawStep with
    ⟨..., eq, congStep⟩
    | ⟨..., eq, βStep⟩
  case 1 (cong arm): apply childLift to congStep, wrap with Step.par.<elim>Cong
  case 2 (β arm): apply childLift to βStep (which yields a Term at
    canonical type), use the corresponding destructor to extract
    the canonical payload, then apply Step.par.beta<elim><Intro>Deep -/

/-- **Tier 3 — Term.transp lift, cong arm only.**  The transp_inv has
3 disjuncts: cong + transpReflBeta (constant-pathLam fires) +
transpReflBetaDeep.  The β arms require the path argument to develop
to a `RawTerm.pathLam typeRaw.weaken` form — checking this at the
typed level requires alignment between the pathLam's body-raw and the
schematic typeRaw payload, deferred. -/
theorem RawStep.par.lift_transp_cong
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType targetType : Ty level scope)
    (sourceTypeRaw targetTypeRaw : RawTerm scope)
    {pathRaw sourceRaw : RawTerm scope}
    (typePath :
      Term context
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw)
        pathRaw)
    (sourceValue : Term context sourceType sourceRaw)
    (typePathLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par pathRaw targetRawIH →
      ∃ typePathTarget :
          Term context
            (Ty.path (Ty.universe universeLevel universeLevelLt)
              sourceTypeRaw targetTypeRaw)
            targetRawIH,
        Step.par typePath typePathTarget)
    (sourceValueLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par sourceRaw targetRawIH →
      ∃ sourceValueTarget : Term context sourceType targetRawIH,
        Step.par sourceValue sourceValueTarget)
    {pathTargetRaw sourceTargetRaw : RawTerm scope}
    (pathStep : RawStep.par pathRaw pathTargetRaw)
    (sourceStep : RawStep.par sourceRaw sourceTargetRaw) :
    ∃ targetTerm :
        Term context targetType (RawTerm.transp pathTargetRaw sourceTargetRaw),
      Step.par
        (Term.transp modeIsUnivalent universeLevel universeLevelLt
          sourceType targetType sourceTypeRaw targetTypeRaw typePath sourceValue)
        targetTerm := by
  obtain ⟨typePathTarget, typePathStepTyped⟩ := typePathLift pathStep
  obtain ⟨sourceValueTarget, sourceValueStepTyped⟩ := sourceValueLift sourceStep
  exact ⟨Term.transp modeIsUnivalent universeLevel universeLevelLt
                     sourceType targetType
                     sourceTypeRaw targetTypeRaw typePathTarget sourceValueTarget,
         Step.par.transpCong modeIsUnivalent universeLevel universeLevelLt
                             sourceType targetType sourceTypeRaw targetTypeRaw
                             typePathStepTyped sourceValueStepTyped⟩

/-- **Tier 3 — Term.pathApp lift, cong arm only.**  The β-arms
(betaPathApp / betaPathReflApp) require body-substitution casts —
deferred per the lift_app comment. -/
theorem RawStep.par.lift_pathApp_cong
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {pathRaw intervalRaw : RawTerm scope}
    (pathTerm :
      Term context (Ty.path carrierType leftEndpoint rightEndpoint) pathRaw)
    (intervalTerm : Term context Ty.interval intervalRaw)
    (pathLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par pathRaw targetRawIH →
      ∃ pathTarget :
          Term context (Ty.path carrierType leftEndpoint rightEndpoint) targetRawIH,
        Step.par pathTerm pathTarget)
    (intervalLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par intervalRaw targetRawIH →
      ∃ intervalTarget : Term context Ty.interval targetRawIH,
        Step.par intervalTerm intervalTarget)
    {pathTargetRaw intervalTargetRaw : RawTerm scope}
    (pathStep : RawStep.par pathRaw pathTargetRaw)
    (intervalStep : RawStep.par intervalRaw intervalTargetRaw) :
    ∃ targetTerm :
        Term context carrierType (RawTerm.pathApp pathTargetRaw intervalTargetRaw),
      Step.par (Term.pathApp modeIsUnivalent pathTerm intervalTerm) targetTerm := by
  obtain ⟨pathTarget, pathStepTyped⟩ := pathLift pathStep
  obtain ⟨intervalTarget, intervalStepTyped⟩ := intervalLift intervalStep
  exact ⟨Term.pathApp modeIsUnivalent pathTarget intervalTarget,
         Step.par.pathApp modeIsUnivalent pathStepTyped intervalStepTyped⟩

/-- **Tier 3 — Term.appPi lift, cong arm only.**  Source/target Ty
shapes are identical (both `codomainType.subst0 domainType <argRaw>`)
when the function step is non-β; the β arm has the same cast wall as
`lift_app` (deferred). -/
theorem RawStep.par.lift_appPi_cong
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {functionRaw argumentRaw : RawTerm scope}
    (functionTerm : Term context (Ty.piTy domainType codomainType) functionRaw)
    (argumentTerm : Term context domainType argumentRaw)
    (functionLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par functionRaw targetRawIH →
      ∃ functionTarget :
          Term context (Ty.piTy domainType codomainType) targetRawIH,
        Step.par functionTerm functionTarget)
    (argumentLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par argumentRaw targetRawIH →
      ∃ argumentTarget : Term context domainType targetRawIH,
        Step.par argumentTerm argumentTarget)
    {functionTargetRaw argumentTargetRaw : RawTerm scope}
    (functionStep : RawStep.par functionRaw functionTargetRaw)
    (argumentStep : RawStep.par argumentRaw argumentTargetRaw) :
    ∃ targetTerm :
        Term context (codomainType.subst0 domainType argumentTargetRaw)
                     (RawTerm.app functionTargetRaw argumentTargetRaw),
      Step.par (Term.appPi functionTerm argumentTerm) targetTerm := by
  obtain ⟨functionTarget, functionStepTyped⟩ := functionLift functionStep
  obtain ⟨argumentTarget, argumentStepTyped⟩ := argumentLift argumentStep
  exact ⟨Term.appPi functionTarget argumentTarget,
         Step.par.appPi functionStepTyped argumentStepTyped⟩

/-- **Tier 3 — Term.app lift, cong arm only.**  The β arm of
`RawStep.par.app_inv` requires casting between `codomainType.weaken.
subst0 ...` and `codomainType` (related by
`Ty.weaken_subst_singleton`); the `▸`-rewrite propagates through the
existential's type binder.  A clean solution requires a HEq-shaped
existential or a more flexible cast helper — deferred to a future
phase.

This cong-only variant covers the case where `RawStep.par fnRaw
fnTargetRaw` does NOT reach a `RawTerm.lam` form — which is the
shape of every non-β raw step from `RawTerm.app`.  Specifically, when
the function's raw step is `refl` or any `app`-cong, the βApp arm of
the inversion does not fire; only the cong arm fires.

For the general case (including β-firing), use a richer headline that
allows the target Ty to differ via HEq — pending. -/
theorem RawStep.par.lift_app_cong
    {domainType codomainType : Ty level scope}
    {functionRaw argumentRaw : RawTerm scope}
    (functionTerm : Term context (Ty.arrow domainType codomainType) functionRaw)
    (argumentTerm : Term context domainType argumentRaw)
    (functionLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par functionRaw targetRawIH →
      ∃ functionTarget :
          Term context (Ty.arrow domainType codomainType) targetRawIH,
        Step.par functionTerm functionTarget)
    (argumentLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par argumentRaw targetRawIH →
      ∃ argumentTarget : Term context domainType targetRawIH,
        Step.par argumentTerm argumentTarget)
    {functionTargetRaw argumentTargetRaw : RawTerm scope}
    (functionStep : RawStep.par functionRaw functionTargetRaw)
    (argumentStep : RawStep.par argumentRaw argumentTargetRaw) :
    ∃ targetTerm :
        Term context codomainType (RawTerm.app functionTargetRaw argumentTargetRaw),
      Step.par (Term.app functionTerm argumentTerm) targetTerm := by
  obtain ⟨functionTarget, functionStepTyped⟩ := functionLift functionStep
  obtain ⟨argumentTarget, argumentStepTyped⟩ := argumentLift argumentStep
  exact ⟨Term.app functionTarget argumentTarget,
         Step.par.app functionStepTyped argumentStepTyped⟩
theorem RawStep.par.lift_modElim
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    (innerTerm : Term context innerType innerRaw)
    (innerLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par innerRaw targetRawIH →
      ∃ innerTarget : Term context innerType targetRawIH,
        Step.par innerTerm innerTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.modElim innerRaw) targetRaw) :
    ∃ targetTerm : Term context innerType targetRaw,
      Step.par (Term.modElim innerTerm) targetTerm := by
  rcases RawStep.par.modElim_inv rawStep with
    ⟨innerTargetRaw, eq, innerStep⟩
    | ⟨payloadTarget, eq, innerToModIntro⟩
  · obtain ⟨innerTarget, innerStepTyped⟩ := innerLift innerStep
    cases eq
    exact ⟨Term.modElim innerTarget, Step.par.modElim innerStepTyped⟩
  · obtain ⟨innerCanonical, innerStepTyped⟩ := innerLift innerToModIntro
    obtain ⟨payload, payloadHeq⟩ := Term.modIntroDestruct innerCanonical
    have payloadEq : innerCanonical = Term.modIntro payload := eq_of_heq payloadHeq
    rw [payloadEq] at innerStepTyped
    cases eq
    exact ⟨payload, Step.par.betaModElimIntroDeep innerStepTyped⟩

/-- **Tier 3 — Term.recordProj lift.**  Two-arm: cong + betaRecordProjIntro. -/
theorem RawStep.par.lift_recordProj
    {singleFieldType : Ty level scope}
    {recordRaw : RawTerm scope}
    (recordValue : Term context (Ty.record singleFieldType) recordRaw)
    (recordLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par recordRaw targetRawIH →
      ∃ recordTarget :
          Term context (Ty.record singleFieldType) targetRawIH,
        Step.par recordValue recordTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.recordProj recordRaw) targetRaw) :
    ∃ targetTerm : Term context singleFieldType targetRaw,
      Step.par (Term.recordProj recordValue) targetTerm := by
  rcases RawStep.par.recordProj_inv rawStep with
    ⟨recordTargetRaw, eq, recordStep⟩
    | ⟨firstTarget, eq, recordToIntro⟩
  · obtain ⟨recordTarget, recordStepTyped⟩ := recordLift recordStep
    cases eq
    exact ⟨Term.recordProj recordTarget, Step.par.recordProjCong recordStepTyped⟩
  · obtain ⟨recordCanonical, recordStepTyped⟩ := recordLift recordToIntro
    obtain ⟨firstField, firstHeq⟩ := Term.recordIntroDestruct recordCanonical
    have firstEq : recordCanonical = Term.recordIntro firstField := eq_of_heq firstHeq
    rw [firstEq] at recordStepTyped
    cases eq
    exact ⟨firstField, Step.par.betaRecordProjIntroDeep recordStepTyped⟩

/-- **Tier 3 — Term.refineElim lift.**  Two-arm: cong + betaRefineElimIntro.
The β arm extracts the typed value from a Term.refineIntro. -/
theorem RawStep.par.lift_refineElim
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {refinedRaw : RawTerm scope}
    (refinedValue : Term context (Ty.refine baseType predicate) refinedRaw)
    (refinedLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par refinedRaw targetRawIH →
      ∃ refinedTarget :
          Term context (Ty.refine baseType predicate) targetRawIH,
        Step.par refinedValue refinedTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.refineElim refinedRaw) targetRaw) :
    ∃ targetTerm : Term context baseType targetRaw,
      Step.par (Term.refineElim refinedValue) targetTerm := by
  rcases RawStep.par.refineElim_inv rawStep with
    ⟨refinedTargetRaw, eq, refinedStep⟩
    | ⟨valueTarget, proofTarget, eq, refinedToIntro⟩
  · obtain ⟨refinedTarget, refinedStepTyped⟩ := refinedLift refinedStep
    cases eq
    exact ⟨Term.refineElim refinedTarget,
           Step.par.refineElimCong refinedStepTyped⟩
  · obtain ⟨refinedCanonical, refinedStepTyped⟩ := refinedLift refinedToIntro
    obtain ⟨baseValue, predicateProof, valueHeq⟩ :=
      Term.refineIntroDestruct predicate refinedCanonical
    have valueEq :
        refinedCanonical = Term.refineIntro predicate baseValue predicateProof :=
      eq_of_heq valueHeq
    rw [valueEq] at refinedStepTyped
    cases eq
    exact ⟨baseValue, Step.par.betaRefineElimIntroDeep refinedStepTyped⟩

/-- **Tier 3 — Term.glueElim lift.**  Two-arm: cong + betaGlueElimIntro.
The β arm extracts the typed base from a Term.glueIntro. -/
theorem RawStep.par.lift_glueElim
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level scope}
    {boundaryWitness : RawTerm scope}
    {gluedRaw : RawTerm scope}
    (gluedValue : Term context (Ty.glue baseType boundaryWitness) gluedRaw)
    (gluedLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par gluedRaw targetRawIH →
      ∃ gluedTarget :
          Term context (Ty.glue baseType boundaryWitness) targetRawIH,
        Step.par gluedValue gluedTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.glueElim gluedRaw) targetRaw) :
    ∃ targetTerm : Term context baseType targetRaw,
      Step.par (Term.glueElim modeIsUnivalent gluedValue) targetTerm := by
  rcases RawStep.par.glueElim_inv rawStep with
    ⟨gluedTargetRaw, eq, gluedStep⟩
    | ⟨baseTarget, partialTarget, eq, gluedToIntro⟩
  · obtain ⟨gluedTarget, gluedStepTyped⟩ := gluedLift gluedStep
    cases eq
    exact ⟨Term.glueElim modeIsUnivalent gluedTarget,
           Step.par.glueElimCong modeIsUnivalent gluedStepTyped⟩
  · obtain ⟨gluedCanonical, gluedStepTyped⟩ := gluedLift gluedToIntro
    obtain ⟨baseValue, partialValue, glueHeq⟩ :=
      Term.glueIntroDestruct modeIsUnivalent baseType boundaryWitness gluedCanonical
    have glueEq :
        gluedCanonical = Term.glueIntro modeIsUnivalent baseType boundaryWitness
                                        baseValue partialValue :=
      eq_of_heq glueHeq
    rw [glueEq] at gluedStepTyped
    cases eq
    exact ⟨baseValue, Step.par.betaGlueElimIntroDeep modeIsUnivalent gluedStepTyped⟩

/-- **Tier 3 — Term.codataDest lift.**  Two-arm: cong + betaCodataDestUnfold.
The β arm extracts the typed initial state and transition from a
Term.codataUnfold; the iota target is `app transition initialState`. -/
theorem RawStep.par.lift_codataDest
    {stateType outputType : Ty level scope}
    {codataRaw : RawTerm scope}
    (codataValue : Term context (Ty.codata stateType outputType) codataRaw)
    (codataLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par codataRaw targetRawIH →
      ∃ codataTarget :
          Term context (Ty.codata stateType outputType) targetRawIH,
        Step.par codataValue codataTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.codataDest codataRaw) targetRaw) :
    ∃ targetTerm : Term context outputType targetRaw,
      Step.par (Term.codataDest codataValue) targetTerm := by
  rcases RawStep.par.codataDest_inv rawStep with
    ⟨codataTargetRaw, eq, codataStep⟩
    | ⟨stateTarget, transitionTarget, eq, codataToUnfold⟩
  · obtain ⟨codataTarget, codataStepTyped⟩ := codataLift codataStep
    cases eq
    exact ⟨Term.codataDest codataTarget,
           Step.par.codataDestCong codataStepTyped⟩
  · obtain ⟨codataCanonical, codataStepTyped⟩ := codataLift codataToUnfold
    obtain ⟨initialState, transition, codataHeq⟩ :=
      Term.codataUnfoldDestruct codataCanonical
    have codataEq :
        codataCanonical = Term.codataUnfold initialState transition :=
      eq_of_heq codataHeq
    rw [codataEq] at codataStepTyped
    cases eq
    exact ⟨Term.app transition initialState,
           Step.par.betaCodataDestUnfoldDeep codataStepTyped⟩

end LeanFX2
