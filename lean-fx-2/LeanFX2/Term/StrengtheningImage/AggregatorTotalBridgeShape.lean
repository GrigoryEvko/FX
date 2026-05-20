import LeanFX2.Term.StrengtheningImage.AggregatorTotalWrapable

/-! # Term/StrengtheningImage/AggregatorTotalBridgeShape

Bridge totality wrappers for shape witnesses on path, hcomp, glue, codata, projection, equivalence, refinement, and app.
-/

namespace LeanFX2

namespace Term

/-! ## Phase Y.2: Bridge wrappers for ctors whose source type lacks
    sub-Ty / sub-raw witnesses the dispatcher reads.

    These wrappers take per-ctor auxiliary witnesses as additional
    hypotheses (modeled on Agent C's Phase X bridge for
    `isTotalOnWeaken_of_weaken_isAggregatorTotal`).  The wrapper still
    discharges `IsAggregatorTotal` at the source ctor application;
    downstream consumers supply the auxiliary witnesses case-by-case.

    The universal-over-all-source-terms headline
    `∀ t, IsAggregatorTotal t` is NOT shippable for these ctors at the
    current predicate, but per-ctor wrappers with case-specific witness
    construction are.  Consumers route through these wrappers when
    the source-level witnesses are constructible in their context. -/

/-- Bridge totality wrapper for `Term.pathApp`.  The dispatcher arm
needs leftEndpoint.back + rightEndpoint.back + carrierType.back, but
the source type encodes only carrierType.  We take the missing
endpoint strengthenings as additional hypotheses parameterized over
strengthening (universally, matching IsAggregatorTotal's shape).

Consumers satisfy these hypotheses when leftEndpoint and rightEndpoint
have known strengthening behaviour (e.g. when they're proved totally
strengthenable independently). -/
theorem isAggregatorTotal_pathApp_with_endpoints {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {pathRaw intervalRaw : RawTerm sourceScope}
    {pathTerm :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint)
        pathRaw}
    {intervalTerm : Term sourceCtx Ty.interval intervalRaw}
    (pathTotal : IsAggregatorTotal pathTerm)
    (intervalTotal : IsAggregatorTotal intervalTerm)
    (leftEndpointTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetCarrierType : Ty level targetScope},
        carrierType.partialStrengthen? strengthening.back =
            some targetCarrierType →
        ∃ targetLeftEndpoint,
          leftEndpoint.partialStrengthen? strengthening.back =
            some targetLeftEndpoint)
    (rightEndpointTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetCarrierType : Ty level targetScope},
        carrierType.partialStrengthen? strengthening.back =
            some targetCarrierType →
        ∃ targetRightEndpoint,
          rightEndpoint.partialStrengthen? strengthening.back =
            some targetRightEndpoint) :
    IsAggregatorTotal
      (Term.pathApp modeIsUnivalent pathTerm intervalTerm) := by
  intros _ _ strengthening targetCarrierType _ typeStrengthens rawStrengthens
  -- typeStrengthens : carrierType.back = some targetCarrierType
  -- rawStrengthens : (RawTerm.pathApp pathRaw intervalRaw).back = some _
  change Option.mapTwo
      (pathRaw.partialStrengthen? strengthening.back)
      (intervalRaw.partialStrengthen? strengthening.back)
      RawTerm.pathApp = some _ at rawStrengthens
  obtain ⟨_, _, pathRawSuccess, intervalRawSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  -- Get the endpoint strengthenings from the auxiliary hypotheses
  obtain ⟨targetLeftEndpoint, leftEndpointSuccess⟩ :=
    leftEndpointTotal strengthening typeStrengthens
  obtain ⟨targetRightEndpoint, rightEndpointSuccess⟩ :=
    rightEndpointTotal strengthening typeStrengthens
  -- Construct pathTerm's type strengthening: Ty.path.mapThree
  have pathTypeStrengthens :
      (Ty.path carrierType leftEndpoint rightEndpoint).partialStrengthen?
          strengthening.back =
        some (Ty.path targetCarrierType targetLeftEndpoint
          targetRightEndpoint) := by
    show Option.mapThree
        (carrierType.partialStrengthen? strengthening.back)
        (leftEndpoint.partialStrengthen? strengthening.back)
        (rightEndpoint.partialStrengthen? strengthening.back)
        Ty.path = _
    rw [typeStrengthens, leftEndpointSuccess, rightEndpointSuccess]
    rfl
  -- Construct intervalTerm's type strengthening: Ty.interval is closed-atomic
  have intervalTypeStrengthens :
      (Ty.interval : Ty level sourceScope).partialStrengthen?
          strengthening.back =
        some Ty.interval := rfl
  have pathTotalCall :=
    pathTotal strengthening pathTypeStrengthens pathRawSuccess
  have intervalTotalCall :=
    intervalTotal strengthening intervalTypeStrengthens intervalRawSuccess
  dsimp only [partialStrengthenTyped?]
  split
  · next carrierFails =>
      rw [typeStrengthens] at carrierFails
      cases carrierFails
  · next _ _ =>
      split
      · next leftFails =>
          rw [leftEndpointSuccess] at leftFails
          cases leftFails
      · next _ _ =>
          split
          · next rightFails =>
              rw [rightEndpointSuccess] at rightFails
              cases rightFails
          · next _ _ =>
              split
              · next pathFails =>
                  rw [pathFails] at pathTotalCall
                  cases pathTotalCall
              · next _ _ =>
                  split
                  · next intervalFails =>
                      rw [intervalFails] at intervalTotalCall
                      cases intervalTotalCall
                  · rfl

/-- Bridge totality wrapper for `Term.hcompPath`.  Like `pathApp`, the
endpoints are dispatcher-needed but not in source.  Take endpoint
strengthening witnesses as extra hypotheses. -/
theorem isAggregatorTotal_hcompPath_with_endpoints {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    (leftEndpoint rightEndpoint : RawTerm sourceScope)
    {sidesPathRaw capRaw : RawTerm sourceScope}
    {sidesPath :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint)
        sidesPathRaw}
    {capValue : Term sourceCtx carrierType capRaw}
    (sidesPathTotal : IsAggregatorTotal sidesPath)
    (capTotal : IsAggregatorTotal capValue)
    (leftEndpointTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetCarrierType : Ty level targetScope},
        carrierType.partialStrengthen? strengthening.back =
            some targetCarrierType →
        ∃ targetLeftEndpoint,
          leftEndpoint.partialStrengthen? strengthening.back =
            some targetLeftEndpoint)
    (rightEndpointTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetCarrierType : Ty level targetScope},
        carrierType.partialStrengthen? strengthening.back =
            some targetCarrierType →
        ∃ targetRightEndpoint,
          rightEndpoint.partialStrengthen? strengthening.back =
            some targetRightEndpoint) :
    IsAggregatorTotal
      (Term.hcompPath modeIsUnivalent leftEndpoint rightEndpoint
        sidesPath capValue) := by
  intros _ _ strengthening targetCarrierType _ typeStrengthens rawStrengthens
  change Option.mapTwo
      (sidesPathRaw.partialStrengthen? strengthening.back)
      (capRaw.partialStrengthen? strengthening.back)
      RawTerm.hcomp = some _ at rawStrengthens
  obtain ⟨_, _, sidesPathRawSuccess, capRawSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  obtain ⟨targetLeftEndpoint, leftEndpointSuccess⟩ :=
    leftEndpointTotal strengthening typeStrengthens
  obtain ⟨targetRightEndpoint, rightEndpointSuccess⟩ :=
    rightEndpointTotal strengthening typeStrengthens
  have pathTypeStrengthens :
      (Ty.path carrierType leftEndpoint rightEndpoint).partialStrengthen?
          strengthening.back =
        some (Ty.path targetCarrierType targetLeftEndpoint
          targetRightEndpoint) := by
    show Option.mapThree
        (carrierType.partialStrengthen? strengthening.back)
        (leftEndpoint.partialStrengthen? strengthening.back)
        (rightEndpoint.partialStrengthen? strengthening.back)
        Ty.path = _
    rw [typeStrengthens, leftEndpointSuccess, rightEndpointSuccess]
    rfl
  have sidesPathTotalCall :=
    sidesPathTotal strengthening pathTypeStrengthens sidesPathRawSuccess
  have capTotalCall :=
    capTotal strengthening typeStrengthens capRawSuccess
  dsimp only [partialStrengthenTyped?]
  split
  · next carrierFails =>
      rw [typeStrengthens] at carrierFails
      cases carrierFails
  · next _ _ =>
      split
      · next leftFails =>
          rw [leftEndpointSuccess] at leftFails
          cases leftFails
      · next _ _ =>
          split
          · next rightFails =>
              rw [rightEndpointSuccess] at rightFails
              cases rightFails
          · next _ _ =>
              split
              · next sidesPathFails =>
                  rw [sidesPathFails] at sidesPathTotalCall
                  cases sidesPathTotalCall
              · next _ _ =>
                  split
                  · next capFails =>
                      rw [capFails] at capTotalCall
                      cases capTotalCall
                  · rfl

/-- Bridge totality wrapper for `Term.glueElim`.  Source type is
`baseType`; dispatcher needs baseType.back + boundaryWitness.back +
gluedValue IH (type `Ty.glue baseType boundaryWitness`).  Take
boundaryWitness strengthening as extra hypothesis. -/
theorem isAggregatorTotal_glueElim_with_boundary {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level sourceScope}
    {boundaryWitness gluedRaw : RawTerm sourceScope}
    {gluedValue :
      Term sourceCtx (Ty.glue baseType boundaryWitness) gluedRaw}
    (gluedTotal : IsAggregatorTotal gluedValue)
    (boundaryTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetBaseType : Ty level targetScope},
        baseType.partialStrengthen? strengthening.back =
            some targetBaseType →
        ∃ targetBoundaryWitness,
          boundaryWitness.partialStrengthen? strengthening.back =
            some targetBoundaryWitness) :
    IsAggregatorTotal
      (Term.glueElim modeIsUnivalent gluedValue) := by
  intros _ _ strengthening targetBaseType _ typeStrengthens rawStrengthens
  dsimp only [RawTerm.partialStrengthen?, RawTerm.partialRename?] at rawStrengthens
  split at rawStrengthens
  rotate_left
  · cases rawStrengthens
  next targetGluedRaw gluedRawRenameSuccess =>
    have gluedRawSuccess :
        gluedRaw.partialStrengthen? strengthening.back =
          some targetGluedRaw := gluedRawRenameSuccess
    obtain ⟨targetBoundaryWitness, boundarySuccess⟩ :=
      boundaryTotal strengthening typeStrengthens
    have glueTypeStrengthens :
        (Ty.glue baseType boundaryWitness).partialStrengthen?
            strengthening.back =
          some (Ty.glue targetBaseType targetBoundaryWitness) := by
      show Option.mapTwo
          (baseType.partialStrengthen? strengthening.back)
          (boundaryWitness.partialStrengthen? strengthening.back)
          Ty.glue = _
      rw [typeStrengthens, boundarySuccess]
      rfl
    have gluedTotalCall :=
      gluedTotal strengthening glueTypeStrengthens gluedRawSuccess
    dsimp only [partialStrengthenTyped?]
    split
    · next baseFails =>
        rw [typeStrengthens] at baseFails
        cases baseFails
    · next _ _ =>
        split
        · next boundaryFails =>
            rw [boundarySuccess] at boundaryFails
            cases boundaryFails
        · next _ _ =>
            split
            · next gluedFails =>
                rw [gluedFails] at gluedTotalCall
                cases gluedTotalCall
            · rfl

/-- Bridge totality wrapper for `Term.codataDest`.  Source type is
`outputType`; dispatcher needs stateType.back + outputType.back +
codataValue IH (type `Ty.codata stateType outputType`).  Take
stateType strengthening as extra hypothesis. -/
theorem isAggregatorTotal_codataDest_with_state {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {stateType outputType : Ty level sourceScope}
    {codataRaw : RawTerm sourceScope}
    {codataValue :
      Term sourceCtx (Ty.codata stateType outputType) codataRaw}
    (codataTotal : IsAggregatorTotal codataValue)
    (stateTypeTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetOutputType : Ty level targetScope},
        outputType.partialStrengthen? strengthening.back =
            some targetOutputType →
        ∃ targetStateType,
          stateType.partialStrengthen? strengthening.back =
            some targetStateType) :
    IsAggregatorTotal (Term.codataDest codataValue) := by
  intros _ _ strengthening targetOutputType _ typeStrengthens rawStrengthens
  dsimp only [RawTerm.partialStrengthen?, RawTerm.partialRename?] at rawStrengthens
  split at rawStrengthens
  rotate_left
  · cases rawStrengthens
  next targetCodataRaw codataRawRenameSuccess =>
    have codataRawSuccess :
        codataRaw.partialStrengthen? strengthening.back =
          some targetCodataRaw := codataRawRenameSuccess
    obtain ⟨targetStateType, stateTypeSuccess⟩ :=
      stateTypeTotal strengthening typeStrengthens
    have codataTypeStrengthens :
        (Ty.codata stateType outputType).partialStrengthen?
            strengthening.back =
          some (Ty.codata targetStateType targetOutputType) := by
      show Option.mapTwo
          (stateType.partialStrengthen? strengthening.back)
          (outputType.partialStrengthen? strengthening.back)
          Ty.codata = _
      rw [stateTypeSuccess, typeStrengthens]
      rfl
    have codataTotalCall :=
      codataTotal strengthening codataTypeStrengthens codataRawSuccess
    dsimp only [partialStrengthenTyped?]
    split
    · next stateFails =>
        rw [stateTypeSuccess] at stateFails
        cases stateFails
    · next _ _ =>
        split
        · next outputFails =>
            rw [typeStrengthens] at outputFails
            cases outputFails
        · next _ _ =>
            split
            · next codataFails =>
                rw [codataFails] at codataTotalCall
                cases codataTotalCall
            · rfl

/-- Bridge totality wrapper for `Term.fst`.  Source type is
`firstType`; dispatcher needs firstType.back + secondType.back.lift +
pairTerm IH (type `Ty.sigmaTy firstType secondType`).  Take
secondType.back.lift strengthening as extra hypothesis. -/
theorem isAggregatorTotal_fst_with_second {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {pairRaw : RawTerm sourceScope}
    {pairTerm : Term sourceCtx (Ty.sigmaTy firstType secondType) pairRaw}
    (pairTotal : IsAggregatorTotal pairTerm)
    (secondTypeTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetFirstType : Ty level targetScope},
        firstType.partialStrengthen? strengthening.back =
            some targetFirstType →
        ∃ targetSecondType,
          secondType.partialStrengthen? strengthening.back.lift =
            some targetSecondType) :
    IsAggregatorTotal (Term.fst pairTerm) := by
  intros _ _ strengthening targetFirstType _ typeStrengthens rawStrengthens
  dsimp only [RawTerm.partialStrengthen?, RawTerm.partialRename?] at rawStrengthens
  split at rawStrengthens
  rotate_left
  · cases rawStrengthens
  next targetPairRaw pairRawRenSuccess =>
    have pairRawSuccess :
        pairRaw.partialStrengthen? strengthening.back =
          some targetPairRaw := pairRawRenSuccess
    obtain ⟨targetSecondType, secondTypeSuccess⟩ :=
      secondTypeTotal strengthening typeStrengthens
    have sigmaTypeStrengthens :
        (Ty.sigmaTy firstType secondType).partialStrengthen?
            strengthening.back =
          some (Ty.sigmaTy targetFirstType targetSecondType) := by
      show Option.mapTwo
          (firstType.partialStrengthen? strengthening.back)
          (secondType.partialStrengthen? strengthening.back.lift)
          Ty.sigmaTy = _
      rw [typeStrengthens, secondTypeSuccess]
      rfl
    have pairTotalCall :=
      pairTotal strengthening sigmaTypeStrengthens pairRawSuccess
    dsimp only [partialStrengthenTyped?]
    split
    · next firstFails =>
        rw [typeStrengthens] at firstFails
        cases firstFails
    · next _ _ =>
        split
        · next secondFails =>
            rw [secondTypeSuccess] at secondFails
            cases secondFails
        · next _ _ =>
            split
            · next pairFails =>
                rw [pairFails] at pairTotalCall
                cases pairTotalCall
            · rfl

/-- Bridge totality wrapper for `Term.equivApp`.  Source type is
`carrierB`; dispatcher needs carrierA.back + carrierB.back +
equivTerm IH (Ty.equiv) + argumentTerm IH (carrierA).  Take
carrierA.back strengthening as extra hypothesis. -/
theorem isAggregatorTotal_equivApp_with_carrierA {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {carrierA carrierB : Ty level sourceScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    {equivTerm : Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term sourceCtx carrierA argumentRaw}
    (equivTotal : IsAggregatorTotal equivTerm)
    (argumentTotal : IsAggregatorTotal argumentTerm)
    (carrierATotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetCarrierB : Ty level targetScope},
        carrierB.partialStrengthen? strengthening.back =
            some targetCarrierB →
        ∃ targetCarrierA,
          carrierA.partialStrengthen? strengthening.back =
            some targetCarrierA) :
    IsAggregatorTotal (Term.equivApp equivTerm argumentTerm) := by
  intros _ _ strengthening targetCarrierB _ typeStrengthens rawStrengthens
  change Option.mapTwo
      (equivRaw.partialStrengthen? strengthening.back)
      (argumentRaw.partialStrengthen? strengthening.back)
      RawTerm.equivApp = some _ at rawStrengthens
  obtain ⟨_, _, equivRawSuccess, argumentRawSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  obtain ⟨targetCarrierA, carrierASuccess⟩ :=
    carrierATotal strengthening typeStrengthens
  have equivTypeStrengthens :
      (Ty.equiv carrierA carrierB).partialStrengthen?
          strengthening.back =
        some (Ty.equiv targetCarrierA targetCarrierB) := by
    show Option.mapTwo
        (carrierA.partialStrengthen? strengthening.back)
        (carrierB.partialStrengthen? strengthening.back)
        Ty.equiv = _
    rw [carrierASuccess, typeStrengthens]
    rfl
  have equivTotalCall :=
    equivTotal strengthening equivTypeStrengthens equivRawSuccess
  have argumentTotalCall :=
    argumentTotal strengthening carrierASuccess argumentRawSuccess
  dsimp only [partialStrengthenTyped?]
  split
  · next carrierAFails =>
      rw [carrierASuccess] at carrierAFails
      cases carrierAFails
  · next _ _ =>
      split
      · next carrierBFails =>
          rw [typeStrengthens] at carrierBFails
          cases carrierBFails
      · next _ _ =>
          split
          · next equivFails =>
              rw [equivFails] at equivTotalCall
              cases equivTotalCall
          · next _ _ =>
              split
              · next argumentFails =>
                  rw [argumentFails] at argumentTotalCall
                  cases argumentTotalCall
              · rfl

/-- Bridge totality wrapper for `Term.equivApply`.  Like equivApp but
the raw uses RawTerm.equivApply.  Same auxiliary witness pattern. -/
theorem isAggregatorTotal_equivApply_with_carrierA {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {carrierA carrierB : Ty level sourceScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    {equivTerm : Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term sourceCtx carrierA argumentRaw}
    (equivTotal : IsAggregatorTotal equivTerm)
    (argumentTotal : IsAggregatorTotal argumentTerm)
    (carrierATotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetCarrierB : Ty level targetScope},
        carrierB.partialStrengthen? strengthening.back =
            some targetCarrierB →
        ∃ targetCarrierA,
          carrierA.partialStrengthen? strengthening.back =
            some targetCarrierA) :
    IsAggregatorTotal (Term.equivApply equivTerm argumentTerm) := by
  intros _ _ strengthening targetCarrierB _ typeStrengthens rawStrengthens
  change Option.mapTwo
      (equivRaw.partialStrengthen? strengthening.back)
      (argumentRaw.partialStrengthen? strengthening.back)
      RawTerm.equivApply = some _ at rawStrengthens
  obtain ⟨_, _, equivRawSuccess, argumentRawSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  obtain ⟨targetCarrierA, carrierASuccess⟩ :=
    carrierATotal strengthening typeStrengthens
  have equivTypeStrengthens :
      (Ty.equiv carrierA carrierB).partialStrengthen?
          strengthening.back =
        some (Ty.equiv targetCarrierA targetCarrierB) := by
    show Option.mapTwo
        (carrierA.partialStrengthen? strengthening.back)
        (carrierB.partialStrengthen? strengthening.back)
        Ty.equiv = _
    rw [carrierASuccess, typeStrengthens]
    rfl
  have equivTotalCall :=
    equivTotal strengthening equivTypeStrengthens equivRawSuccess
  have argumentTotalCall :=
    argumentTotal strengthening carrierASuccess argumentRawSuccess
  dsimp only [partialStrengthenTyped?]
  split
  · next carrierAFails =>
      rw [carrierASuccess] at carrierAFails
      cases carrierAFails
  · next _ _ =>
      split
      · next carrierBFails =>
          rw [typeStrengthens] at carrierBFails
          cases carrierBFails
      · next _ _ =>
          split
          · next equivFails =>
              rw [equivFails] at equivTotalCall
              cases equivTotalCall
          · next _ _ =>
              split
              · next argumentFails =>
                  rw [argumentFails] at argumentTotalCall
                  cases argumentTotalCall
              · rfl

/-- Bridge totality wrapper for `Term.refineElim`.  Source type is
`baseType`; dispatcher needs baseType.back + predicate.back.lift +
refinedValue IH (type `Ty.refine baseType predicate`).  Take
predicate.back.lift strengthening as extra hypothesis. -/
theorem isAggregatorTotal_refineElim_with_predicate {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {baseType : Ty level sourceScope}
    {predicate : RawTerm (sourceScope + 1)}
    {refinedRaw : RawTerm sourceScope}
    {refinedValue :
      Term sourceCtx (Ty.refine baseType predicate) refinedRaw}
    (refinedTotal : IsAggregatorTotal refinedValue)
    (predicateTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetBaseType : Ty level targetScope},
        baseType.partialStrengthen? strengthening.back =
            some targetBaseType →
        ∃ targetPredicate,
          predicate.partialStrengthen? strengthening.back.lift =
            some targetPredicate) :
    IsAggregatorTotal (Term.refineElim refinedValue) := by
  intros _ _ strengthening targetBaseType _ typeStrengthens rawStrengthens
  dsimp only [RawTerm.partialStrengthen?, RawTerm.partialRename?] at rawStrengthens
  split at rawStrengthens
  rotate_left
  · cases rawStrengthens
  next targetRefinedRaw refinedRawRenSuccess =>
    have refinedRawSuccess :
        refinedRaw.partialStrengthen? strengthening.back =
          some targetRefinedRaw := refinedRawRenSuccess
    obtain ⟨targetPredicate, predicateSuccess⟩ :=
      predicateTotal strengthening typeStrengthens
    have refineTypeStrengthens :
        (Ty.refine baseType predicate).partialStrengthen?
            strengthening.back =
          some (Ty.refine targetBaseType targetPredicate) := by
      show Option.mapTwo
          (baseType.partialStrengthen? strengthening.back)
          (predicate.partialStrengthen? strengthening.back.lift)
          Ty.refine = _
      rw [typeStrengthens, predicateSuccess]
      rfl
    have refinedTotalCall :=
      refinedTotal strengthening refineTypeStrengthens refinedRawSuccess
    dsimp only [partialStrengthenTyped?]
    split
    · next baseFails =>
        rw [typeStrengthens] at baseFails
        cases baseFails
    · next _ _ =>
        split
        · next predicateFails =>
            rw [predicateSuccess] at predicateFails
            cases predicateFails
        · next _ _ =>
            split
            · next refinedFails =>
                rw [refinedFails] at refinedTotalCall
                cases refinedTotalCall
            · rfl

/-- Bridge totality wrapper for `Term.app`.  Source type is
`codomainType`; dispatcher needs domainType.back + codomainType.back +
functionTerm IH (Ty.arrow) + argumentTerm IH (domainType).  Take
domainType.back strengthening as extra hypothesis. -/
theorem isAggregatorTotal_app_with_domain {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {domainType codomainType : Ty level sourceScope}
    {functionRaw argumentRaw : RawTerm sourceScope}
    {functionTerm :
      Term sourceCtx (Ty.arrow domainType codomainType) functionRaw}
    {argumentTerm : Term sourceCtx domainType argumentRaw}
    (functionTotal : IsAggregatorTotal functionTerm)
    (argumentTotal : IsAggregatorTotal argumentTerm)
    (domainTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetCodomainType : Ty level targetScope},
        codomainType.partialStrengthen? strengthening.back =
            some targetCodomainType →
        ∃ targetDomainType,
          domainType.partialStrengthen? strengthening.back =
            some targetDomainType) :
    IsAggregatorTotal (Term.app functionTerm argumentTerm) := by
  intros _ _ strengthening targetCodomainType _ typeStrengthens rawStrengthens
  change Option.mapTwo
      (functionRaw.partialStrengthen? strengthening.back)
      (argumentRaw.partialStrengthen? strengthening.back)
      RawTerm.app = some _ at rawStrengthens
  obtain ⟨_, _, functionRawSuccess, argumentRawSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  obtain ⟨targetDomainType, domainSuccess⟩ :=
    domainTotal strengthening typeStrengthens
  have arrowTypeStrengthens :
      (Ty.arrow domainType codomainType).partialStrengthen?
          strengthening.back =
        some (Ty.arrow targetDomainType targetCodomainType) := by
    show Option.mapTwo
        (domainType.partialStrengthen? strengthening.back)
        (codomainType.partialStrengthen? strengthening.back)
        Ty.arrow = _
    rw [domainSuccess, typeStrengthens]
    rfl
  have functionTotalCall :=
    functionTotal strengthening arrowTypeStrengthens functionRawSuccess
  have argumentTotalCall :=
    argumentTotal strengthening domainSuccess argumentRawSuccess
  dsimp only [partialStrengthenTyped?]
  split
  · next domainFails =>
      rw [domainSuccess] at domainFails
      cases domainFails
  · next _ _ =>
      split
      · next codomainFails =>
          rw [typeStrengthens] at codomainFails
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

end Term

end LeanFX2
