import LeanFX2.Term.StrengtheningImage.AggregatorTotalCodesRefl

/-! # Term/StrengtheningImage/AggregatorTotalStructured

Aggregator totality wrappers for pair, equivalence reflexivity, refinement introduction, and codata unfold.
-/

namespace LeanFX2

namespace Term

/-! ## Wave T8: 2-IH pair totality (dependent Σ-intro).

`Term.pair firstValue secondValue` has source type
`Ty.sigmaTy firstType secondType`.  The first child's type is the
encodable `firstType`; the second child's type is the substituted
`secondType.subst0 firstType firstRaw` — reconstructed via
`Ty.partialStrengthen?_subst0_of_success` using strengthening's
forward/injectsBack/back_forward fields. -/

/-- 2-IH non-binder totality: `Term.pair`.  Combines firstType +
secondType.lift strengthens (from sigmaTy typeStrengthens) +
firstRaw / secondRaw strengthens (from pair rawStrengthens), applying
the subst0 reconstruction lemma to manufacture secondValue's IH input. -/
theorem isAggregatorTotal_pair {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {firstRaw secondRaw : RawTerm sourceScope}
    {firstValue : Term sourceCtx firstType firstRaw}
    {secondValue :
      Term sourceCtx (secondType.subst0 firstType firstRaw) secondRaw}
    (firstTotal : IsAggregatorTotal firstValue)
    (secondTotal : IsAggregatorTotal secondValue) :
    IsAggregatorTotal
      (Term.pair (firstValue := firstValue) (secondValue := secondValue)) := by
  intros _ _ strengthening _ _ typeStrengthens rawStrengthens
  obtain ⟨targetFirstType, targetSecondType, firstSuccess, secondLiftSuccess, _⟩ :=
    Option.mapTwo_eq_some typeStrengthens
  change Option.mapTwo
      (firstRaw.partialStrengthen? strengthening.back)
      (secondRaw.partialStrengthen? strengthening.back)
      RawTerm.pair = some _ at rawStrengthens
  obtain ⟨targetFirstRaw, targetSecondRaw, firstRawSuccess, secondRawSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  have firstTotalCall :=
    firstTotal strengthening firstSuccess firstRawSuccess
  -- Reconstruct secondType.subst0 strengthens via the subst0 lemma.
  have substStrengthens :
      (secondType.subst0 firstType firstRaw).partialStrengthen?
          strengthening.back =
        some (targetSecondType.subst0 targetFirstType targetFirstRaw) :=
    Ty.partialStrengthen?_subst0_of_success secondType targetSecondType
      firstType targetFirstType firstRaw targetFirstRaw
      strengthening.forward strengthening.back strengthening.injectsBack
      strengthening.back_forward secondLiftSuccess firstSuccess firstRawSuccess
  have secondTotalCall :=
    secondTotal strengthening substStrengthens secondRawSuccess
  dsimp only [partialStrengthenTyped?]
  split
  · next secondTypeFails =>
      rw [secondLiftSuccess] at secondTypeFails
      cases secondTypeFails
  · next _ _ =>
      split
      · next firstFails =>
          rw [firstFails] at firstTotalCall
          cases firstTotalCall
      · next _ _ =>
          split
          · next secondFails =>
              rw [secondFails] at secondTotalCall
              cases secondTotalCall
          · rfl

/-- 0-IH totality: `Term.equivReflId`.  Source type
`Ty.equiv carrier carrier` — single carrier component duplicated.
Dispatcher splits on carrier.strengthens which decomposes from
typeStrengthens mapTwo. -/
theorem isAggregatorTotal_equivReflId {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (carrier : Ty level sourceScope) :
    IsAggregatorTotal (Term.equivReflId (context := sourceCtx) carrier) := by
  intros _ _ strengthening _ _ typeStrengthens _
  obtain ⟨_, _, carrierSuccess, _, _⟩ :=
    Option.mapTwo_eq_some typeStrengthens
  dsimp only [partialStrengthenTyped?]
  split
  · next carrierFails =>
      rw [carrierSuccess] at carrierFails
      cases carrierFails
  · rfl

/-- 2-IH totality: `Term.refineIntro`.  Source type
`Ty.refine baseType predicate` — typeStrengthens decomposes via
mapTwo (baseType + predicate.lift).  predicateProof has type
`Ty.unit` (trivially strengthens). -/
theorem isAggregatorTotal_refineIntro {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {baseType : Ty level sourceScope}
    (predicate : RawTerm (sourceScope + 1))
    {valueRaw proofRaw : RawTerm sourceScope}
    {baseValue : Term sourceCtx baseType valueRaw}
    {predicateProof : Term sourceCtx Ty.unit proofRaw}
    (baseTotal : IsAggregatorTotal baseValue)
    (proofTotal : IsAggregatorTotal predicateProof) :
    IsAggregatorTotal
      (Term.refineIntro predicate baseValue predicateProof) := by
  intros _ _ strengthening _ _ typeStrengthens rawStrengthens
  obtain ⟨_, _, baseSuccess, predicateLiftSuccess, _⟩ :=
    Option.mapTwo_eq_some typeStrengthens
  change Option.mapTwo
      (valueRaw.partialStrengthen? strengthening.back)
      (proofRaw.partialStrengthen? strengthening.back)
      RawTerm.refineIntro = some _ at rawStrengthens
  obtain ⟨_, _, valueRawSuccess, proofRawSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  have baseTotalCall :=
    baseTotal strengthening baseSuccess valueRawSuccess
  have unitStrengthens :
      (Ty.unit : Ty level sourceScope).partialStrengthen?
          strengthening.back =
        some Ty.unit := rfl
  have proofTotalCall :=
    proofTotal strengthening unitStrengthens proofRawSuccess
  dsimp only [partialStrengthenTyped?]
  split
  · next predicateFails =>
      rw [predicateLiftSuccess] at predicateFails
      cases predicateFails
  · next _ _ =>
      split
      · next baseFails =>
          rw [baseFails] at baseTotalCall
          cases baseTotalCall
      · next _ _ =>
          split
          · next proofFails =>
              rw [proofFails] at proofTotalCall
              cases proofTotalCall
          · rfl

/-- 2-IH totality: `Term.codataUnfold`.  Source type
`Ty.codata stateType outputType` — typeStrengthens decomposes via
mapTwo (stateType + outputType).  initialState's type is stateType;
transition's type is `Ty.arrow stateType outputType` (built via
mapTwo). -/
theorem isAggregatorTotal_codataUnfold {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {stateType outputType : Ty level sourceScope}
    {stateRaw transitionRaw : RawTerm sourceScope}
    {initialState : Term sourceCtx stateType stateRaw}
    {transition : Term sourceCtx (Ty.arrow stateType outputType) transitionRaw}
    (stateTotal : IsAggregatorTotal initialState)
    (transitionTotal : IsAggregatorTotal transition) :
    IsAggregatorTotal
      (Term.codataUnfold (initialState := initialState) (transition := transition)) := by
  intros _ _ strengthening _ _ typeStrengthens rawStrengthens
  obtain ⟨targetStateType, targetOutputType, stateSuccess, outputSuccess, _⟩ :=
    Option.mapTwo_eq_some typeStrengthens
  change Option.mapTwo
      (stateRaw.partialStrengthen? strengthening.back)
      (transitionRaw.partialStrengthen? strengthening.back)
      RawTerm.codataUnfold = some _ at rawStrengthens
  obtain ⟨_, _, stateRawSuccess, transitionRawSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  have stateTotalCall :=
    stateTotal strengthening stateSuccess stateRawSuccess
  have arrowStrengthens :
      (Ty.arrow stateType outputType).partialStrengthen?
          strengthening.back =
        some (Ty.arrow targetStateType targetOutputType) := by
    show Option.mapTwo
        (stateType.partialStrengthen? strengthening.back)
        (outputType.partialStrengthen? strengthening.back)
        Ty.arrow = _
    rw [stateSuccess, outputSuccess]
    rfl
  have transitionTotalCall :=
    transitionTotal strengthening arrowStrengthens transitionRawSuccess
  dsimp only [partialStrengthenTyped?]
  split
  · next outputFails =>
      rw [outputSuccess] at outputFails
      cases outputFails
  · next _ _ =>
      split
      · next stateFails =>
          rw [stateFails] at stateTotalCall
          cases stateTotalCall
      · next _ _ =>
          split
          · next transitionFails =>
              rw [transitionFails] at transitionTotalCall
              cases transitionTotalCall
          · rfl

end Term

end LeanFX2
