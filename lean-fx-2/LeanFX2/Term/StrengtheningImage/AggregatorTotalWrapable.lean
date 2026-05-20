import LeanFX2.Term.StrengtheningImage.AggregatorTotalStructured

/-! # Term/StrengtheningImage/AggregatorTotalWrapable

Aggregator totality wrappers for constructors whose source type supplies enough visible payloads.
-/

namespace LeanFX2

namespace Term

/-! ## Wave Y1: wrap-able 0-IH/2-IH totality wrappers for ctors whose
    source type fully encodes the dispatcher's index witnesses.

    Each wrapper below decomposes `typeStrengthens` / `rawStrengthens`
    via Option.mapTwo / mapThree inversion plus `Ty.partialStrengthen?_weaken_lift`
    where the source type uses a lifted (binder) sub-Ty.  No additional
    auxiliary witnesses required — the predicate IsAggregatorTotal already
    encodes everything the dispatcher arm reads. -/

/-- 0-IH totality: `Term.funextRefl`.  Source type
`funextReflType domainType codomainType applyRaw = Ty.piTy domainType
(Ty.id codomainType.weaken applyRaw applyRaw)`.  Decompose typeStrengthens
via Ty.piTy mapTwo → domainStrengthens + (Ty.id ...).back.lift = some _.
The latter via Ty.id mapThree → codomainType.weaken.back.lift = some _ +
applyRaw.back.lift = some _ (twice).  Recover codomainStrengthens via
`Ty.partialStrengthen?_weaken_lift` (codomainType.weaken.back.lift =
codomainType.back |>.map weaken; map = some ⟹ inner = some).  Recover
applyRaw.back.lift from rawStrengthens (`RawTerm.lam (RawTerm.refl _)`)
or directly from typeStrengthens. -/
theorem isAggregatorTotal_funextRefl {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (domainType codomainType : Ty level sourceScope)
    (applyRaw : RawTerm (sourceScope + 1)) :
    IsAggregatorTotal (Term.funextRefl (context := sourceCtx)
      domainType codomainType applyRaw) := by
  intros _ _ strengthening _ _ typeStrengthens _
  -- typeStrengthens : (Ty.piTy domainType (Ty.id codomainType.weaken applyRaw applyRaw)).back = some _
  -- Decompose via Ty.piTy mapTwo
  change Option.mapTwo
      (domainType.partialStrengthen? strengthening.back)
      ((Ty.id codomainType.weaken applyRaw applyRaw).partialStrengthen?
        strengthening.back.lift)
      Ty.piTy = some _ at typeStrengthens
  obtain ⟨targetDomainType, targetIdBody, domainSuccess, idSuccess, _⟩ :=
    Option.mapTwo_eq_some typeStrengthens
  -- Decompose idSuccess via Ty.id mapThree
  change Option.mapThree
      (codomainType.weaken.partialStrengthen? strengthening.back.lift)
      (applyRaw.partialStrengthen? strengthening.back.lift)
      (applyRaw.partialStrengthen? strengthening.back.lift)
      Ty.id = some _ at idSuccess
  obtain ⟨targetCodomainWeaken, targetApplyRaw, _, codomainWeakenSuccess,
    applyRawSuccess, _, _⟩ :=
    Option.mapThree_eq_some idSuccess
  -- Recover codomainType.partialStrengthen? back = some _ via weaken_lift
  rw [Ty.partialStrengthen?_weaken_lift codomainType strengthening.back]
    at codomainWeakenSuccess
  obtain ⟨targetCodomainType, codomainSuccess, _⟩ :=
    Option.map_eq_some_inversion codomainWeakenSuccess
  -- Now discharge the dispatcher
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
          · next applyFails =>
              rw [applyRawSuccess] at applyFails
              cases applyFails
          · rfl

/-- 0-IH totality: `Term.funextReflAtId`.  Source type
`Ty.id (Ty.arrow domainType codomainType) (RawTerm.lam (RawTerm.refl applyRaw))
(RawTerm.lam (RawTerm.refl applyRaw))`.  Decompose typeStrengthens via
Ty.id mapThree → arrow.back + two lam-refl raw witnesses.  Ty.arrow.mapTwo
gives dom.back + codom.back.  Either lam-refl raw witness decomposes
to applyRaw.back.lift. -/
theorem isAggregatorTotal_funextReflAtId {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (domainType codomainType : Ty level sourceScope)
    (applyRaw : RawTerm (sourceScope + 1)) :
    IsAggregatorTotal (Term.funextReflAtId (context := sourceCtx)
      domainType codomainType applyRaw) := by
  intros _ _ strengthening _ _ typeStrengthens _
  -- Decompose typeStrengthens via Ty.id mapThree
  change Option.mapThree
      ((Ty.arrow domainType codomainType).partialStrengthen?
        strengthening.back)
      ((RawTerm.lam (RawTerm.refl applyRaw)).partialStrengthen?
        strengthening.back)
      ((RawTerm.lam (RawTerm.refl applyRaw)).partialStrengthen?
        strengthening.back)
      Ty.id = some _ at typeStrengthens
  obtain ⟨_, lamWitness, _, arrowSuccess, lamSuccess, _, _⟩ :=
    Option.mapThree_eq_some typeStrengthens
  -- Decompose arrowSuccess via Ty.arrow mapTwo
  change Option.mapTwo
      (domainType.partialStrengthen? strengthening.back)
      (codomainType.partialStrengthen? strengthening.back)
      Ty.arrow = some _ at arrowSuccess
  obtain ⟨_, _, domainSuccess, codomainSuccess, _⟩ :=
    Option.mapTwo_eq_some arrowSuccess
  -- Decompose lamSuccess (RawTerm.lam → RawTerm.refl → applyRaw at lift)
  unfold RawTerm.partialStrengthen? at lamSuccess
  unfold RawTerm.partialRename? at lamSuccess
  split at lamSuccess
  rotate_left
  · cases lamSuccess
  next reflWitness reflSuccess =>
    unfold RawTerm.partialRename? at reflSuccess
    split at reflSuccess
    rotate_left
    · cases reflSuccess
    next targetApplyRaw applyRawSuccess =>
      have applyStrengthenSuccess :
          applyRaw.partialStrengthen? strengthening.back.lift =
            some targetApplyRaw := applyRawSuccess
      -- Now discharge the dispatcher
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
              · next applyFails =>
                  rw [applyStrengthenSuccess] at applyFails
                  cases applyFails
              · rfl

/-- 2-IH totality: `Term.hcomp`.  Source type is the carrier `carrierType`
directly, and the dispatcher arm reads NO sub-Ty witnesses (only its
two IH children).  Both children share the carrier as their type, so
both IHs invoke with typeStrengthens directly.  Raw form
`RawTerm.hcomp sidesRaw capRaw` decomposes mapTwo. -/
theorem isAggregatorTotal_hcomp {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {sidesRaw capRaw : RawTerm sourceScope}
    {sidesValue : Term sourceCtx carrierType sidesRaw}
    {capValue : Term sourceCtx carrierType capRaw}
    (sidesTotal : IsAggregatorTotal sidesValue)
    (capTotal : IsAggregatorTotal capValue) :
    IsAggregatorTotal (Term.hcomp modeIsUnivalent sidesValue capValue) := by
  intros _ _ strengthening _ _ typeStrengthens rawStrengthens
  change Option.mapTwo
      (sidesRaw.partialStrengthen? strengthening.back)
      (capRaw.partialStrengthen? strengthening.back)
      RawTerm.hcomp = some _ at rawStrengthens
  obtain ⟨_, _, sidesRawSuccess, capRawSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  have sidesTotalCall :=
    sidesTotal strengthening typeStrengthens sidesRawSuccess
  have capTotalCall :=
    capTotal strengthening typeStrengthens capRawSuccess
  unfold partialStrengthenTyped?
  split
  · next sidesFails =>
      rw [sidesFails] at sidesTotalCall
      cases sidesTotalCall
  · next _ _ =>
      split
      · next capFails =>
          rw [capFails] at capTotalCall
          cases capTotalCall
      · rfl

/-- 1-IH totality: `Term.oeqFunext`.  Source type
`Ty.oeq (Ty.arrow domainType codomainType) leftFunctionRaw rightFunctionRaw`.
Dispatcher needs dom/codom/left/right.back + pointwiseProof IH.
pointwiseProof's type is `oeqFunextPointwiseType` (a piTy of dom with
oeq codom.weaken (app leftRaw.weaken (var 0)) (app rightRaw.weaken (var 0))
in body).  We synthesize the type strengthening via Ty.partialStrengthen?
unfolding + Ty.partialStrengthen?_weaken_lift +
RawTerm.partialStrengthen?_weaken_lift. -/
theorem isAggregatorTotal_oeqFunext {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (domainType codomainType : Ty level sourceScope)
    (leftFunctionRaw rightFunctionRaw : RawTerm sourceScope)
    {pointwiseRaw : RawTerm sourceScope}
    {pointwiseProof :
      Term sourceCtx
        (oeqFunextPointwiseType domainType codomainType
          leftFunctionRaw rightFunctionRaw)
        pointwiseRaw}
    (pointwiseTotal : IsAggregatorTotal pointwiseProof) :
    IsAggregatorTotal
      (Term.oeqFunext (context := sourceCtx) domainType codomainType
        leftFunctionRaw rightFunctionRaw pointwiseProof) := by
  intros _ _ strengthening _ _ typeStrengthens rawStrengthens
  -- typeStrengthens via Ty.oeq mapThree
  change Option.mapThree
      ((Ty.arrow domainType codomainType).partialStrengthen?
        strengthening.back)
      (leftFunctionRaw.partialStrengthen? strengthening.back)
      (rightFunctionRaw.partialStrengthen? strengthening.back)
      Ty.oeq = some _ at typeStrengthens
  obtain ⟨_, targetLeftFunctionRaw, targetRightFunctionRaw, arrowSuccess,
    leftSuccess', rightSuccess', _⟩ :=
    Option.mapThree_eq_some typeStrengthens
  -- arrowSuccess via Ty.arrow mapTwo
  change Option.mapTwo
      (domainType.partialStrengthen? strengthening.back)
      (codomainType.partialStrengthen? strengthening.back)
      Ty.arrow = some _ at arrowSuccess
  obtain ⟨targetDomainType, targetCodomainType, domainSuccess,
    codomainSuccess, _⟩ :=
    Option.mapTwo_eq_some arrowSuccess
  -- rawStrengthens : (RawTerm.oeqFunext pointwiseRaw).back = some _
  unfold RawTerm.partialStrengthen? at rawStrengthens
  unfold RawTerm.partialRename? at rawStrengthens
  split at rawStrengthens
  rotate_left
  · cases rawStrengthens
  next targetPointwiseRaw pointwiseRawSuccess =>
    have pointwiseStrengthenSuccess :
        pointwiseRaw.partialStrengthen? strengthening.back =
          some targetPointwiseRaw := pointwiseRawSuccess
    -- Construct pointwiseProof's type strengthening:
    -- oeqFunextPointwiseType.back = piTy of dom + oeq codom.weaken etc.
    have codomainWeakenStrengthens :
        codomainType.weaken.partialStrengthen? strengthening.back.lift =
          some targetCodomainType.weaken := by
      rw [Ty.partialStrengthen?_weaken_lift codomainType strengthening.back,
        codomainSuccess]
      rfl
    have leftWeakenStrengthens :
        leftFunctionRaw.weaken.partialStrengthen? strengthening.back.lift =
          some targetLeftFunctionRaw.weaken := by
      rw [RawTerm.partialStrengthen?_weaken_lift leftFunctionRaw
        strengthening.back, leftSuccess']
      rfl
    have rightWeakenStrengthens :
        rightFunctionRaw.weaken.partialStrengthen?
            strengthening.back.lift =
          some targetRightFunctionRaw.weaken := by
      rw [RawTerm.partialStrengthen?_weaken_lift rightFunctionRaw
        strengthening.back, rightSuccess']
      rfl
    have leftAppStrengthens :
        (RawTerm.app leftFunctionRaw.weaken
          (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩)
          ).partialStrengthen? strengthening.back.lift =
          some (RawTerm.app targetLeftFunctionRaw.weaken
            (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩)) := by
      change
        Option.mapTwo
          (leftFunctionRaw.weaken.partialStrengthen?
            strengthening.back.lift)
          (some (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩))
          RawTerm.app =
            some (RawTerm.app targetLeftFunctionRaw.weaken
              (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩))
      rw [leftWeakenStrengthens]
      rfl
    have rightAppStrengthens :
        (RawTerm.app rightFunctionRaw.weaken
          (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩)
          ).partialStrengthen? strengthening.back.lift =
          some (RawTerm.app targetRightFunctionRaw.weaken
            (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩)) := by
      change
        Option.mapTwo
          (rightFunctionRaw.weaken.partialStrengthen?
            strengthening.back.lift)
          (some (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩))
          RawTerm.app =
            some (RawTerm.app targetRightFunctionRaw.weaken
              (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩))
      rw [rightWeakenStrengthens]
      rfl
    have codomainBodyStrengthens :
        (oeqFunextPointwiseCodomain codomainType
            leftFunctionRaw rightFunctionRaw).partialStrengthen?
            strengthening.back.lift =
          some (oeqFunextPointwiseCodomain targetCodomainType
            targetLeftFunctionRaw targetRightFunctionRaw) := by
      change
        Option.mapThree
          (codomainType.weaken.partialStrengthen?
            strengthening.back.lift)
          ((RawTerm.app leftFunctionRaw.weaken
            (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩)
            ).partialStrengthen? strengthening.back.lift)
          ((RawTerm.app rightFunctionRaw.weaken
            (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩)
            ).partialStrengthen? strengthening.back.lift)
          Ty.oeq =
            some (oeqFunextPointwiseCodomain targetCodomainType
              targetLeftFunctionRaw targetRightFunctionRaw)
      rw [codomainWeakenStrengthens, leftAppStrengthens,
        rightAppStrengthens]
      rfl
    have pointwiseTypeStrengthens :
        (oeqFunextPointwiseType domainType codomainType
            leftFunctionRaw rightFunctionRaw).partialStrengthen?
            strengthening.back =
          some (oeqFunextPointwiseType targetDomainType targetCodomainType
            targetLeftFunctionRaw targetRightFunctionRaw) := by
      change
        Option.mapTwo
          (domainType.partialStrengthen? strengthening.back)
          ((oeqFunextPointwiseCodomain codomainType
              leftFunctionRaw rightFunctionRaw).partialStrengthen?
              strengthening.back.lift)
          Ty.piTy =
            some (oeqFunextPointwiseType targetDomainType
              targetCodomainType targetLeftFunctionRaw
              targetRightFunctionRaw)
      rw [domainSuccess, codomainBodyStrengthens]
      rfl
    have pointwiseTotalCall :=
      pointwiseTotal strengthening pointwiseTypeStrengthens
        pointwiseStrengthenSuccess
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
            · next leftFails =>
                rw [leftSuccess'] at leftFails
                cases leftFails
            · next _ _ =>
                split
                · next rightFails =>
                    rw [rightSuccess'] at rightFails
                    cases rightFails
                · next _ _ =>
                    split
                    · next pointwiseFails =>
                        rw [pointwiseFails] at pointwiseTotalCall
                        cases pointwiseTotalCall
                    · rfl

/-- 0-IH totality: `Term.funextIntroHet`.  Source type
`Ty.id (Ty.arrow domainType codomainType) (RawTerm.lam applyARaw)
(RawTerm.lam applyBRaw)`.  Decompose typeStrengthens via Ty.id mapThree
→ arrow.back + two lam raw witnesses.  Ty.arrow.mapTwo gives dom + codom.
Each lam-raw decomposes (via RawTerm.lam) to applyXRaw at .back.lift. -/
theorem isAggregatorTotal_funextIntroHet {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (domainType codomainType : Ty level sourceScope)
    (applyARaw applyBRaw : RawTerm (sourceScope + 1)) :
    IsAggregatorTotal (Term.funextIntroHet (context := sourceCtx)
      domainType codomainType applyARaw applyBRaw) := by
  intros _ _ strengthening _ _ typeStrengthens _
  -- Decompose typeStrengthens via Ty.id mapThree
  change Option.mapThree
      ((Ty.arrow domainType codomainType).partialStrengthen?
        strengthening.back)
      ((RawTerm.lam applyARaw).partialStrengthen?
        strengthening.back)
      ((RawTerm.lam applyBRaw).partialStrengthen?
        strengthening.back)
      Ty.id = some _ at typeStrengthens
  obtain ⟨_, _, _, arrowSuccess, lamAOk, lamBOk, _⟩ :=
    Option.mapThree_eq_some typeStrengthens
  -- Decompose arrowSuccess via Ty.arrow mapTwo
  change Option.mapTwo
      (domainType.partialStrengthen? strengthening.back)
      (codomainType.partialStrengthen? strengthening.back)
      Ty.arrow = some _ at arrowSuccess
  obtain ⟨_, _, domainSuccess, codomainSuccess, _⟩ :=
    Option.mapTwo_eq_some arrowSuccess
  -- Decompose lamAOk (RawTerm.lam → applyARaw at lift)
  unfold RawTerm.partialStrengthen? at lamAOk
  unfold RawTerm.partialRename? at lamAOk
  split at lamAOk
  rotate_left
  · cases lamAOk
  next targetApplyARaw applyARawRenSuccess =>
    have applyAStrengthenSuccess :
        applyARaw.partialStrengthen? strengthening.back.lift =
          some targetApplyARaw := applyARawRenSuccess
    -- Decompose lamBOk (RawTerm.lam → applyBRaw at lift)
    unfold RawTerm.partialStrengthen? at lamBOk
    unfold RawTerm.partialRename? at lamBOk
    split at lamBOk
    rotate_left
    · cases lamBOk
    next targetApplyBRaw applyBRawRenSuccess =>
      have applyBStrengthenSuccess :
          applyBRaw.partialStrengthen? strengthening.back.lift =
            some targetApplyBRaw := applyBRawRenSuccess
      -- Discharge the dispatcher
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
              · next applyAFails =>
                  rw [applyAStrengthenSuccess] at applyAFails
                  cases applyAFails
              · next _ _ =>
                  split
                  · next applyBFails =>
                      rw [applyBStrengthenSuccess] at applyBFails
                      cases applyBFails
                  · rfl

/-- 2-IH totality: `Term.glueIntro`.  Source type
`Ty.glue baseType boundaryWitness`; dispatcher needs baseType.back +
boundaryWitness.back + 2 IH children (baseValue, partialValue), both
typed at baseType.  typeStrengthens decomposes via Ty.glue mapTwo. -/
theorem isAggregatorTotal_glueIntro {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (modeIsUnivalent : mode = Mode.univalent)
    (baseType : Ty level sourceScope)
    (boundaryWitness : RawTerm sourceScope)
    {baseRaw partialRaw : RawTerm sourceScope}
    {baseValue : Term sourceCtx baseType baseRaw}
    {partialValue : Term sourceCtx baseType partialRaw}
    (baseTotal : IsAggregatorTotal baseValue)
    (partialTotal : IsAggregatorTotal partialValue) :
    IsAggregatorTotal
      (Term.glueIntro modeIsUnivalent baseType boundaryWitness
        baseValue partialValue) := by
  intros _ _ strengthening _ _ typeStrengthens rawStrengthens
  -- typeStrengthens : (Ty.glue baseType boundaryWitness).back = some _
  change Option.mapTwo
      (baseType.partialStrengthen? strengthening.back)
      (boundaryWitness.partialStrengthen? strengthening.back)
      Ty.glue = some _ at typeStrengthens
  obtain ⟨targetBaseType, _, baseTypeSuccess, boundarySuccess, _⟩ :=
    Option.mapTwo_eq_some typeStrengthens
  -- rawStrengthens : (RawTerm.glueIntro baseRaw partialRaw).back = some _
  change Option.mapTwo
      (baseRaw.partialStrengthen? strengthening.back)
      (partialRaw.partialStrengthen? strengthening.back)
      RawTerm.glueIntro = some _ at rawStrengthens
  obtain ⟨_, _, baseRawSuccess, partialRawSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  -- Both children's type IS baseType
  have baseTotalCall :=
    baseTotal strengthening baseTypeSuccess baseRawSuccess
  have partialTotalCall :=
    partialTotal strengthening baseTypeSuccess partialRawSuccess
  unfold partialStrengthenTyped?
  split
  · next baseTypeFails =>
      rw [baseTypeSuccess] at baseTypeFails
      cases baseTypeFails
  · next _ _ =>
      split
      · next boundaryFails =>
          rw [boundarySuccess] at boundaryFails
          cases boundaryFails
      · next _ _ =>
          split
          · next baseFails =>
              rw [baseFails] at baseTotalCall
              cases baseTotalCall
          · next _ _ =>
              split
              · next partialFails =>
                  rw [partialFails] at partialTotalCall
                  cases partialTotalCall
              · rfl

end Term

end LeanFX2
