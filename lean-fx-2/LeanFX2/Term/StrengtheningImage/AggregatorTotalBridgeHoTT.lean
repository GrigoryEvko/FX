import LeanFX2.Term.StrengtheningImage.AggregatorTotalBridgeShape

/-! # Term/StrengtheningImage/AggregatorTotalBridgeHoTT

Bridge totality wrappers for HoTT identity, strict identity, and univalence constructors.
-/

namespace LeanFX2

namespace Term

/-- Bridge totality wrapper for `Term.idJ`.  Source type is `motiveType`;
dispatcher needs carrier.back + leftEndpoint.back + rightEndpoint.back +
baseCase IH (motiveType) + witness IH (Ty.id carrier leftEndpoint
rightEndpoint).  Take the three Ty.id-component witnesses as extra
hypotheses. -/
theorem isAggregatorTotal_idJ_with_id_components {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw}
    (baseTotal : IsAggregatorTotal baseCase)
    (witnessTotal : IsAggregatorTotal witness)
    (idComponentsTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetMotiveType : Ty level targetScope},
        motiveType.partialStrengthen? strengthening.back =
            some targetMotiveType →
        ∃ targetCarrier targetLeftEndpoint targetRightEndpoint,
          carrier.partialStrengthen? strengthening.back =
              some targetCarrier ∧
          leftEndpoint.partialStrengthen? strengthening.back =
              some targetLeftEndpoint ∧
          rightEndpoint.partialStrengthen? strengthening.back =
              some targetRightEndpoint) :
    IsAggregatorTotal (Term.idJ baseCase witness) := by
  intros _ _ strengthening targetMotiveType _ typeStrengthens rawStrengthens
  change Option.mapTwo
      (baseRaw.partialStrengthen? strengthening.back)
      (witnessRaw.partialStrengthen? strengthening.back)
      RawTerm.idJ = some _ at rawStrengthens
  obtain ⟨_, _, baseRawSuccess, witnessRawSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  obtain ⟨targetCarrier, targetLeftEndpoint, targetRightEndpoint,
    carrierSuccess, leftSuccess, rightSuccess⟩ :=
    idComponentsTotal strengthening typeStrengthens
  have idTypeStrengthens :
      (Ty.id carrier leftEndpoint rightEndpoint).partialStrengthen?
          strengthening.back =
        some (Ty.id targetCarrier targetLeftEndpoint targetRightEndpoint) := by
    show Option.mapThree
        (carrier.partialStrengthen? strengthening.back)
        (leftEndpoint.partialStrengthen? strengthening.back)
        (rightEndpoint.partialStrengthen? strengthening.back)
        Ty.id = _
    rw [carrierSuccess, leftSuccess, rightSuccess]
    rfl
  have baseTotalCall :=
    baseTotal strengthening typeStrengthens baseRawSuccess
  have witnessTotalCall :=
    witnessTotal strengthening idTypeStrengthens witnessRawSuccess
  unfold partialStrengthenTyped?
  split
  · next carrierFails =>
      rw [carrierSuccess] at carrierFails
      cases carrierFails
  · next _ _ =>
      split
      · next leftFails =>
          rw [leftSuccess] at leftFails
          cases leftFails
      · next _ _ =>
          split
          · next rightFails =>
              rw [rightSuccess] at rightFails
              cases rightFails
          · next _ _ =>
              split
              · next baseFails =>
                  rw [baseFails] at baseTotalCall
                  cases baseTotalCall
              · next _ _ =>
                  split
                  · next witnessFails =>
                      rw [witnessFails] at witnessTotalCall
                      cases witnessTotalCall
                  · rfl

/-- Bridge totality wrapper for `Term.oeqJ`.  Same structure as idJ
but with Ty.oeq instead of Ty.id. -/
theorem isAggregatorTotal_oeqJ_with_oeq_components {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx (Ty.oeq carrier leftEndpoint rightEndpoint) witnessRaw}
    (baseTotal : IsAggregatorTotal baseCase)
    (witnessTotal : IsAggregatorTotal witness)
    (oeqComponentsTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetMotiveType : Ty level targetScope},
        motiveType.partialStrengthen? strengthening.back =
            some targetMotiveType →
        ∃ targetCarrier targetLeftEndpoint targetRightEndpoint,
          carrier.partialStrengthen? strengthening.back =
              some targetCarrier ∧
          leftEndpoint.partialStrengthen? strengthening.back =
              some targetLeftEndpoint ∧
          rightEndpoint.partialStrengthen? strengthening.back =
              some targetRightEndpoint) :
    IsAggregatorTotal (Term.oeqJ baseCase witness) := by
  intros _ _ strengthening targetMotiveType _ typeStrengthens rawStrengthens
  change Option.mapTwo
      (baseRaw.partialStrengthen? strengthening.back)
      (witnessRaw.partialStrengthen? strengthening.back)
      RawTerm.oeqJ = some _ at rawStrengthens
  obtain ⟨_, _, baseRawSuccess, witnessRawSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  obtain ⟨targetCarrier, targetLeftEndpoint, targetRightEndpoint,
    carrierSuccess, leftSuccess, rightSuccess⟩ :=
    oeqComponentsTotal strengthening typeStrengthens
  have oeqTypeStrengthens :
      (Ty.oeq carrier leftEndpoint rightEndpoint).partialStrengthen?
          strengthening.back =
        some (Ty.oeq targetCarrier targetLeftEndpoint targetRightEndpoint) := by
    show Option.mapThree
        (carrier.partialStrengthen? strengthening.back)
        (leftEndpoint.partialStrengthen? strengthening.back)
        (rightEndpoint.partialStrengthen? strengthening.back)
        Ty.oeq = _
    rw [carrierSuccess, leftSuccess, rightSuccess]
    rfl
  have baseTotalCall :=
    baseTotal strengthening typeStrengthens baseRawSuccess
  have witnessTotalCall :=
    witnessTotal strengthening oeqTypeStrengthens witnessRawSuccess
  unfold partialStrengthenTyped?
  split
  · next carrierFails =>
      rw [carrierSuccess] at carrierFails
      cases carrierFails
  · next _ _ =>
      split
      · next leftFails =>
          rw [leftSuccess] at leftFails
          cases leftFails
      · next _ _ =>
          split
          · next rightFails =>
              rw [rightSuccess] at rightFails
              cases rightFails
          · next _ _ =>
              split
              · next baseFails =>
                  rw [baseFails] at baseTotalCall
                  cases baseTotalCall
              · next _ _ =>
                  split
                  · next witnessFails =>
                      rw [witnessFails] at witnessTotalCall
                      cases witnessTotalCall
                  · rfl

/-- Bridge totality wrapper for `Term.idStrictRec`.  Source type is
`motiveType`; same structure as idJ/oeqJ with Ty.idStrict. -/
theorem isAggregatorTotal_idStrictRec_with_idStrict_components
    {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx (Ty.idStrict carrier leftEndpoint rightEndpoint)
        witnessRaw}
    (baseTotal : IsAggregatorTotal baseCase)
    (witnessTotal : IsAggregatorTotal witness)
    (idStrictComponentsTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetMotiveType : Ty level targetScope},
        motiveType.partialStrengthen? strengthening.back =
            some targetMotiveType →
        ∃ targetCarrier targetLeftEndpoint targetRightEndpoint,
          carrier.partialStrengthen? strengthening.back =
              some targetCarrier ∧
          leftEndpoint.partialStrengthen? strengthening.back =
              some targetLeftEndpoint ∧
          rightEndpoint.partialStrengthen? strengthening.back =
              some targetRightEndpoint) :
    IsAggregatorTotal
      (Term.idStrictRec modeIsStrict baseCase witness) := by
  intros _ _ strengthening targetMotiveType _ typeStrengthens rawStrengthens
  change Option.mapTwo
      (baseRaw.partialStrengthen? strengthening.back)
      (witnessRaw.partialStrengthen? strengthening.back)
      RawTerm.idStrictRec = some _ at rawStrengthens
  obtain ⟨_, _, baseRawSuccess, witnessRawSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  obtain ⟨targetCarrier, targetLeftEndpoint, targetRightEndpoint,
    carrierSuccess, leftSuccess, rightSuccess⟩ :=
    idStrictComponentsTotal strengthening typeStrengthens
  have idStrictTypeStrengthens :
      (Ty.idStrict carrier leftEndpoint rightEndpoint).partialStrengthen?
          strengthening.back =
        some (Ty.idStrict targetCarrier targetLeftEndpoint
          targetRightEndpoint) := by
    show Option.mapThree
        (carrier.partialStrengthen? strengthening.back)
        (leftEndpoint.partialStrengthen? strengthening.back)
        (rightEndpoint.partialStrengthen? strengthening.back)
        Ty.idStrict = _
    rw [carrierSuccess, leftSuccess, rightSuccess]
    rfl
  have baseTotalCall :=
    baseTotal strengthening typeStrengthens baseRawSuccess
  have witnessTotalCall :=
    witnessTotal strengthening idStrictTypeStrengthens witnessRawSuccess
  unfold partialStrengthenTyped?
  split
  · next carrierFails =>
      rw [carrierSuccess] at carrierFails
      cases carrierFails
  · next _ _ =>
      split
      · next leftFails =>
          rw [leftSuccess] at leftFails
          cases leftFails
      · next _ _ =>
          split
          · next rightFails =>
              rw [rightSuccess] at rightFails
              cases rightFails
          · next _ _ =>
              split
              · next baseFails =>
                  rw [baseFails] at baseTotalCall
                  cases baseTotalCall
              · next _ _ =>
                  split
                  · next witnessFails =>
                      rw [witnessFails] at witnessTotalCall
                      cases witnessTotalCall
                  · rfl

/-- Bridge totality wrapper for `Term.equivReflIdAtId`.  Source type
`Ty.id (Ty.universe innerLevel innerLevelLt) carrierRaw carrierRaw`
encodes carrierRaw but NOT carrier (Ty).  Take carrier.back as extra
hypothesis. -/
theorem isAggregatorTotal_equivReflIdAtId_with_carrier {mode : Mode}
    {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level sourceScope)
    (carrierRaw : RawTerm sourceScope)
    (carrierTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetCarrierRaw : RawTerm targetScope},
        carrierRaw.partialStrengthen? strengthening.back =
            some targetCarrierRaw →
        ∃ targetCarrier,
          carrier.partialStrengthen? strengthening.back =
            some targetCarrier) :
    IsAggregatorTotal
      (Term.equivReflIdAtId (context := sourceCtx) innerLevel innerLevelLt
        carrier carrierRaw) := by
  intros _ _ strengthening _ _ typeStrengthens _
  change Option.mapThree
      ((Ty.universe innerLevel innerLevelLt :
          Ty level sourceScope).partialStrengthen?
        strengthening.back)
      (carrierRaw.partialStrengthen? strengthening.back)
      (carrierRaw.partialStrengthen? strengthening.back)
      Ty.id = some _ at typeStrengthens
  obtain ⟨_, _, _, _, carrierRawSuccess, _, _⟩ :=
    Option.mapThree_eq_some typeStrengthens
  obtain ⟨_, carrierSuccess⟩ :=
    carrierTotal strengthening carrierRawSuccess
  unfold partialStrengthenTyped?
  split
  · next carrierFails =>
      rw [carrierSuccess] at carrierFails
      cases carrierFails
  · next _ _ =>
      split
      · next carrierRawFails =>
          rw [carrierRawSuccess] at carrierRawFails
          cases carrierRawFails
      · rfl

/-- Bridge totality wrapper for `Term.uaToEquiv`.  Source type
`Ty.equiv leftTy rightTy` encodes the carrier Ty's but the dispatcher
also reads leftTyRaw / rightTyRaw (positional schematic raw fields).
Take them as extra hypotheses. -/
theorem isAggregatorTotal_uaToEquiv_with_carrier_raws {mode : Mode}
    {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (leftTy rightTy : Ty level sourceScope)
    (leftTyRaw rightTyRaw : RawTerm sourceScope)
    {proofRaw : RawTerm sourceScope}
    {proof : Term sourceCtx
              (Ty.id (Ty.universe innerLevel innerLevelLt)
                     leftTyRaw rightTyRaw)
              proofRaw}
    (proofTotal : IsAggregatorTotal proof)
    (carrierRawsTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetLeftTy targetRightTy : Ty level targetScope},
        leftTy.partialStrengthen? strengthening.back =
            some targetLeftTy →
        rightTy.partialStrengthen? strengthening.back =
            some targetRightTy →
        ∃ targetLeftTyRaw targetRightTyRaw,
          leftTyRaw.partialStrengthen? strengthening.back =
              some targetLeftTyRaw ∧
          rightTyRaw.partialStrengthen? strengthening.back =
              some targetRightTyRaw) :
    IsAggregatorTotal
      (Term.uaToEquiv (context := sourceCtx) innerLevel innerLevelLt
        leftTy rightTy leftTyRaw rightTyRaw proof) := by
  intros _ _ strengthening _ _ typeStrengthens rawStrengthens
  change Option.mapTwo
      (leftTy.partialStrengthen? strengthening.back)
      (rightTy.partialStrengthen? strengthening.back)
      Ty.equiv = some _ at typeStrengthens
  obtain ⟨targetLeftTy, targetRightTy, leftTySuccess, rightTySuccess, _⟩ :=
    Option.mapTwo_eq_some typeStrengthens
  -- rawStrengthens: (RawTerm.uaToEquiv proofRaw).back
  unfold RawTerm.partialStrengthen? at rawStrengthens
  unfold RawTerm.partialRename? at rawStrengthens
  split at rawStrengthens
  rotate_left
  · cases rawStrengthens
  next targetProofRaw proofRawRenSuccess =>
    have proofRawSuccess :
        proofRaw.partialStrengthen? strengthening.back =
          some targetProofRaw := proofRawRenSuccess
    obtain ⟨targetLeftTyRaw, targetRightTyRaw, leftRawSuccess,
      rightRawSuccess⟩ :=
      carrierRawsTotal strengthening leftTySuccess rightTySuccess
    -- proof's type: Ty.id (Ty.universe ...) leftTyRaw rightTyRaw
    have universeStrengthens :
        (Ty.universe innerLevel innerLevelLt :
            Ty level sourceScope).partialStrengthen? strengthening.back =
          some (Ty.universe innerLevel innerLevelLt) := rfl
    have idTypeStrengthens :
        (Ty.id (Ty.universe innerLevel innerLevelLt) leftTyRaw rightTyRaw
          ).partialStrengthen? strengthening.back =
          some (Ty.id (Ty.universe innerLevel innerLevelLt) targetLeftTyRaw
            targetRightTyRaw) := by
      show Option.mapThree
          ((Ty.universe innerLevel innerLevelLt :
              Ty level sourceScope).partialStrengthen?
            strengthening.back)
          (leftTyRaw.partialStrengthen? strengthening.back)
          (rightTyRaw.partialStrengthen? strengthening.back)
          Ty.id = _
      rw [universeStrengthens, leftRawSuccess, rightRawSuccess]
      rfl
    have proofTotalCall :=
      proofTotal strengthening idTypeStrengthens proofRawSuccess
    unfold partialStrengthenTyped?
    split
    · next leftTyFails =>
        rw [leftTySuccess] at leftTyFails
        cases leftTyFails
    · next _ _ =>
        split
        · next rightTyFails =>
            rw [rightTySuccess] at rightTyFails
            cases rightTyFails
        · next _ _ =>
            split
            · next leftRawFails =>
                rw [leftRawSuccess] at leftRawFails
                cases leftRawFails
            · next _ _ =>
                split
                · next rightRawFails =>
                    rw [rightRawSuccess] at rightRawFails
                    cases rightRawFails
                · next _ _ =>
                    split
                    · next proofFails =>
                        rw [proofFails] at proofTotalCall
                        cases proofTotalCall
                    · rfl

/-- Bridge totality wrapper for `Term.uaIntroHet`.  Source type
`Ty.id (Ty.universe...) carrierARaw carrierBRaw` encodes carrierARaw/
carrierBRaw via Ty.id mapThree but NOT carrierA/carrierB (Ty's).
Source raw `RawTerm.equivIntro forwardRaw backwardRaw` gives forwardRaw,
backwardRaw via mapTwo.  Take carrierA.back + carrierB.back as
extra hypotheses. -/
theorem isAggregatorTotal_uaIntroHet_with_carriers {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    {carrierA carrierB : Ty level sourceScope}
    (carrierARaw carrierBRaw : RawTerm sourceScope)
    {forwardRaw backwardRaw : RawTerm sourceScope}
    {equivWitness :
      Term sourceCtx (Ty.equiv carrierA carrierB)
        (RawTerm.equivIntro forwardRaw backwardRaw)}
    (equivTotal : IsAggregatorTotal equivWitness)
    (carrierTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetCarrierARaw targetCarrierBRaw : RawTerm targetScope},
        carrierARaw.partialStrengthen? strengthening.back =
            some targetCarrierARaw →
        carrierBRaw.partialStrengthen? strengthening.back =
            some targetCarrierBRaw →
        ∃ targetCarrierA targetCarrierB,
          carrierA.partialStrengthen? strengthening.back =
              some targetCarrierA ∧
          carrierB.partialStrengthen? strengthening.back =
              some targetCarrierB) :
    IsAggregatorTotal
      (Term.uaIntroHet (context := sourceCtx) innerLevel innerLevelLt
        carrierARaw carrierBRaw equivWitness) := by
  intros _ _ strengthening _ _ typeStrengthens rawStrengthens
  -- typeStrengthens: Ty.id (Ty.universe ...) carrierARaw carrierBRaw
  change Option.mapThree
      ((Ty.universe innerLevel innerLevelLt :
          Ty level sourceScope).partialStrengthen?
        strengthening.back)
      (carrierARaw.partialStrengthen? strengthening.back)
      (carrierBRaw.partialStrengthen? strengthening.back)
      Ty.id = some _ at typeStrengthens
  obtain ⟨_, _, _, _, carrierARawSuccess, carrierBRawSuccess, _⟩ :=
    Option.mapThree_eq_some typeStrengthens
  -- rawStrengthens: RawTerm.equivIntro forwardRaw backwardRaw
  change Option.mapTwo
      (forwardRaw.partialStrengthen? strengthening.back)
      (backwardRaw.partialStrengthen? strengthening.back)
      RawTerm.equivIntro = some _ at rawStrengthens
  obtain ⟨targetForwardRaw, targetBackwardRaw, forwardRawSuccess,
    backwardRawSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  obtain ⟨targetCarrierA, targetCarrierB, carrierASuccess,
    carrierBSuccess⟩ :=
    carrierTotal strengthening carrierARawSuccess carrierBRawSuccess
  -- equivWitness's type: Ty.equiv carrierA carrierB
  have equivTypeStrengthens :
      (Ty.equiv carrierA carrierB).partialStrengthen?
          strengthening.back =
        some (Ty.equiv targetCarrierA targetCarrierB) := by
    show Option.mapTwo
        (carrierA.partialStrengthen? strengthening.back)
        (carrierB.partialStrengthen? strengthening.back)
        Ty.equiv = _
    rw [carrierASuccess, carrierBSuccess]
    rfl
  -- equivWitness's raw: RawTerm.equivIntro forwardRaw backwardRaw
  have equivRawStrengthens :
      (RawTerm.equivIntro forwardRaw backwardRaw).partialStrengthen?
          strengthening.back =
        some (RawTerm.equivIntro targetForwardRaw targetBackwardRaw) := by
    change Option.mapTwo
        (forwardRaw.partialStrengthen? strengthening.back)
        (backwardRaw.partialStrengthen? strengthening.back)
        RawTerm.equivIntro = _
    rw [forwardRawSuccess, backwardRawSuccess]
    rfl
  have equivTotalCall :=
    equivTotal strengthening equivTypeStrengthens equivRawStrengthens
  unfold partialStrengthenTyped?
  split
  · next carrierAFails =>
      rw [carrierASuccess] at carrierAFails
      cases carrierAFails
  · next _ _ =>
      split
      · next carrierBFails =>
          rw [carrierBSuccess] at carrierBFails
          cases carrierBFails
      · next _ _ =>
          split
          · next carrierARawFails =>
              rw [carrierARawSuccess] at carrierARawFails
              cases carrierARawFails
          · next _ _ =>
              split
              · next carrierBRawFails =>
                  rw [carrierBRawSuccess] at carrierBRawFails
                  cases carrierBRawFails
              · next _ _ =>
                  split
                  · next forwardRawFails =>
                      rw [forwardRawSuccess] at forwardRawFails
                      cases forwardRawFails
                  · next _ _ =>
                      split
                      · next backwardRawFails =>
                          rw [backwardRawSuccess] at backwardRawFails
                          cases backwardRawFails
                      · next _ _ =>
                          split
                          · next equivFails =>
                              rw [equivFails] at equivTotalCall
                              cases equivTotalCall
                          · rfl

end Term

end LeanFX2
