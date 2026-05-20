import LeanFX2.Term.StrengtheningImage.Core

/-! # Term/StrengtheningImage/HoTTElimSuccess

Soundness lemmas for HoTT/equivalence success producers and observational funext.
-/

namespace LeanFX2

namespace Term

/-- Soundness for cubical Glue introduction.  Direct producer: both
sub-Term children share the same `baseType` (pre-witnessed by
`baseTypeStrengthens`).  Mirrors the producer's two-cases chain
(`cases baseResult; rw + cases; cases partialResult; rw + cases`) and
applies `glueIntro_HEq_congr` with the two pre-witnessed renames plus
the sub-Terms' soundness HEqs. -/
theorem partialStrengthenTypedGlueIntro_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (modeIsUnivalent : mode = Mode.univalent)
    (baseType : Ty level sourceScope)
    (targetBaseType : Ty level targetScope)
    (boundaryWitness : RawTerm sourceScope)
    (targetBoundaryWitness : RawTerm targetScope)
    {baseRaw partialRaw : RawTerm sourceScope}
    {baseValue : Term sourceCtx baseType baseRaw}
    {partialValue : Term sourceCtx baseType partialRaw}
    (baseTypeStrengthens :
      baseType.partialStrengthen? strengthening.back = some targetBaseType)
    (boundaryStrengthens :
      boundaryWitness.partialStrengthen? strengthening.back =
        some targetBoundaryWitness)
    {baseResult : StrengtheningResult strengthening baseValue}
    {partialResult : StrengtheningResult strengthening partialValue}
    (baseSound : StrengtheningSoundness baseResult)
    (partialSound : StrengtheningSoundness partialResult) :
    StrengtheningSoundness
      (partialStrengthenTypedGlueIntro modeIsUnivalent baseType
        targetBaseType boundaryWitness targetBoundaryWitness
        baseTypeStrengthens boundaryStrengthens baseResult partialResult) := by
  cases baseResult with
  | mk targetBaseValueType targetBaseRaw targetBaseValue
      baseValueTypeStrengthens baseRawStrengthens baseValueTypeRenames
      baseRawRenames =>
      rw [baseTypeStrengthens] at baseValueTypeStrengthens
      cases baseValueTypeStrengthens
      cases partialResult with
      | mk targetPartialValueType targetPartialRaw targetPartialValue
          partialValueTypeStrengthens partialRawStrengthens
          partialValueTypeRenames partialRawRenames =>
          rw [baseTypeStrengthens] at partialValueTypeStrengthens
          cases partialValueTypeStrengthens
          refine ⟨?_⟩
          dsimp [partialStrengthenTypedGlueIntro,
              StrengtheningResult.renamedTarget]
            at baseSound partialSound ⊢
          have baseRenames :
              baseType = targetBaseType.rename strengthening.forward :=
            Ty.partialStrengthen?_imp_rename baseType
              strengthening.forward strengthening.back
              strengthening.injectsBack targetBaseType baseTypeStrengthens
          have boundaryRenames :
              boundaryWitness =
                targetBoundaryWitness.rename strengthening.forward :=
            RawTerm.partialStrengthen?_imp_rename boundaryWitness
              strengthening.forward strengthening.back
              strengthening.injectsBack targetBoundaryWitness
              boundaryStrengthens
          exact Term.glueIntro_HEq_congr modeIsUnivalent baseRenames
            boundaryRenames baseRawRenames partialRawRenames
            baseSound.termRenames partialSound.termRenames

/-- Soundness for observational funext.  Bridges the rename-distribution
cast on `oeqFunextPointwiseType` via the published commutation lemma
`oeqFunextPointwiseType_rename`, which `Term.rename` itself uses with an
explicit `▸` cast in the `oeqFunext` arm.  The HEq congruence's
expected `pointwiseProof2` parameter therefore arrives in the cast
shape `typeEq ▸ Term.rename ... targetPointwiseProof`, and we bridge
`pointwiseSound.termRenames` to that shape via
`Term.type_eq_cast_heq` + `HEq.trans` + `HEq.symm`. -/
theorem partialStrengthenTypedOeqFunext_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (domainType codomainType : Ty level sourceScope)
    (targetDomainType targetCodomainType : Ty level targetScope)
    (leftFunctionRaw rightFunctionRaw : RawTerm sourceScope)
    (targetLeftFunctionRaw targetRightFunctionRaw : RawTerm targetScope)
    {pointwiseRaw : RawTerm sourceScope}
    {pointwiseProof :
      Term sourceCtx
        (oeqFunextPointwiseType domainType codomainType
          leftFunctionRaw rightFunctionRaw)
        pointwiseRaw}
    (domainStrengthens :
      domainType.partialStrengthen? strengthening.back =
        some targetDomainType)
    (codomainStrengthens :
      codomainType.partialStrengthen? strengthening.back =
        some targetCodomainType)
    (leftFunctionStrengthens :
      leftFunctionRaw.partialStrengthen? strengthening.back =
        some targetLeftFunctionRaw)
    (rightFunctionStrengthens :
      rightFunctionRaw.partialStrengthen? strengthening.back =
        some targetRightFunctionRaw)
    {pointwiseResult : StrengtheningResult strengthening pointwiseProof}
    (pointwiseSound : StrengtheningSoundness pointwiseResult) :
    StrengtheningSoundness
      (partialStrengthenTypedOeqFunext domainType codomainType
        targetDomainType targetCodomainType leftFunctionRaw rightFunctionRaw
        targetLeftFunctionRaw targetRightFunctionRaw domainStrengthens
        codomainStrengthens leftFunctionStrengthens rightFunctionStrengthens
        pointwiseResult) := by
  cases pointwiseResult with
  | mk targetPointwiseType targetPointwiseRaw targetPointwiseProof
      pointwiseTypeStrengthens pointwiseRawStrengthens
      pointwiseTypeRenames pointwiseRawRenames =>
      have codomainWeakenStrengthens :
          codomainType.weaken.partialStrengthen? strengthening.back.lift =
            some targetCodomainType.weaken := by
        rw [Ty.partialStrengthen?_weaken_lift codomainType
          strengthening.back, codomainStrengthens]
        rfl
      have leftWeakenStrengthens :
          leftFunctionRaw.weaken.partialStrengthen?
              strengthening.back.lift =
            some targetLeftFunctionRaw.weaken := by
        rw [RawTerm.partialStrengthen?_weaken_lift leftFunctionRaw
          strengthening.back, leftFunctionStrengthens]
        rfl
      have rightWeakenStrengthens :
          rightFunctionRaw.weaken.partialStrengthen?
              strengthening.back.lift =
            some targetRightFunctionRaw.weaken := by
        rw [RawTerm.partialStrengthen?_weaken_lift rightFunctionRaw
          strengthening.back, rightFunctionStrengthens]
        rfl
      have pointwiseExpectedStrengthens :
          (oeqFunextPointwiseType domainType codomainType
              leftFunctionRaw rightFunctionRaw).partialStrengthen?
              strengthening.back =
            some (oeqFunextPointwiseType targetDomainType targetCodomainType
              targetLeftFunctionRaw targetRightFunctionRaw) := by
        have codomainBodyStrengthens :
            (oeqFunextPointwiseCodomain codomainType
                leftFunctionRaw rightFunctionRaw).partialStrengthen?
                strengthening.back.lift =
              some (oeqFunextPointwiseCodomain targetCodomainType
                targetLeftFunctionRaw targetRightFunctionRaw) := by
          have leftAppStrengthens :
              (RawTerm.app leftFunctionRaw.weaken
                (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩)
                ).partialStrengthen? strengthening.back.lift =
                some (RawTerm.app targetLeftFunctionRaw.weaken
                  (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩)) := by
            change
              Option.mapTwo
                (leftFunctionRaw.weaken.partialStrengthen?
                  strengthening.back.lift)
                (some (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩))
                RawTerm.app =
                  some (RawTerm.app targetLeftFunctionRaw.weaken
                    (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩))
            rw [leftWeakenStrengthens]
            rfl
          have rightAppStrengthens :
              (RawTerm.app rightFunctionRaw.weaken
                (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩)
                ).partialStrengthen? strengthening.back.lift =
                some (RawTerm.app targetRightFunctionRaw.weaken
                  (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩)) := by
            change
              Option.mapTwo
                (rightFunctionRaw.weaken.partialStrengthen?
                  strengthening.back.lift)
                (some (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩))
                RawTerm.app =
                  some (RawTerm.app targetRightFunctionRaw.weaken
                    (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩))
            rw [rightWeakenStrengthens]
            rfl
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
        rw [domainStrengthens, codomainBodyStrengthens]
        rfl
      rw [pointwiseExpectedStrengthens] at pointwiseTypeStrengthens
      cases pointwiseTypeStrengthens
      refine ⟨?_⟩
      dsimp [partialStrengthenTypedOeqFunext,
          StrengtheningResult.renamedTarget] at pointwiseSound ⊢
      have domainRenames :
          domainType = targetDomainType.rename strengthening.forward :=
        Ty.partialStrengthen?_imp_rename domainType
          strengthening.forward strengthening.back strengthening.injectsBack
          targetDomainType domainStrengthens
      have codomainRenames :
          codomainType = targetCodomainType.rename strengthening.forward :=
        Ty.partialStrengthen?_imp_rename codomainType
          strengthening.forward strengthening.back strengthening.injectsBack
          targetCodomainType codomainStrengthens
      have leftFunctionRenames :
          leftFunctionRaw =
            targetLeftFunctionRaw.rename strengthening.forward :=
        RawTerm.partialStrengthen?_imp_rename leftFunctionRaw
          strengthening.forward strengthening.back strengthening.injectsBack
          targetLeftFunctionRaw leftFunctionStrengthens
      have rightFunctionRenames :
          rightFunctionRaw =
            targetRightFunctionRaw.rename strengthening.forward :=
        RawTerm.partialStrengthen?_imp_rename rightFunctionRaw
          strengthening.forward strengthening.back strengthening.injectsBack
          targetRightFunctionRaw rightFunctionStrengthens
      have typeEq :
          (oeqFunextPointwiseType targetDomainType targetCodomainType
              targetLeftFunctionRaw targetRightFunctionRaw).rename
              strengthening.forward =
            oeqFunextPointwiseType
              (targetDomainType.rename strengthening.forward)
              (targetCodomainType.rename strengthening.forward)
              (targetLeftFunctionRaw.rename strengthening.forward)
              (targetRightFunctionRaw.rename strengthening.forward) :=
        oeqFunextPointwiseType_rename strengthening.forward
          targetDomainType targetCodomainType targetLeftFunctionRaw
          targetRightFunctionRaw
      have castedHEq :
          HEq
            (Term.rename strengthening.toTermRenaming targetPointwiseProof)
            (typeEq ▸
              Term.rename strengthening.toTermRenaming targetPointwiseProof) :=
        HEq.symm
          (Term.type_eq_cast_heq typeEq
            (Term.rename strengthening.toTermRenaming targetPointwiseProof))
      have pointwiseHEq :
          HEq pointwiseProof
            (typeEq ▸
              Term.rename strengthening.toTermRenaming targetPointwiseProof) :=
        HEq.trans pointwiseSound.termRenames castedHEq
      exact Term.oeqFunext_HEq_congr domainRenames codomainRenames
        leftFunctionRenames rightFunctionRenames pointwiseRawRenames
        pointwiseHEq

/-- Soundness for the success branch of identity-elimination
strengthening.  The producer's success-arm record is what `dsimp`
unfolds — the wrapper's `cases` cascade on the witness's `Ty.id`
parameters is left unsounded by design (the OfSuccess pattern from
RefineElim/RecordProj/CodataDest/etc.).  `Ty.id` is a Ty constructor
so `Ty.rename` distributes definitionally, no cast bridge needed. -/
theorem partialStrengthenTypedIdJOfSuccess_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {targetMotiveType : Ty level targetScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {targetBaseRaw targetWitnessRaw : RawTerm targetScope}
    {targetCarrier : Ty level targetScope}
    {targetLeftEndpoint targetRightEndpoint : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw}
    {targetBaseTerm : Term targetCtx targetMotiveType targetBaseRaw}
    {targetWitnessTerm :
      Term targetCtx
        (Ty.id targetCarrier targetLeftEndpoint targetRightEndpoint)
        targetWitnessRaw}
    (baseTypeStrengthens :
      motiveType.partialStrengthen? strengthening.back =
        some targetMotiveType)
    (carrierSuccess :
      carrier.partialStrengthen? strengthening.back = some targetCarrier)
    (leftSuccess :
      leftEndpoint.partialStrengthen? strengthening.back =
        some targetLeftEndpoint)
    (rightSuccess :
      rightEndpoint.partialStrengthen? strengthening.back =
        some targetRightEndpoint)
    (baseRawStrengthens :
      baseRaw.partialStrengthen? strengthening.back = some targetBaseRaw)
    (witnessRawStrengthens :
      witnessRaw.partialStrengthen? strengthening.back =
        some targetWitnessRaw)
    (baseTypeRenames :
      motiveType = targetMotiveType.rename strengthening.forward)
    (baseRawRenames : baseRaw = targetBaseRaw.rename strengthening.forward)
    (witnessRawRenames :
      witnessRaw = targetWitnessRaw.rename strengthening.forward)
    (baseSound :
      HEq baseCase
        (Term.rename strengthening.toTermRenaming targetBaseTerm))
    (witnessSound :
      HEq witness
        (Term.rename strengthening.toTermRenaming targetWitnessTerm)) :
    StrengtheningSoundness
      (partialStrengthenTypedIdJOfSuccess
        (baseCase := baseCase) (witness := witness)
        targetBaseTerm targetWitnessTerm baseTypeStrengthens
        carrierSuccess leftSuccess rightSuccess baseRawStrengthens
        witnessRawStrengthens baseTypeRenames baseRawRenames
        witnessRawRenames) := by
  refine ⟨?_⟩
  unfold StrengtheningResult.renamedTarget
  dsimp [partialStrengthenTypedIdJOfSuccess]
  have carrierRenames :
      carrier = targetCarrier.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename carrier
      strengthening.forward strengthening.back strengthening.injectsBack
      targetCarrier carrierSuccess
  have leftRenames :
      leftEndpoint = targetLeftEndpoint.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename leftEndpoint
      strengthening.forward strengthening.back strengthening.injectsBack
      targetLeftEndpoint leftSuccess
  have rightRenames :
      rightEndpoint = targetRightEndpoint.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename rightEndpoint
      strengthening.forward strengthening.back strengthening.injectsBack
      targetRightEndpoint rightSuccess
  exact Term.idJ_HEq_congr carrierRenames leftRenames rightRenames
    baseTypeRenames baseRawRenames witnessRawRenames baseSound witnessSound

/-- Soundness for the success branch of observational-equality
elimination strengthening.  Mirrors `partialStrengthenTypedIdJOfSuccess_sound`
with `Ty.oeq` in place of `Ty.id`. -/
theorem partialStrengthenTypedOeqJOfSuccess_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {targetMotiveType : Ty level targetScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {targetBaseRaw targetWitnessRaw : RawTerm targetScope}
    {targetCarrier : Ty level targetScope}
    {targetLeftEndpoint targetRightEndpoint : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx (Ty.oeq carrier leftEndpoint rightEndpoint) witnessRaw}
    {targetBaseTerm : Term targetCtx targetMotiveType targetBaseRaw}
    {targetWitnessTerm :
      Term targetCtx
        (Ty.oeq targetCarrier targetLeftEndpoint targetRightEndpoint)
        targetWitnessRaw}
    (baseTypeStrengthens :
      motiveType.partialStrengthen? strengthening.back =
        some targetMotiveType)
    (carrierSuccess :
      carrier.partialStrengthen? strengthening.back = some targetCarrier)
    (leftSuccess :
      leftEndpoint.partialStrengthen? strengthening.back =
        some targetLeftEndpoint)
    (rightSuccess :
      rightEndpoint.partialStrengthen? strengthening.back =
        some targetRightEndpoint)
    (baseRawStrengthens :
      baseRaw.partialStrengthen? strengthening.back = some targetBaseRaw)
    (witnessRawStrengthens :
      witnessRaw.partialStrengthen? strengthening.back =
        some targetWitnessRaw)
    (baseTypeRenames :
      motiveType = targetMotiveType.rename strengthening.forward)
    (baseRawRenames : baseRaw = targetBaseRaw.rename strengthening.forward)
    (witnessRawRenames :
      witnessRaw = targetWitnessRaw.rename strengthening.forward)
    (baseSound :
      HEq baseCase
        (Term.rename strengthening.toTermRenaming targetBaseTerm))
    (witnessSound :
      HEq witness
        (Term.rename strengthening.toTermRenaming targetWitnessTerm)) :
    StrengtheningSoundness
      (partialStrengthenTypedOeqJOfSuccess
        (baseCase := baseCase) (witness := witness)
        targetBaseTerm targetWitnessTerm baseTypeStrengthens
        carrierSuccess leftSuccess rightSuccess baseRawStrengthens
        witnessRawStrengthens baseTypeRenames baseRawRenames
        witnessRawRenames) := by
  refine ⟨?_⟩
  unfold StrengtheningResult.renamedTarget
  dsimp [partialStrengthenTypedOeqJOfSuccess]
  have carrierRenames :
      carrier = targetCarrier.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename carrier
      strengthening.forward strengthening.back strengthening.injectsBack
      targetCarrier carrierSuccess
  have leftRenames :
      leftEndpoint = targetLeftEndpoint.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename leftEndpoint
      strengthening.forward strengthening.back strengthening.injectsBack
      targetLeftEndpoint leftSuccess
  have rightRenames :
      rightEndpoint = targetRightEndpoint.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename rightEndpoint
      strengthening.forward strengthening.back strengthening.injectsBack
      targetRightEndpoint rightSuccess
  exact Term.oeqJ_HEq_congr carrierRenames leftRenames rightRenames
    baseTypeRenames baseRawRenames witnessRawRenames baseSound witnessSound

/-- Soundness for the success branch of strict-identity-recursor
strengthening.  Mirrors `partialStrengthenTypedIdJOfSuccess_sound`
with `Ty.idStrict` and the `modeIsStrict` evidence. -/
theorem partialStrengthenTypedIdStrictRecOfSuccess_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {targetMotiveType : Ty level targetScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {targetBaseRaw targetWitnessRaw : RawTerm targetScope}
    {targetCarrier : Ty level targetScope}
    {targetLeftEndpoint targetRightEndpoint : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx
        (Ty.idStrict carrier leftEndpoint rightEndpoint) witnessRaw}
    {targetBaseTerm : Term targetCtx targetMotiveType targetBaseRaw}
    {targetWitnessTerm :
      Term targetCtx
        (Ty.idStrict targetCarrier targetLeftEndpoint targetRightEndpoint)
        targetWitnessRaw}
    (baseTypeStrengthens :
      motiveType.partialStrengthen? strengthening.back =
        some targetMotiveType)
    (carrierSuccess :
      carrier.partialStrengthen? strengthening.back = some targetCarrier)
    (leftSuccess :
      leftEndpoint.partialStrengthen? strengthening.back =
        some targetLeftEndpoint)
    (rightSuccess :
      rightEndpoint.partialStrengthen? strengthening.back =
        some targetRightEndpoint)
    (baseRawStrengthens :
      baseRaw.partialStrengthen? strengthening.back = some targetBaseRaw)
    (witnessRawStrengthens :
      witnessRaw.partialStrengthen? strengthening.back =
        some targetWitnessRaw)
    (baseTypeRenames :
      motiveType = targetMotiveType.rename strengthening.forward)
    (baseRawRenames : baseRaw = targetBaseRaw.rename strengthening.forward)
    (witnessRawRenames :
      witnessRaw = targetWitnessRaw.rename strengthening.forward)
    (baseSound :
      HEq baseCase
        (Term.rename strengthening.toTermRenaming targetBaseTerm))
    (witnessSound :
      HEq witness
        (Term.rename strengthening.toTermRenaming targetWitnessTerm)) :
    StrengtheningSoundness
      (partialStrengthenTypedIdStrictRecOfSuccess modeIsStrict
        (baseCase := baseCase) (witness := witness)
        targetBaseTerm targetWitnessTerm baseTypeStrengthens
        carrierSuccess leftSuccess rightSuccess baseRawStrengthens
        witnessRawStrengthens baseTypeRenames baseRawRenames
        witnessRawRenames) := by
  refine ⟨?_⟩
  unfold StrengtheningResult.renamedTarget
  dsimp [partialStrengthenTypedIdStrictRecOfSuccess]
  have carrierRenames :
      carrier = targetCarrier.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename carrier
      strengthening.forward strengthening.back strengthening.injectsBack
      targetCarrier carrierSuccess
  have leftRenames :
      leftEndpoint = targetLeftEndpoint.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename leftEndpoint
      strengthening.forward strengthening.back strengthening.injectsBack
      targetLeftEndpoint leftSuccess
  have rightRenames :
      rightEndpoint = targetRightEndpoint.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename rightEndpoint
      strengthening.forward strengthening.back strengthening.injectsBack
      targetRightEndpoint rightSuccess
  exact Term.idStrictRec_HEq_congr modeIsStrict carrierRenames leftRenames
    rightRenames baseTypeRenames baseRawRenames witnessRawRenames
    baseSound witnessSound

/-- Soundness for the success branch of equiv-application strengthening.
Direct mirror of `partialStrengthenTypedIdJOfSuccess_sound` with dual
carrier pivots; no cast bridge needed since `Ty.equiv` is a Ty
constructor and `Ty.rename` distributes definitionally. -/
theorem partialStrengthenTypedEquivApplyOfSuccess_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrierA carrierB : Ty level sourceScope}
    {targetCarrierA targetCarrierB : Ty level targetScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    {targetEquivRaw targetArgumentRaw : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {equivTerm : Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term sourceCtx carrierA argumentRaw}
    {targetEquivTerm :
      Term targetCtx (Ty.equiv targetCarrierA targetCarrierB) targetEquivRaw}
    {targetArgumentTerm :
      Term targetCtx targetCarrierA targetArgumentRaw}
    (carrierASuccess :
      carrierA.partialStrengthen? strengthening.back = some targetCarrierA)
    (carrierBSuccess :
      carrierB.partialStrengthen? strengthening.back = some targetCarrierB)
    (equivRawStrengthens :
      equivRaw.partialStrengthen? strengthening.back = some targetEquivRaw)
    (argumentRawStrengthens :
      argumentRaw.partialStrengthen? strengthening.back =
        some targetArgumentRaw)
    (equivRawRenames :
      equivRaw = targetEquivRaw.rename strengthening.forward)
    (argumentRawRenames :
      argumentRaw = targetArgumentRaw.rename strengthening.forward)
    (equivSound :
      HEq equivTerm
        (Term.rename strengthening.toTermRenaming targetEquivTerm))
    (argumentSound :
      HEq argumentTerm
        (Term.rename strengthening.toTermRenaming targetArgumentTerm)) :
    StrengtheningSoundness
      (partialStrengthenTypedEquivApplyOfSuccess
        (equivTerm := equivTerm) (argumentTerm := argumentTerm)
        targetEquivTerm targetArgumentTerm carrierASuccess carrierBSuccess
        equivRawStrengthens argumentRawStrengthens equivRawRenames
        argumentRawRenames) := by
  refine ⟨?_⟩
  unfold StrengtheningResult.renamedTarget
  dsimp [partialStrengthenTypedEquivApplyOfSuccess]
  have carrierARenames :
      carrierA = targetCarrierA.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename carrierA
      strengthening.forward strengthening.back strengthening.injectsBack
      targetCarrierA carrierASuccess
  have carrierBRenames :
      carrierB = targetCarrierB.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename carrierB
      strengthening.forward strengthening.back strengthening.injectsBack
      targetCarrierB carrierBSuccess
  exact Term.equivApply_HEq_congr carrierARenames carrierBRenames
    equivRawRenames argumentRawRenames equivSound argumentSound

/-- Soundness for the success branch of equivalence-application
strengthening.  Mirrors `partialStrengthenTypedEquivApplyOfSuccess_sound`
with `Term.equivApp` / `RawTerm.equivApp` in place of the
univalence-β `equivApply`. -/
theorem partialStrengthenTypedEquivAppOfSuccess_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrierA carrierB : Ty level sourceScope}
    {targetCarrierA targetCarrierB : Ty level targetScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    {targetEquivRaw targetArgumentRaw : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {equivTerm : Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term sourceCtx carrierA argumentRaw}
    {targetEquivTerm :
      Term targetCtx (Ty.equiv targetCarrierA targetCarrierB) targetEquivRaw}
    {targetArgumentTerm :
      Term targetCtx targetCarrierA targetArgumentRaw}
    (carrierASuccess :
      carrierA.partialStrengthen? strengthening.back = some targetCarrierA)
    (carrierBSuccess :
      carrierB.partialStrengthen? strengthening.back = some targetCarrierB)
    (equivRawStrengthens :
      equivRaw.partialStrengthen? strengthening.back = some targetEquivRaw)
    (argumentRawStrengthens :
      argumentRaw.partialStrengthen? strengthening.back =
        some targetArgumentRaw)
    (equivRawRenames :
      equivRaw = targetEquivRaw.rename strengthening.forward)
    (argumentRawRenames :
      argumentRaw = targetArgumentRaw.rename strengthening.forward)
    (equivSound :
      HEq equivTerm
        (Term.rename strengthening.toTermRenaming targetEquivTerm))
    (argumentSound :
      HEq argumentTerm
        (Term.rename strengthening.toTermRenaming targetArgumentTerm)) :
    StrengtheningSoundness
      (partialStrengthenTypedEquivAppOfSuccess
        (equivTerm := equivTerm) (argumentTerm := argumentTerm)
        targetEquivTerm targetArgumentTerm carrierASuccess carrierBSuccess
        equivRawStrengthens argumentRawStrengthens equivRawRenames
        argumentRawRenames) := by
  refine ⟨?_⟩
  unfold StrengtheningResult.renamedTarget
  dsimp [partialStrengthenTypedEquivAppOfSuccess]
  have carrierARenames :
      carrierA = targetCarrierA.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename carrierA
      strengthening.forward strengthening.back strengthening.injectsBack
      targetCarrierA carrierASuccess
  have carrierBRenames :
      carrierB = targetCarrierB.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename carrierB
      strengthening.forward strengthening.back strengthening.injectsBack
      targetCarrierB carrierBSuccess
  exact Term.equivApp_HEq_congr carrierARenames carrierBRenames
    equivRawRenames argumentRawRenames equivSound argumentSound

end Term

end LeanFX2
