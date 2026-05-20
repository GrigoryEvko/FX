import LeanFX2.Term.StrengtheningImage.Core

/-! # Term/StrengtheningImage/Reflexivity

Soundness lemmas for identity, observational, strict, and funext reflexivity producers.
-/

namespace LeanFX2

namespace Term

/-- Soundness for identity reflexivity strengthening. -/
theorem partialStrengthenTypedRefl_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrier : Ty level sourceScope}
    {targetCarrier : Ty level targetScope}
    {rawWitness : RawTerm sourceScope}
    {targetWitness : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (carrierStrengthens :
      carrier.partialStrengthen? strengthening.back = some targetCarrier)
    (witnessStrengthens :
      rawWitness.partialStrengthen? strengthening.back =
        some targetWitness) :
    StrengtheningSoundness
      (partialStrengthenTypedRefl (sourceCtx := sourceCtx)
        (targetCtx := targetCtx) (strengthening := strengthening)
        carrierStrengthens witnessStrengthens) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedRefl, StrengtheningResult.renamedTarget]
  have carrierRenames :
      carrier = targetCarrier.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename carrier strengthening.forward
      strengthening.back strengthening.injectsBack targetCarrier
      carrierStrengthens
  have witnessRenames :
      rawWitness = targetWitness.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename rawWitness
      strengthening.forward strengthening.back strengthening.injectsBack
      targetWitness witnessStrengthens
  exact Term.refl_HEq_congr carrierRenames witnessRenames

/-- Soundness for observational-equality reflexivity strengthening. -/
theorem partialStrengthenTypedOeqRefl_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrier : Ty level sourceScope}
    {targetCarrier : Ty level targetScope}
    {rawWitness : RawTerm sourceScope}
    {targetWitness : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (carrierStrengthens :
      carrier.partialStrengthen? strengthening.back = some targetCarrier)
    (witnessStrengthens :
      rawWitness.partialStrengthen? strengthening.back =
        some targetWitness) :
    StrengtheningSoundness
      (partialStrengthenTypedOeqRefl (sourceCtx := sourceCtx)
        (targetCtx := targetCtx) (strengthening := strengthening)
        carrierStrengthens witnessStrengthens) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedOeqRefl, StrengtheningResult.renamedTarget]
  have carrierRenames :
      carrier = targetCarrier.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename carrier strengthening.forward
      strengthening.back strengthening.injectsBack targetCarrier
      carrierStrengthens
  have witnessRenames :
      rawWitness = targetWitness.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename rawWitness
      strengthening.forward strengthening.back strengthening.injectsBack
      targetWitness witnessStrengthens
  exact Term.oeqRefl_HEq_congr carrierRenames witnessRenames

/-- Soundness for strict-identity reflexivity strengthening. -/
theorem partialStrengthenTypedIdStrictRefl_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level sourceScope}
    {targetCarrier : Ty level targetScope}
    {rawWitness : RawTerm sourceScope}
    {targetWitness : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (carrierStrengthens :
      carrier.partialStrengthen? strengthening.back = some targetCarrier)
    (witnessStrengthens :
      rawWitness.partialStrengthen? strengthening.back =
        some targetWitness) :
    StrengtheningSoundness
      (partialStrengthenTypedIdStrictRefl (sourceCtx := sourceCtx)
        (targetCtx := targetCtx) (strengthening := strengthening)
        modeIsStrict carrierStrengthens witnessStrengthens) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedIdStrictRefl,
    StrengtheningResult.renamedTarget]
  have carrierRenames :
      carrier = targetCarrier.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename carrier strengthening.forward
      strengthening.back strengthening.injectsBack targetCarrier
      carrierStrengthens
  have witnessRenames :
      rawWitness = targetWitness.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename rawWitness
      strengthening.forward strengthening.back strengthening.injectsBack
      targetWitness witnessStrengthens
  exact Term.idStrictRefl_HEq_congr modeIsStrict carrierRenames
    witnessRenames

/-- Soundness for canonical identity equivalence reflexivity
strengthening. -/
theorem partialStrengthenTypedEquivReflId_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (carrier : Ty level sourceScope)
    (targetCarrier : Ty level targetScope)
    (carrierStrengthens :
      carrier.partialStrengthen? strengthening.back = some targetCarrier) :
    StrengtheningSoundness
      (partialStrengthenTypedEquivReflId (sourceCtx := sourceCtx)
        (targetCtx := targetCtx) (strengthening := strengthening)
        carrier targetCarrier carrierStrengthens) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedEquivReflId,
    StrengtheningResult.renamedTarget]
  have carrierRenames :
      carrier = targetCarrier.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename carrier strengthening.forward
      strengthening.back strengthening.injectsBack targetCarrier
      carrierStrengthens
  exact Term.equivReflId_HEq_congr carrierRenames

/-- Soundness for Id-typed canonical-identity equivalence
strengthening. -/
theorem partialStrengthenTypedEquivReflIdAtId_sound
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level sourceScope)
    (targetCarrier : Ty level targetScope)
    (carrierRaw : RawTerm sourceScope)
    (targetCarrierRaw : RawTerm targetScope)
    (carrierStrengthens :
      carrier.partialStrengthen? strengthening.back = some targetCarrier)
    (carrierRawStrengthens :
      carrierRaw.partialStrengthen? strengthening.back =
        some targetCarrierRaw) :
    StrengtheningSoundness
      (partialStrengthenTypedEquivReflIdAtId (sourceCtx := sourceCtx)
        (targetCtx := targetCtx) (strengthening := strengthening)
        innerLevel innerLevelLt carrier targetCarrier
        carrierRaw targetCarrierRaw
        carrierStrengthens carrierRawStrengthens) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedEquivReflIdAtId,
    StrengtheningResult.renamedTarget]
  have carrierRenames :
      carrier = targetCarrier.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename carrier strengthening.forward
      strengthening.back strengthening.injectsBack targetCarrier
      carrierStrengthens
  have carrierRawRenames :
      carrierRaw = targetCarrierRaw.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename carrierRaw
      strengthening.forward strengthening.back strengthening.injectsBack
      targetCarrierRaw carrierRawStrengthens
  exact Term.equivReflIdAtId_HEq_congr carrierRenames carrierRawRenames

/-- Soundness for canonical funext reflexivity strengthening. -/
theorem partialStrengthenTypedFunextRefl_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (domainType codomainType : Ty level sourceScope)
    (targetDomainType targetCodomainType : Ty level targetScope)
    (applyRaw : RawTerm (sourceScope + 1))
    (targetApplyRaw : RawTerm (targetScope + 1))
    (domainStrengthens :
      domainType.partialStrengthen? strengthening.back =
        some targetDomainType)
    (codomainStrengthens :
      codomainType.partialStrengthen? strengthening.back =
        some targetCodomainType)
    (applyStrengthens :
      applyRaw.partialStrengthen? strengthening.back.lift =
        some targetApplyRaw) :
    StrengtheningSoundness
      (partialStrengthenTypedFunextRefl (sourceCtx := sourceCtx)
        (targetCtx := targetCtx) (strengthening := strengthening)
        domainType codomainType targetDomainType targetCodomainType
        applyRaw targetApplyRaw
        domainStrengthens codomainStrengthens applyStrengthens) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedFunextRefl,
    StrengtheningResult.renamedTarget]
  have domainRenames :
      domainType = targetDomainType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename domainType strengthening.forward
      strengthening.back strengthening.injectsBack targetDomainType
      domainStrengthens
  have codomainRenames :
      codomainType = targetCodomainType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename codomainType strengthening.forward
      strengthening.back strengthening.injectsBack targetCodomainType
      codomainStrengthens
  have applyRenames :
      applyRaw = targetApplyRaw.rename strengthening.forward.lift :=
    RawTerm.partialStrengthen?_imp_rename applyRaw
      strengthening.forward.lift strengthening.back.lift
      (PartialRawRenaming.lift_renamingInjectsBack
        strengthening.injectsBack)
      targetApplyRaw applyStrengthens
  have congrHEq :
      HEq (Term.funextRefl (context := sourceCtx) domainType codomainType
            applyRaw)
        (Term.funextRefl (context := sourceCtx)
          (targetDomainType.rename strengthening.forward)
          (targetCodomainType.rename strengthening.forward)
          (targetApplyRaw.rename strengthening.forward.lift)) :=
    Term.funextRefl_HEq_congr domainRenames codomainRenames applyRenames
  have castHEq :
      HEq
        (Term.funextRefl (context := sourceCtx)
          (targetDomainType.rename strengthening.forward)
          (targetCodomainType.rename strengthening.forward)
          (targetApplyRaw.rename strengthening.forward.lift))
        ((funextReflType_rename strengthening.forward targetDomainType
            targetCodomainType targetApplyRaw).symm ▸
          Term.funextRefl (context := sourceCtx)
            (targetDomainType.rename strengthening.forward)
            (targetCodomainType.rename strengthening.forward)
            (targetApplyRaw.rename strengthening.forward.lift)) :=
    heq_cast_left
      (motive := fun resultType =>
        Term sourceCtx resultType
          (RawTerm.lam
            (RawTerm.refl
              (targetApplyRaw.rename strengthening.forward.lift))))
      (funextReflType_rename strengthening.forward targetDomainType
        targetCodomainType targetApplyRaw).symm
      (Term.funextRefl (context := sourceCtx)
        (targetDomainType.rename strengthening.forward)
        (targetCodomainType.rename strengthening.forward)
        (targetApplyRaw.rename strengthening.forward.lift))
  exact HEq.trans congrHEq castHEq

/-- Soundness for Id-typed funext reflexivity strengthening. -/
theorem partialStrengthenTypedFunextReflAtId_sound
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (domainType codomainType : Ty level sourceScope)
    (targetDomainType targetCodomainType : Ty level targetScope)
    (applyRaw : RawTerm (sourceScope + 1))
    (targetApplyRaw : RawTerm (targetScope + 1))
    (domainStrengthens :
      domainType.partialStrengthen? strengthening.back =
        some targetDomainType)
    (codomainStrengthens :
      codomainType.partialStrengthen? strengthening.back =
        some targetCodomainType)
    (applyStrengthens :
      applyRaw.partialStrengthen? strengthening.back.lift =
        some targetApplyRaw) :
    StrengtheningSoundness
      (partialStrengthenTypedFunextReflAtId (sourceCtx := sourceCtx)
        (targetCtx := targetCtx) (strengthening := strengthening)
        domainType codomainType targetDomainType targetCodomainType
        applyRaw targetApplyRaw
        domainStrengthens codomainStrengthens applyStrengthens) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedFunextReflAtId,
    StrengtheningResult.renamedTarget]
  have domainRenames :
      domainType = targetDomainType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename domainType strengthening.forward
      strengthening.back strengthening.injectsBack targetDomainType
      domainStrengthens
  have codomainRenames :
      codomainType = targetCodomainType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename codomainType strengthening.forward
      strengthening.back strengthening.injectsBack targetCodomainType
      codomainStrengthens
  have applyRenames :
      applyRaw = targetApplyRaw.rename strengthening.forward.lift :=
    RawTerm.partialStrengthen?_imp_rename applyRaw
      strengthening.forward.lift strengthening.back.lift
      (PartialRawRenaming.lift_renamingInjectsBack
        strengthening.injectsBack)
      targetApplyRaw applyStrengthens
  exact Term.funextReflAtId_HEq_congr domainRenames codomainRenames
    applyRenames

end Term

end LeanFX2
