import LeanFX2.Term.StrengtheningImage.Core

/-! # Term/StrengtheningImage/TypeCodes

Soundness lemmas for universe and type-code strengthening producers.
-/

namespace LeanFX2

namespace Term

/-- Soundness for closed universe-code strengthening.  Closed-leaf
producer: the producer carries no scope-dependent payload, so the
recovered target renames to the source structurally. -/
theorem partialStrengthenTypedUniverseCode_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    StrengtheningSoundness
      (partialStrengthenTypedUniverseCode strengthening innerLevel
        outerLevel cumulOk levelLe) := by
  exact ⟨HEq.rfl⟩

/-- Soundness for arrow type-code strengthening: each schematic raw
payload survives the strengthening and the recovered target term
renames back to the source via `Term.arrowCode_HEq_congr`. -/
theorem partialStrengthenTypedArrowCode_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw codomainCodeRaw : RawTerm sourceScope)
    (targetDomainCodeRaw targetCodomainCodeRaw : RawTerm targetScope)
    (domainStrengthens :
      domainCodeRaw.partialStrengthen? strengthening.back =
        some targetDomainCodeRaw)
    (codomainStrengthens :
      codomainCodeRaw.partialStrengthen? strengthening.back =
        some targetCodomainCodeRaw) :
    StrengtheningSoundness
      (partialStrengthenTypedArrowCode (sourceCtx := sourceCtx)
        (targetCtx := targetCtx) (strengthening := strengthening)
        outerLevel levelLe domainCodeRaw codomainCodeRaw
        targetDomainCodeRaw targetCodomainCodeRaw
        domainStrengthens codomainStrengthens) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedArrowCode, StrengtheningResult.renamedTarget]
  have domainRenames :
      domainCodeRaw =
        targetDomainCodeRaw.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename domainCodeRaw
      strengthening.forward strengthening.back strengthening.injectsBack
      targetDomainCodeRaw domainStrengthens
  have codomainRenames :
      codomainCodeRaw =
        targetCodomainCodeRaw.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename codomainCodeRaw
      strengthening.forward strengthening.back strengthening.injectsBack
      targetCodomainCodeRaw codomainStrengthens
  exact Term.arrowCode_HEq_congr outerLevel levelLe domainRenames
    codomainRenames

/-- Soundness for Π type-code strengthening: domain at the current
context, codomain under the lifted partial renaming. -/
theorem partialStrengthenTypedPiTyCode_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm sourceScope)
    (codomainCodeRaw : RawTerm (sourceScope + 1))
    (targetDomainCodeRaw : RawTerm targetScope)
    (targetCodomainCodeRaw : RawTerm (targetScope + 1))
    (domainStrengthens :
      domainCodeRaw.partialStrengthen? strengthening.back =
        some targetDomainCodeRaw)
    (codomainStrengthens :
      codomainCodeRaw.partialStrengthen? strengthening.back.lift =
        some targetCodomainCodeRaw) :
    StrengtheningSoundness
      (partialStrengthenTypedPiTyCode (sourceCtx := sourceCtx)
        (targetCtx := targetCtx) (strengthening := strengthening)
        outerLevel levelLe domainCodeRaw codomainCodeRaw
        targetDomainCodeRaw targetCodomainCodeRaw
        domainStrengthens codomainStrengthens) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedPiTyCode, StrengtheningResult.renamedTarget]
  have domainRenames :
      domainCodeRaw =
        targetDomainCodeRaw.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename domainCodeRaw
      strengthening.forward strengthening.back strengthening.injectsBack
      targetDomainCodeRaw domainStrengthens
  have codomainRenames :
      codomainCodeRaw =
        targetCodomainCodeRaw.rename strengthening.forward.lift :=
    RawTerm.partialStrengthen?_imp_rename codomainCodeRaw
      strengthening.forward.lift strengthening.back.lift
      (PartialRawRenaming.lift_renamingInjectsBack
        strengthening.injectsBack)
      targetCodomainCodeRaw codomainStrengthens
  exact Term.piTyCode_HEq_congr outerLevel levelLe domainRenames
    codomainRenames

/-- Soundness for Σ type-code strengthening: domain at the current
context, codomain under the lifted partial renaming. -/
theorem partialStrengthenTypedSigmaTyCode_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm sourceScope)
    (codomainCodeRaw : RawTerm (sourceScope + 1))
    (targetDomainCodeRaw : RawTerm targetScope)
    (targetCodomainCodeRaw : RawTerm (targetScope + 1))
    (domainStrengthens :
      domainCodeRaw.partialStrengthen? strengthening.back =
        some targetDomainCodeRaw)
    (codomainStrengthens :
      codomainCodeRaw.partialStrengthen? strengthening.back.lift =
        some targetCodomainCodeRaw) :
    StrengtheningSoundness
      (partialStrengthenTypedSigmaTyCode (sourceCtx := sourceCtx)
        (targetCtx := targetCtx) (strengthening := strengthening)
        outerLevel levelLe domainCodeRaw codomainCodeRaw
        targetDomainCodeRaw targetCodomainCodeRaw
        domainStrengthens codomainStrengthens) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedSigmaTyCode,
    StrengtheningResult.renamedTarget]
  have domainRenames :
      domainCodeRaw =
        targetDomainCodeRaw.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename domainCodeRaw
      strengthening.forward strengthening.back strengthening.injectsBack
      targetDomainCodeRaw domainStrengthens
  have codomainRenames :
      codomainCodeRaw =
        targetCodomainCodeRaw.rename strengthening.forward.lift :=
    RawTerm.partialStrengthen?_imp_rename codomainCodeRaw
      strengthening.forward.lift strengthening.back.lift
      (PartialRawRenaming.lift_renamingInjectsBack
        strengthening.injectsBack)
      targetCodomainCodeRaw codomainStrengthens
  exact Term.sigmaTyCode_HEq_congr outerLevel levelLe domainRenames
    codomainRenames

/-- Soundness for product type-code strengthening. -/
theorem partialStrengthenTypedProductCode_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (firstCodeRaw secondCodeRaw : RawTerm sourceScope)
    (targetFirstCodeRaw targetSecondCodeRaw : RawTerm targetScope)
    (firstStrengthens :
      firstCodeRaw.partialStrengthen? strengthening.back =
        some targetFirstCodeRaw)
    (secondStrengthens :
      secondCodeRaw.partialStrengthen? strengthening.back =
        some targetSecondCodeRaw) :
    StrengtheningSoundness
      (partialStrengthenTypedProductCode (sourceCtx := sourceCtx)
        (targetCtx := targetCtx) (strengthening := strengthening)
        outerLevel levelLe firstCodeRaw secondCodeRaw
        targetFirstCodeRaw targetSecondCodeRaw
        firstStrengthens secondStrengthens) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedProductCode,
    StrengtheningResult.renamedTarget]
  have firstRenames :
      firstCodeRaw = targetFirstCodeRaw.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename firstCodeRaw
      strengthening.forward strengthening.back strengthening.injectsBack
      targetFirstCodeRaw firstStrengthens
  have secondRenames :
      secondCodeRaw = targetSecondCodeRaw.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename secondCodeRaw
      strengthening.forward strengthening.back strengthening.injectsBack
      targetSecondCodeRaw secondStrengthens
  exact Term.productCode_HEq_congr outerLevel levelLe firstRenames
    secondRenames

/-- Soundness for sum type-code strengthening. -/
theorem partialStrengthenTypedSumCode_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm sourceScope)
    (targetLeftCodeRaw targetRightCodeRaw : RawTerm targetScope)
    (leftStrengthens :
      leftCodeRaw.partialStrengthen? strengthening.back =
        some targetLeftCodeRaw)
    (rightStrengthens :
      rightCodeRaw.partialStrengthen? strengthening.back =
        some targetRightCodeRaw) :
    StrengtheningSoundness
      (partialStrengthenTypedSumCode (sourceCtx := sourceCtx)
        (targetCtx := targetCtx) (strengthening := strengthening)
        outerLevel levelLe leftCodeRaw rightCodeRaw
        targetLeftCodeRaw targetRightCodeRaw
        leftStrengthens rightStrengthens) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedSumCode, StrengtheningResult.renamedTarget]
  have leftRenames :
      leftCodeRaw = targetLeftCodeRaw.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename leftCodeRaw
      strengthening.forward strengthening.back strengthening.injectsBack
      targetLeftCodeRaw leftStrengthens
  have rightRenames :
      rightCodeRaw = targetRightCodeRaw.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename rightCodeRaw
      strengthening.forward strengthening.back strengthening.injectsBack
      targetRightCodeRaw rightStrengthens
  exact Term.sumCode_HEq_congr outerLevel levelLe leftRenames rightRenames

/-- Soundness for list type-code strengthening. -/
theorem partialStrengthenTypedListCode_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm sourceScope)
    (targetElementCodeRaw : RawTerm targetScope)
    (elementStrengthens :
      elementCodeRaw.partialStrengthen? strengthening.back =
        some targetElementCodeRaw) :
    StrengtheningSoundness
      (partialStrengthenTypedListCode (sourceCtx := sourceCtx)
        (targetCtx := targetCtx) (strengthening := strengthening)
        outerLevel levelLe elementCodeRaw targetElementCodeRaw
        elementStrengthens) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedListCode, StrengtheningResult.renamedTarget]
  have elementRenames :
      elementCodeRaw =
        targetElementCodeRaw.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename elementCodeRaw
      strengthening.forward strengthening.back strengthening.injectsBack
      targetElementCodeRaw elementStrengthens
  exact Term.listCode_HEq_congr outerLevel levelLe elementRenames

/-- Soundness for option type-code strengthening. -/
theorem partialStrengthenTypedOptionCode_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm sourceScope)
    (targetElementCodeRaw : RawTerm targetScope)
    (elementStrengthens :
      elementCodeRaw.partialStrengthen? strengthening.back =
        some targetElementCodeRaw) :
    StrengtheningSoundness
      (partialStrengthenTypedOptionCode (sourceCtx := sourceCtx)
        (targetCtx := targetCtx) (strengthening := strengthening)
        outerLevel levelLe elementCodeRaw targetElementCodeRaw
        elementStrengthens) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedOptionCode,
    StrengtheningResult.renamedTarget]
  have elementRenames :
      elementCodeRaw =
        targetElementCodeRaw.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename elementCodeRaw
      strengthening.forward strengthening.back strengthening.injectsBack
      targetElementCodeRaw elementStrengthens
  exact Term.optionCode_HEq_congr outerLevel levelLe elementRenames

/-- Soundness for either type-code strengthening. -/
theorem partialStrengthenTypedEitherCode_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm sourceScope)
    (targetLeftCodeRaw targetRightCodeRaw : RawTerm targetScope)
    (leftStrengthens :
      leftCodeRaw.partialStrengthen? strengthening.back =
        some targetLeftCodeRaw)
    (rightStrengthens :
      rightCodeRaw.partialStrengthen? strengthening.back =
        some targetRightCodeRaw) :
    StrengtheningSoundness
      (partialStrengthenTypedEitherCode (sourceCtx := sourceCtx)
        (targetCtx := targetCtx) (strengthening := strengthening)
        outerLevel levelLe leftCodeRaw rightCodeRaw
        targetLeftCodeRaw targetRightCodeRaw
        leftStrengthens rightStrengthens) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedEitherCode,
    StrengtheningResult.renamedTarget]
  have leftRenames :
      leftCodeRaw = targetLeftCodeRaw.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename leftCodeRaw
      strengthening.forward strengthening.back strengthening.injectsBack
      targetLeftCodeRaw leftStrengthens
  have rightRenames :
      rightCodeRaw = targetRightCodeRaw.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename rightCodeRaw
      strengthening.forward strengthening.back strengthening.injectsBack
      targetRightCodeRaw rightStrengthens
  exact Term.eitherCode_HEq_congr outerLevel levelLe leftRenames
    rightRenames

/-- Soundness for identity type-code strengthening. -/
theorem partialStrengthenTypedIdCode_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (typeCodeRaw leftRaw rightRaw : RawTerm sourceScope)
    (targetTypeCodeRaw targetLeftRaw targetRightRaw : RawTerm targetScope)
    (typeCodeStrengthens :
      typeCodeRaw.partialStrengthen? strengthening.back =
        some targetTypeCodeRaw)
    (leftStrengthens :
      leftRaw.partialStrengthen? strengthening.back =
        some targetLeftRaw)
    (rightStrengthens :
      rightRaw.partialStrengthen? strengthening.back =
        some targetRightRaw) :
    StrengtheningSoundness
      (partialStrengthenTypedIdCode (sourceCtx := sourceCtx)
        (targetCtx := targetCtx) (strengthening := strengthening)
        outerLevel levelLe typeCodeRaw leftRaw rightRaw
        targetTypeCodeRaw targetLeftRaw targetRightRaw
        typeCodeStrengthens leftStrengthens rightStrengthens) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedIdCode, StrengtheningResult.renamedTarget]
  have typeCodeRenames :
      typeCodeRaw = targetTypeCodeRaw.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename typeCodeRaw
      strengthening.forward strengthening.back strengthening.injectsBack
      targetTypeCodeRaw typeCodeStrengthens
  have leftRenames :
      leftRaw = targetLeftRaw.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename leftRaw
      strengthening.forward strengthening.back strengthening.injectsBack
      targetLeftRaw leftStrengthens
  have rightRenames :
      rightRaw = targetRightRaw.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename rightRaw
      strengthening.forward strengthening.back strengthening.injectsBack
      targetRightRaw rightStrengthens
  exact Term.idCode_HEq_congr outerLevel levelLe typeCodeRenames
    leftRenames rightRenames

/-- Soundness for equivalence type-code strengthening. -/
theorem partialStrengthenTypedEquivCode_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftTypeCodeRaw rightTypeCodeRaw : RawTerm sourceScope)
    (targetLeftTypeCodeRaw targetRightTypeCodeRaw : RawTerm targetScope)
    (leftStrengthens :
      leftTypeCodeRaw.partialStrengthen? strengthening.back =
        some targetLeftTypeCodeRaw)
    (rightStrengthens :
      rightTypeCodeRaw.partialStrengthen? strengthening.back =
        some targetRightTypeCodeRaw) :
    StrengtheningSoundness
      (partialStrengthenTypedEquivCode (sourceCtx := sourceCtx)
        (targetCtx := targetCtx) (strengthening := strengthening)
        outerLevel levelLe leftTypeCodeRaw rightTypeCodeRaw
        targetLeftTypeCodeRaw targetRightTypeCodeRaw
        leftStrengthens rightStrengthens) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedEquivCode,
    StrengtheningResult.renamedTarget]
  have leftRenames :
      leftTypeCodeRaw =
        targetLeftTypeCodeRaw.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename leftTypeCodeRaw
      strengthening.forward strengthening.back strengthening.injectsBack
      targetLeftTypeCodeRaw leftStrengthens
  have rightRenames :
      rightTypeCodeRaw =
        targetRightTypeCodeRaw.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename rightTypeCodeRaw
      strengthening.forward strengthening.back strengthening.injectsBack
      targetRightTypeCodeRaw rightStrengthens
  exact Term.equivCode_HEq_congr outerLevel levelLe leftRenames rightRenames

end Term

end LeanFX2
