import LeanFX2.Term.PartialStrengthen.RenameImage.RecursiveEliminators

/-! # Term/PartialStrengthen/RenameImage/TypeCodes

Rename-image T1 equations for type-code term constructors.
-/

namespace LeanFX2

namespace Term

/-- Type-code strength-T1 case: `Term.listCode`.

Single RawTerm payload (`elementCodeRaw`).  Dispatcher matches the
renamed RawTerm's strengthening via subst-via-witness on
`RawTerm.partialStrengthen?_rename_some`. -/
theorem strengthenTyped?_rename_eq_listCode
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm sourceScope) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.listCode (context := sourceCtx) outerLevel levelLe
            elementCodeRaw))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.listCode (context := sourceCtx) outerLevel levelLe
            elementCodeRaw)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have elementStrengthens :
      (elementCodeRaw.rename forwardRename).partialStrengthen? renameInverse
        = some elementCodeRaw := by
    rw [RawTerm.partialStrengthen?_rename_some elementCodeRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity elementCodeRaw]
  split
  next noElementSuccess =>
    exact absurd (elementStrengthens.symm.trans noElementSuccess)
      (by intro contra; cases contra)
  next targetElementCodeRaw elementSuccess =>
    have elementEq : targetElementCodeRaw = elementCodeRaw :=
      Option.some.inj (elementSuccess.symm.trans elementStrengthens)
    subst elementEq
    rfl

/-- Type-code strength-T1 case: `Term.optionCode`. -/
theorem strengthenTyped?_rename_eq_optionCode
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm sourceScope) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.optionCode (context := sourceCtx) outerLevel levelLe
            elementCodeRaw))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.optionCode (context := sourceCtx) outerLevel levelLe
            elementCodeRaw)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have elementStrengthens :
      (elementCodeRaw.rename forwardRename).partialStrengthen? renameInverse
        = some elementCodeRaw := by
    rw [RawTerm.partialStrengthen?_rename_some elementCodeRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity elementCodeRaw]
  split
  next noElementSuccess =>
    exact absurd (elementStrengthens.symm.trans noElementSuccess)
      (by intro contra; cases contra)
  next targetElementCodeRaw elementSuccess =>
    have elementEq : targetElementCodeRaw = elementCodeRaw :=
      Option.some.inj (elementSuccess.symm.trans elementStrengthens)
    subst elementEq
    rfl

/-- Type-code strength-T1 case: `Term.arrowCode`.

Non-binder shape: both `domainCodeRaw` and `codomainCodeRaw` rename
via `rho` at the outer scope. -/
theorem strengthenTyped?_rename_eq_arrowCode
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw codomainCodeRaw : RawTerm sourceScope) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.arrowCode (context := sourceCtx) outerLevel levelLe
            domainCodeRaw codomainCodeRaw))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.arrowCode (context := sourceCtx) outerLevel levelLe
            domainCodeRaw codomainCodeRaw)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have domainStrengthens :
      (domainCodeRaw.rename forwardRename).partialStrengthen? renameInverse
        = some domainCodeRaw := by
    rw [RawTerm.partialStrengthen?_rename_some domainCodeRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity domainCodeRaw]
  have codomainStrengthens :
      (codomainCodeRaw.rename forwardRename).partialStrengthen? renameInverse
        = some codomainCodeRaw := by
    rw [RawTerm.partialStrengthen?_rename_some codomainCodeRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity codomainCodeRaw]
  split
  next noDomainSuccess =>
    exact absurd (domainStrengthens.symm.trans noDomainSuccess)
      (by intro contra; cases contra)
  next targetDomainCodeRaw domainSuccess =>
    have domainEq : targetDomainCodeRaw = domainCodeRaw :=
      Option.some.inj (domainSuccess.symm.trans domainStrengthens)
    subst domainEq
    split
    next noCodomainSuccess =>
      exact absurd (codomainStrengthens.symm.trans noCodomainSuccess)
        (by intro contra; cases contra)
    next targetCodomainCodeRaw codomainSuccess =>
      have codomainEq : targetCodomainCodeRaw = codomainCodeRaw :=
        Option.some.inj (codomainSuccess.symm.trans codomainStrengthens)
      subst codomainEq
      rfl

/-- Type-code strength-T1 case: `Term.sumCode`. -/
theorem strengthenTyped?_rename_eq_sumCode
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm sourceScope) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.sumCode (context := sourceCtx) outerLevel levelLe
            leftCodeRaw rightCodeRaw))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.sumCode (context := sourceCtx) outerLevel levelLe
            leftCodeRaw rightCodeRaw)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have leftStrengthens :
      (leftCodeRaw.rename forwardRename).partialStrengthen? renameInverse
        = some leftCodeRaw := by
    rw [RawTerm.partialStrengthen?_rename_some leftCodeRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity leftCodeRaw]
  have rightStrengthens :
      (rightCodeRaw.rename forwardRename).partialStrengthen? renameInverse
        = some rightCodeRaw := by
    rw [RawTerm.partialStrengthen?_rename_some rightCodeRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity rightCodeRaw]
  split
  next noLeftSuccess =>
    exact absurd (leftStrengthens.symm.trans noLeftSuccess)
      (by intro contra; cases contra)
  next targetLeftCodeRaw leftSuccess =>
    have leftEq : targetLeftCodeRaw = leftCodeRaw :=
      Option.some.inj (leftSuccess.symm.trans leftStrengthens)
    subst leftEq
    split
    next noRightSuccess =>
      exact absurd (rightStrengthens.symm.trans noRightSuccess)
        (by intro contra; cases contra)
    next targetRightCodeRaw rightSuccess =>
      have rightEq : targetRightCodeRaw = rightCodeRaw :=
        Option.some.inj (rightSuccess.symm.trans rightStrengthens)
      subst rightEq
      rfl

/-- Type-code strength-T1 case: `Term.productCode`. -/
theorem strengthenTyped?_rename_eq_productCode
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (firstCodeRaw secondCodeRaw : RawTerm sourceScope) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.productCode (context := sourceCtx) outerLevel levelLe
            firstCodeRaw secondCodeRaw))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.productCode (context := sourceCtx) outerLevel levelLe
            firstCodeRaw secondCodeRaw)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have firstStrengthens :
      (firstCodeRaw.rename forwardRename).partialStrengthen? renameInverse
        = some firstCodeRaw := by
    rw [RawTerm.partialStrengthen?_rename_some firstCodeRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity firstCodeRaw]
  have secondStrengthens :
      (secondCodeRaw.rename forwardRename).partialStrengthen? renameInverse
        = some secondCodeRaw := by
    rw [RawTerm.partialStrengthen?_rename_some secondCodeRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity secondCodeRaw]
  split
  next noFirstSuccess =>
    exact absurd (firstStrengthens.symm.trans noFirstSuccess)
      (by intro contra; cases contra)
  next targetFirstCodeRaw firstSuccess =>
    have firstEq : targetFirstCodeRaw = firstCodeRaw :=
      Option.some.inj (firstSuccess.symm.trans firstStrengthens)
    subst firstEq
    split
    next noSecondSuccess =>
      exact absurd (secondStrengthens.symm.trans noSecondSuccess)
        (by intro contra; cases contra)
    next targetSecondCodeRaw secondSuccess =>
      have secondEq : targetSecondCodeRaw = secondCodeRaw :=
        Option.some.inj (secondSuccess.symm.trans secondStrengthens)
      subst secondEq
      rfl

/-- Type-code strength-T1 case: `Term.eitherCode`. -/
theorem strengthenTyped?_rename_eq_eitherCode
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm sourceScope) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.eitherCode (context := sourceCtx) outerLevel levelLe
            leftCodeRaw rightCodeRaw))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.eitherCode (context := sourceCtx) outerLevel levelLe
            leftCodeRaw rightCodeRaw)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have leftStrengthens :
      (leftCodeRaw.rename forwardRename).partialStrengthen? renameInverse
        = some leftCodeRaw := by
    rw [RawTerm.partialStrengthen?_rename_some leftCodeRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity leftCodeRaw]
  have rightStrengthens :
      (rightCodeRaw.rename forwardRename).partialStrengthen? renameInverse
        = some rightCodeRaw := by
    rw [RawTerm.partialStrengthen?_rename_some rightCodeRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity rightCodeRaw]
  split
  next noLeftSuccess =>
    exact absurd (leftStrengthens.symm.trans noLeftSuccess)
      (by intro contra; cases contra)
  next targetLeftCodeRaw leftSuccess =>
    have leftEq : targetLeftCodeRaw = leftCodeRaw :=
      Option.some.inj (leftSuccess.symm.trans leftStrengthens)
    subst leftEq
    split
    next noRightSuccess =>
      exact absurd (rightStrengthens.symm.trans noRightSuccess)
        (by intro contra; cases contra)
    next targetRightCodeRaw rightSuccess =>
      have rightEq : targetRightCodeRaw = rightCodeRaw :=
        Option.some.inj (rightSuccess.symm.trans rightStrengthens)
      subst rightEq
      rfl

/-- Type-code strength-T1 case: `Term.idCode`.

Three RawTerm payloads sequenced. -/
theorem strengthenTyped?_rename_eq_idCode
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (typeCodeRaw leftRaw rightRaw : RawTerm sourceScope) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.idCode (context := sourceCtx) outerLevel levelLe
            typeCodeRaw leftRaw rightRaw))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.idCode (context := sourceCtx) outerLevel levelLe
            typeCodeRaw leftRaw rightRaw)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have typeStrengthens :
      (typeCodeRaw.rename forwardRename).partialStrengthen? renameInverse
        = some typeCodeRaw := by
    rw [RawTerm.partialStrengthen?_rename_some typeCodeRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity typeCodeRaw]
  have leftStrengthens :
      (leftRaw.rename forwardRename).partialStrengthen? renameInverse
        = some leftRaw := by
    rw [RawTerm.partialStrengthen?_rename_some leftRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity leftRaw]
  have rightStrengthens :
      (rightRaw.rename forwardRename).partialStrengthen? renameInverse
        = some rightRaw := by
    rw [RawTerm.partialStrengthen?_rename_some rightRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity rightRaw]
  split
  next noTypeSuccess =>
    exact absurd (typeStrengthens.symm.trans noTypeSuccess)
      (by intro contra; cases contra)
  next targetTypeCodeRaw typeSuccess =>
    have typeEq : targetTypeCodeRaw = typeCodeRaw :=
      Option.some.inj (typeSuccess.symm.trans typeStrengthens)
    subst typeEq
    split
    next noLeftSuccess =>
      exact absurd (leftStrengthens.symm.trans noLeftSuccess)
        (by intro contra; cases contra)
    next targetLeftRaw leftSuccess =>
      have leftEq : targetLeftRaw = leftRaw :=
        Option.some.inj (leftSuccess.symm.trans leftStrengthens)
      subst leftEq
      split
      next noRightSuccess =>
        exact absurd (rightStrengthens.symm.trans noRightSuccess)
          (by intro contra; cases contra)
      next targetRightRaw rightSuccess =>
        have rightEq : targetRightRaw = rightRaw :=
          Option.some.inj (rightSuccess.symm.trans rightStrengthens)
        subst rightEq
        rfl

/-- Type-code strength-T1 case: `Term.equivCode`. -/
theorem strengthenTyped?_rename_eq_equivCode
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftTypeCodeRaw rightTypeCodeRaw : RawTerm sourceScope) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.equivCode (context := sourceCtx) outerLevel levelLe
            leftTypeCodeRaw rightTypeCodeRaw))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.equivCode (context := sourceCtx) outerLevel levelLe
            leftTypeCodeRaw rightTypeCodeRaw)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have leftStrengthens :
      (leftTypeCodeRaw.rename forwardRename).partialStrengthen? renameInverse
        = some leftTypeCodeRaw := by
    rw [RawTerm.partialStrengthen?_rename_some leftTypeCodeRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity leftTypeCodeRaw]
  have rightStrengthens :
      (rightTypeCodeRaw.rename forwardRename).partialStrengthen? renameInverse
        = some rightTypeCodeRaw := by
    rw [RawTerm.partialStrengthen?_rename_some rightTypeCodeRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity rightTypeCodeRaw]
  split
  next noLeftSuccess =>
    exact absurd (leftStrengthens.symm.trans noLeftSuccess)
      (by intro contra; cases contra)
  next targetLeftTypeCodeRaw leftSuccess =>
    have leftEq : targetLeftTypeCodeRaw = leftTypeCodeRaw :=
      Option.some.inj (leftSuccess.symm.trans leftStrengthens)
    subst leftEq
    split
    next noRightSuccess =>
      exact absurd (rightStrengthens.symm.trans noRightSuccess)
        (by intro contra; cases contra)
    next targetRightTypeCodeRaw rightSuccess =>
      have rightEq : targetRightTypeCodeRaw = rightTypeCodeRaw :=
        Option.some.inj (rightSuccess.symm.trans rightStrengthens)
      subst rightEq
      rfl

/-- Type-code strength-T1 case: `Term.piTyCode`.

Binder-shape: `domainCodeRaw` renames via `rho` at the outer scope,
`codomainCodeRaw` renames via `rho.lift` under one binder.  The
codomain witness uses
`PartialRawRenaming.lift_rename_some` for survival under the lift,
combined with `RawRenaming.identity_lift_pointwise` + rename_identity
to collapse `codomainCodeRaw.rename id.lift` back to `codomainCodeRaw`. -/
theorem strengthenTyped?_rename_eq_piTyCode
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm sourceScope)
    (codomainCodeRaw : RawTerm (sourceScope + 1)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.piTyCode (context := sourceCtx) outerLevel levelLe
            domainCodeRaw codomainCodeRaw))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.piTyCode (context := sourceCtx) outerLevel levelLe
            domainCodeRaw codomainCodeRaw)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have domainStrengthens :
      (domainCodeRaw.rename forwardRename).partialStrengthen? renameInverse
        = some domainCodeRaw := by
    rw [RawTerm.partialStrengthen?_rename_some domainCodeRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity domainCodeRaw]
  have codomainStrengthens :
      (codomainCodeRaw.rename forwardRename.lift).partialStrengthen?
          renameInverse.lift
        = some codomainCodeRaw := by
    rw [RawTerm.partialStrengthen?_rename_some codomainCodeRaw
      forwardRename.lift (@RawRenaming.identity sourceScope).lift
      renameInverse.lift
      (PartialRawRenaming.lift_rename_some renameInverseLeft),
      RawTerm.rename_pointwise
        (@RawRenaming.identity_lift_pointwise sourceScope) codomainCodeRaw,
      RawTerm.rename_identity codomainCodeRaw]
  split
  next noDomainSuccess =>
    exact absurd (domainStrengthens.symm.trans noDomainSuccess)
      (by intro contra; cases contra)
  next targetDomainCodeRaw domainSuccess =>
    have domainEq : targetDomainCodeRaw = domainCodeRaw :=
      Option.some.inj (domainSuccess.symm.trans domainStrengthens)
    subst domainEq
    split
    next noCodomainSuccess =>
      exact absurd (codomainStrengthens.symm.trans noCodomainSuccess)
        (by intro contra; cases contra)
    next targetCodomainCodeRaw codomainSuccess =>
      have codomainEq : targetCodomainCodeRaw = codomainCodeRaw :=
        Option.some.inj (codomainSuccess.symm.trans codomainStrengthens)
      subst codomainEq
      rfl

/-- Type-code strength-T1 case: `Term.sigmaTyCode`.

Binder-shape mirror of `piTyCode`: same survival pattern under the
codomain binder. -/
theorem strengthenTyped?_rename_eq_sigmaTyCode
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm sourceScope)
    (codomainCodeRaw : RawTerm (sourceScope + 1)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.sigmaTyCode (context := sourceCtx) outerLevel levelLe
            domainCodeRaw codomainCodeRaw))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.sigmaTyCode (context := sourceCtx) outerLevel levelLe
            domainCodeRaw codomainCodeRaw)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have domainStrengthens :
      (domainCodeRaw.rename forwardRename).partialStrengthen? renameInverse
        = some domainCodeRaw := by
    rw [RawTerm.partialStrengthen?_rename_some domainCodeRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity domainCodeRaw]
  have codomainStrengthens :
      (codomainCodeRaw.rename forwardRename.lift).partialStrengthen?
          renameInverse.lift
        = some codomainCodeRaw := by
    rw [RawTerm.partialStrengthen?_rename_some codomainCodeRaw
      forwardRename.lift (@RawRenaming.identity sourceScope).lift
      renameInverse.lift
      (PartialRawRenaming.lift_rename_some renameInverseLeft),
      RawTerm.rename_pointwise
        (@RawRenaming.identity_lift_pointwise sourceScope) codomainCodeRaw,
      RawTerm.rename_identity codomainCodeRaw]
  split
  next noDomainSuccess =>
    exact absurd (domainStrengthens.symm.trans noDomainSuccess)
      (by intro contra; cases contra)
  next targetDomainCodeRaw domainSuccess =>
    have domainEq : targetDomainCodeRaw = domainCodeRaw :=
      Option.some.inj (domainSuccess.symm.trans domainStrengthens)
    subst domainEq
    split
    next noCodomainSuccess =>
      exact absurd (codomainStrengthens.symm.trans noCodomainSuccess)
        (by intro contra; cases contra)
    next targetCodomainCodeRaw codomainSuccess =>
      have codomainEq : targetCodomainCodeRaw = codomainCodeRaw :=
        Option.some.inj (codomainSuccess.symm.trans codomainStrengthens)
      subst codomainEq
      rfl

end Term

end LeanFX2
