import LeanFX2.Term.StrengtheningImage.RenameImageCastCore

/-! # Term/StrengtheningImage/RenameImageCastAdvanced

Rename-image success bridges for advanced cast-wrapped rename arms.
-/

namespace LeanFX2

namespace Term

/-- T3 reverse-image bridge for the cast-wrapped `Term.oeqFunext` rename arm. -/
theorem strengthenTyped?_rename_isSome_oeqFunext
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
    (domainType codomainType : Ty level sourceScope)
    (leftFunctionRaw rightFunctionRaw : RawTerm sourceScope)
    {pointwiseRaw : RawTerm sourceScope}
    (pointwiseProof :
      Term sourceCtx
        (oeqFunextPointwiseType domainType codomainType
          leftFunctionRaw rightFunctionRaw)
        pointwiseRaw)
    (pointwiseIH :
      (partialStrengthenTyped?
          (Term.rename typedRenaming pointwiseProof)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.oeqFunext domainType codomainType leftFunctionRaw
            rightFunctionRaw pointwiseProof))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true := by
  dsimp only [Term.rename]
  dsimp only [partialStrengthenTyped?]
  have domainStrengthens :
      (domainType.rename forwardRename).partialStrengthen? renameInverse
        = some domainType := by
    rw [Ty.partialStrengthen?_rename_some domainType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity domainType]
  have codomainStrengthens :
      (codomainType.rename forwardRename).partialStrengthen? renameInverse
        = some codomainType := by
    rw [Ty.partialStrengthen?_rename_some codomainType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity codomainType]
  have leftStrengthens :
      (leftFunctionRaw.rename forwardRename).partialStrengthen?
          renameInverse =
        some leftFunctionRaw := by
    rw [RawTerm.partialStrengthen?_rename_some leftFunctionRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity leftFunctionRaw]
  have rightStrengthens :
      (rightFunctionRaw.rename forwardRename).partialStrengthen?
          renameInverse =
        some rightFunctionRaw := by
    rw [RawTerm.partialStrengthen?_rename_some rightFunctionRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity rightFunctionRaw]
  have castedPointwiseIH :
      (partialStrengthenTyped?
          (oeqFunextPointwiseType_rename forwardRename domainType
              codomainType leftFunctionRaw rightFunctionRaw ▸
            Term.rename typedRenaming pointwiseProof)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true := by
    rw [partialStrengthenTyped?_isSome_castInvariant]
    exact pointwiseIH
  split
  next noDomainSuccess =>
    exact absurd (domainStrengthens.symm.trans noDomainSuccess)
      (by intro contra; cases contra)
  next targetDomainType domainSuccess =>
    split
    next noCodomainSuccess =>
      exact absurd (codomainStrengthens.symm.trans noCodomainSuccess)
        (by intro contra; cases contra)
    next targetCodomainType codomainSuccess =>
      split
      next noLeftSuccess =>
        exact absurd (leftStrengthens.symm.trans noLeftSuccess)
          (by intro contra; cases contra)
      next targetLeftFunctionRaw leftSuccess =>
        split
        next noRightSuccess =>
          exact absurd (rightStrengthens.symm.trans noRightSuccess)
            (by intro contra; cases contra)
        next targetRightFunctionRaw rightSuccess =>
          split
          next noPointwiseSuccess =>
            have noPointwiseIsSome :=
              congrArg Option.isSome noPointwiseSuccess
            rw [noPointwiseIsSome] at castedPointwiseIH
            cases castedPointwiseIH
          next pointwiseResult pointwiseSuccess =>
            rfl

/-- T3 reverse-image bridge for the cast-wrapped `Term.equivIntroHet` rename arm. -/
theorem strengthenTyped?_rename_isSome_equivIntroHet
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
    {carrierA carrierB : Ty level sourceScope}
    {forwardRaw backwardRaw leftInvRaw rightInvRaw : RawTerm sourceScope}
    (forward :
      Term sourceCtx (Ty.arrow carrierA carrierB) forwardRaw)
    (backward :
      Term sourceCtx (Ty.arrow carrierB carrierA) backwardRaw)
    (leftInv :
      Term sourceCtx
        (equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw)
        leftInvRaw)
    (rightInv :
      Term sourceCtx
        (equivIntroHetRightInverseType carrierB forwardRaw backwardRaw)
        rightInvRaw)
    (forwardIH :
      (partialStrengthenTyped?
          (Term.rename typedRenaming forward)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true)
    (backwardIH :
      (partialStrengthenTyped?
          (Term.rename typedRenaming backward)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true)
    (leftInvIH :
      (partialStrengthenTyped?
          (Term.rename typedRenaming leftInv)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true)
    (rightInvIH :
      (partialStrengthenTyped?
          (Term.rename typedRenaming rightInv)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.equivIntroHet forward backward leftInv rightInv))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true := by
  dsimp only [Term.rename]
  dsimp only [partialStrengthenTyped?]
  have carrierAStrengthens :
      (carrierA.rename forwardRename).partialStrengthen? renameInverse =
        some carrierA := by
    rw [Ty.partialStrengthen?_rename_some carrierA forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity carrierA]
  have carrierBStrengthens :
      (carrierB.rename forwardRename).partialStrengthen? renameInverse =
        some carrierB := by
    rw [Ty.partialStrengthen?_rename_some carrierB forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity carrierB]
  have castedLeftInvIH :
      (partialStrengthenTyped?
          (equivIntroHetLeftInverseType_rename forwardRename carrierA
              forwardRaw backwardRaw ▸
            Term.rename typedRenaming leftInv)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true := by
    rw [partialStrengthenTyped?_isSome_castInvariant]
    exact leftInvIH
  have castedRightInvIH :
      (partialStrengthenTyped?
          (equivIntroHetRightInverseType_rename forwardRename carrierB
              forwardRaw backwardRaw ▸
            Term.rename typedRenaming rightInv)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true := by
    rw [partialStrengthenTyped?_isSome_castInvariant]
    exact rightInvIH
  split
  next noCarrierASuccess =>
    exact absurd (carrierAStrengthens.symm.trans noCarrierASuccess)
      (by intro contra; cases contra)
  next targetCarrierA carrierASuccess =>
    split
    next noCarrierBSuccess =>
      exact absurd (carrierBStrengthens.symm.trans noCarrierBSuccess)
        (by intro contra; cases contra)
    next targetCarrierB carrierBSuccess =>
      split
      next noForwardSuccess =>
        have impossible : Option.isSome (none (α := _)) = true :=
          noForwardSuccess ▸ forwardIH
        cases impossible
      next forwardResult forwardSuccess =>
        split
        next noBackwardSuccess =>
          have impossible : Option.isSome (none (α := _)) = true :=
            noBackwardSuccess ▸ backwardIH
          cases impossible
        next backwardResult backwardSuccess =>
          split
          next noLeftInvSuccess =>
            have impossible : Option.isSome (none (α := _)) = true :=
              noLeftInvSuccess ▸ castedLeftInvIH
            cases impossible
          next leftInvResult leftInvSuccess =>
            split
            next noRightInvSuccess =>
              have impossible : Option.isSome (none (α := _)) = true :=
                noRightInvSuccess ▸ castedRightInvIH
              cases impossible
            next rightInvResult rightInvSuccess =>
              rfl

/-- T3 reverse-image bridge for the cast-wrapped `Term.boolElim` rename arm. -/
theorem strengthenTyped?_rename_isSome_boolElim
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
    {motiveType : Ty level (sourceScope + 1)}
    {scrutineeRaw thenRaw elseRaw : RawTerm sourceScope}
    (scrutinee : Term sourceCtx Ty.bool scrutineeRaw)
    (thenBranch :
      Term sourceCtx (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw)
    (elseBranch :
      Term sourceCtx (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw)
    (scrutineeIH :
      (partialStrengthenTyped?
          (Term.rename typedRenaming scrutinee)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true)
    (thenIH :
      (partialStrengthenTyped?
          (Term.rename typedRenaming thenBranch)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true)
    (elseIH :
      (partialStrengthenTyped?
          (Term.rename typedRenaming elseBranch)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.boolElim scrutinee thenBranch elseBranch))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true := by
  dsimp only [Term.rename]
  rw [partialStrengthenTyped?_isSome_castInvariant]
  dsimp only [partialStrengthenTyped?]
  have motiveStrengthens :
      (motiveType.rename forwardRename.lift).partialStrengthen?
          renameInverse.lift =
        some motiveType := by
    rw [Ty.partialStrengthen?_rename_some motiveType
      forwardRename.lift (@RawRenaming.identity sourceScope).lift
      renameInverse.lift
      (PartialRawRenaming.lift_rename_some renameInverseLeft),
      Ty.rename_pointwise
        (@RawRenaming.identity_lift_pointwise sourceScope) motiveType,
      Ty.rename_identity motiveType]
  have castedThenIH :
      (partialStrengthenTyped?
          (Ty.subst0_rename_commute motiveType Ty.bool
              RawTerm.boolTrue forwardRename ▸
            Term.rename typedRenaming thenBranch)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true := by
    rw [partialStrengthenTyped?_isSome_castInvariant]
    exact thenIH
  have castedElseIH :
      (partialStrengthenTyped?
          (Ty.subst0_rename_commute motiveType Ty.bool
              RawTerm.boolFalse forwardRename ▸
            Term.rename typedRenaming elseBranch)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true := by
    rw [partialStrengthenTyped?_isSome_castInvariant]
    exact elseIH
  split
  next noMotiveSuccess =>
    exact absurd (motiveStrengthens.symm.trans noMotiveSuccess)
      (by intro contra; cases contra)
  next targetMotiveType motiveSuccess =>
    split
    next noScrutineeSuccess =>
      have impossible : Option.isSome (none (α := _)) = true :=
        noScrutineeSuccess ▸ scrutineeIH
      cases impossible
    next scrutineeResult scrutineeSuccess =>
      split
      next noThenSuccess =>
        have impossible : Option.isSome (none (α := _)) = true :=
          noThenSuccess ▸ castedThenIH
        cases impossible
      next thenResult thenSuccess =>
        split
        next noElseSuccess =>
          have impossible : Option.isSome (none (α := _)) = true :=
            noElseSuccess ▸ castedElseIH
          cases impossible
        next elseResult elseSuccess =>
          rfl

end Term

end LeanFX2
