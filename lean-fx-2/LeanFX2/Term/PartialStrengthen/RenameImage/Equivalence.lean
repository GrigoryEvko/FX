import LeanFX2.Term.PartialStrengthen.RenameImage.Core

/-! # Term/PartialStrengthen/RenameImage/Equivalence

Rename-image T1 equations for equivalence, funext, and univalence cases.
-/

namespace LeanFX2

namespace Term

/-- HoTT-special strength-T1 case: `Term.funextReflAtId`.

Carries 2 Ty payloads at the outer scope (domainType, codomainType)
plus 1 RawTerm payload under one binder (applyRaw via `back.lift`).
The codomain RawTerm `applyRaw` uses the same `rho.lift` survival
recipe as `piTyCode`. -/
theorem strengthenTyped?_rename_eq_funextReflAtId
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
    {domainType codomainType : Ty level sourceScope}
    (applyRaw : RawTerm (sourceScope + 1)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.funextReflAtId (context := sourceCtx) domainType codomainType
            applyRaw))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.funextReflAtId (context := sourceCtx) domainType codomainType
            applyRaw)) := by
  dsimp only [Term.rename, partialStrengthenTyped?]
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
  have applyStrengthens :
      (applyRaw.rename forwardRename.lift).partialStrengthen?
          renameInverse.lift
        = some applyRaw := by
    rw [RawTerm.partialStrengthen?_rename_some applyRaw
      forwardRename.lift (@RawRenaming.identity sourceScope).lift
      renameInverse.lift
      (PartialRawRenaming.lift_rename_some renameInverseLeft),
      RawTerm.rename_pointwise
        (@RawRenaming.identity_lift_pointwise sourceScope) applyRaw,
      RawTerm.rename_identity applyRaw]
  split
  next noDomainSuccess =>
    exact absurd (domainStrengthens.symm.trans noDomainSuccess)
      (by intro contra; cases contra)
  next targetDomainType domainSuccess =>
    have domainEq : targetDomainType = domainType :=
      Option.some.inj (domainSuccess.symm.trans domainStrengthens)
    subst domainEq
    split
    next noCodomainSuccess =>
      exact absurd (codomainStrengthens.symm.trans noCodomainSuccess)
        (by intro contra; cases contra)
    next targetCodomainType codomainSuccess =>
      have codomainEq : targetCodomainType = codomainType :=
        Option.some.inj (codomainSuccess.symm.trans codomainStrengthens)
      subst codomainEq
      split
      next noApplySuccess =>
        exact absurd (applyStrengthens.symm.trans noApplySuccess)
          (by intro contra; cases contra)
      next targetApplyRaw applySuccess =>
        have applyEq : targetApplyRaw = applyRaw :=
          Option.some.inj (applySuccess.symm.trans applyStrengthens)
        subst applyEq
        rfl

/-- HoTT-special strength-T1 case: `Term.equivApp`.

Carries 2 Ty payloads (`carrierA + carrierB` at outer `back`) + 2 Term
IHs (`equivTerm` at `Ty.equiv carrierA carrierB` + `argumentTerm` at
`carrierA`).  Both Ty payloads are implicit on the ctor. -/
theorem strengthenTyped?_rename_eq_equivApp
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
    {equivRaw argumentRaw : RawTerm sourceScope}
    (equivTerm : Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw)
    (argumentTerm : Term sourceCtx carrierA argumentRaw)
    (equivIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming equivTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            equivTerm))
    (argumentIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming argumentTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            argumentTerm)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.equivApp (context := sourceCtx) equivTerm argumentTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.equivApp (context := sourceCtx) equivTerm argumentTerm)) := by
  dsimp only [Term.rename, partialStrengthenTyped?]
  have carrierAStrengthens :
      (carrierA.rename forwardRename).partialStrengthen? renameInverse
        = some carrierA := by
    rw [Ty.partialStrengthen?_rename_some carrierA forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity carrierA]
  have carrierBStrengthens :
      (carrierB.rename forwardRename).partialStrengthen? renameInverse
        = some carrierB := by
    rw [Ty.partialStrengthen?_rename_some carrierB forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity carrierB]
  split
  next noCarrierASuccess =>
    exact absurd (carrierAStrengthens.symm.trans noCarrierASuccess)
      (by intro contra; cases contra)
  next targetCarrierA carrierASuccess =>
    have carrierAEq : targetCarrierA = carrierA :=
      Option.some.inj (carrierASuccess.symm.trans carrierAStrengthens)
    subst carrierAEq
    split
    next noCarrierBSuccess =>
      exact absurd (carrierBStrengthens.symm.trans noCarrierBSuccess)
        (by intro contra; cases contra)
    next targetCarrierB carrierBSuccess =>
      have carrierBEq : targetCarrierB = carrierB :=
        Option.some.inj (carrierBSuccess.symm.trans carrierBStrengthens)
      subst carrierBEq
      split
      next noEquivSuccess =>
        exact absurd (equivIH.symm.trans noEquivSuccess)
          (by intro contra; cases contra)
      next equivResult equivSuccess =>
        have equivEq : equivResult =
            StrengtheningResult.fromRename forwardRename typedRenaming
              renameInverse renameInverseLeft renameInverseInjects
              equivTerm :=
          Option.some.inj (equivSuccess.symm.trans equivIH)
        subst equivEq
        split
        next noArgumentSuccess =>
          exact absurd (argumentIH.symm.trans noArgumentSuccess)
            (by intro contra; cases contra)
        next argumentResult argumentSuccess =>
          have argumentEq : argumentResult =
              StrengtheningResult.fromRename forwardRename typedRenaming
                renameInverse renameInverseLeft renameInverseInjects
                argumentTerm :=
            Option.some.inj (argumentSuccess.symm.trans argumentIH)
          subst argumentEq
          rfl

/-- HoTT-special strength-T1 case: `Term.equivApply`.

Carries 2 outer Ty payloads (carrierA + carrierB at `back`) + 2 Term
IHs (equivTerm at `Ty.equiv carrierA carrierB`, argumentTerm at
carrierA).  No cast on rename — result type `carrierB` renames
structurally; same precedent as `equivApp`. -/
theorem strengthenTyped?_rename_eq_equivApply
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
    {equivRaw argumentRaw : RawTerm sourceScope}
    (equivTerm : Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw)
    (argumentTerm : Term sourceCtx carrierA argumentRaw)
    (equivIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming equivTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            equivTerm))
    (argumentIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming argumentTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            argumentTerm)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming (Term.equivApply equivTerm argumentTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.equivApply equivTerm argumentTerm)) := by
  dsimp only [Term.rename, partialStrengthenTyped?]
  have carrierAStrengthens :
      (carrierA.rename forwardRename).partialStrengthen? renameInverse
        = some carrierA := by
    rw [Ty.partialStrengthen?_rename_some carrierA forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity carrierA]
  have carrierBStrengthens :
      (carrierB.rename forwardRename).partialStrengthen? renameInverse
        = some carrierB := by
    rw [Ty.partialStrengthen?_rename_some carrierB forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity carrierB]
  split
  next noCarrierASuccess =>
    exact absurd (carrierAStrengthens.symm.trans noCarrierASuccess)
      (by intro contra; cases contra)
  next targetCarrierA carrierASuccess =>
    have carrierAEq : targetCarrierA = carrierA :=
      Option.some.inj (carrierASuccess.symm.trans carrierAStrengthens)
    subst carrierAEq
    split
    next noCarrierBSuccess =>
      exact absurd (carrierBStrengthens.symm.trans noCarrierBSuccess)
        (by intro contra; cases contra)
    next targetCarrierB carrierBSuccess =>
      have carrierBEq : targetCarrierB = carrierB :=
        Option.some.inj (carrierBSuccess.symm.trans carrierBStrengthens)
      subst carrierBEq
      split
      next noEquivSuccess =>
        exact absurd (equivIH.symm.trans noEquivSuccess)
          (by intro contra; cases contra)
      next equivResult equivSuccess =>
        have equivEq : equivResult =
            StrengtheningResult.fromRename forwardRename typedRenaming
              renameInverse renameInverseLeft renameInverseInjects
              equivTerm :=
          Option.some.inj (equivSuccess.symm.trans equivIH)
        subst equivEq
        split
        next noArgumentSuccess =>
          exact absurd (argumentIH.symm.trans noArgumentSuccess)
            (by intro contra; cases contra)
        next argumentResult argumentSuccess =>
          have argumentEq : argumentResult =
              StrengtheningResult.fromRename forwardRename typedRenaming
                renameInverse renameInverseLeft renameInverseInjects
                argumentTerm :=
            Option.some.inj (argumentSuccess.symm.trans argumentIH)
          subst argumentEq
          rfl

/-- HoTT-special strength-T1 case: `Term.uaToEquiv`.

Carries `innerLevel` + `innerLevelLt` value-shape + 2 Ty payloads
(leftTy, rightTy at outer `back`) + 2 RawTerm payloads
(leftTyRaw, rightTyRaw at outer `back`) + 1 Term IH (proof at
`Ty.id (Ty.universe innerLevel innerLevelLt) leftTyRaw rightTyRaw`).
No cast on rename — result `Ty.equiv leftTy rightTy` renames
structurally. -/
theorem strengthenTyped?_rename_eq_uaToEquiv
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
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (leftTy rightTy : Ty level sourceScope)
    (leftTyRaw rightTyRaw : RawTerm sourceScope)
    {proofRaw : RawTerm sourceScope}
    (proof : Term sourceCtx
      (Ty.id (Ty.universe innerLevel innerLevelLt) leftTyRaw rightTyRaw)
      proofRaw)
    (proofIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming proof)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            proof)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.uaToEquiv (context := sourceCtx) innerLevel innerLevelLt
            leftTy rightTy leftTyRaw rightTyRaw proof))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.uaToEquiv (context := sourceCtx) innerLevel innerLevelLt
            leftTy rightTy leftTyRaw rightTyRaw proof)) := by
  dsimp only [Term.rename, partialStrengthenTyped?]
  have leftTyStrengthens :
      (leftTy.rename forwardRename).partialStrengthen? renameInverse
        = some leftTy := by
    rw [Ty.partialStrengthen?_rename_some leftTy forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity leftTy]
  have rightTyStrengthens :
      (rightTy.rename forwardRename).partialStrengthen? renameInverse
        = some rightTy := by
    rw [Ty.partialStrengthen?_rename_some rightTy forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity rightTy]
  have leftRawStrengthens :
      (leftTyRaw.rename forwardRename).partialStrengthen? renameInverse
        = some leftTyRaw := by
    rw [RawTerm.partialStrengthen?_rename_some leftTyRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity leftTyRaw]
  have rightRawStrengthens :
      (rightTyRaw.rename forwardRename).partialStrengthen? renameInverse
        = some rightTyRaw := by
    rw [RawTerm.partialStrengthen?_rename_some rightTyRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity rightTyRaw]
  split
  next noLeftTySuccess =>
    exact absurd (leftTyStrengthens.symm.trans noLeftTySuccess)
      (by intro contra; cases contra)
  next targetLeftTy leftTySuccess =>
    have leftTyEq : targetLeftTy = leftTy :=
      Option.some.inj (leftTySuccess.symm.trans leftTyStrengthens)
    subst leftTyEq
    split
    next noRightTySuccess =>
      exact absurd (rightTyStrengthens.symm.trans noRightTySuccess)
        (by intro contra; cases contra)
    next targetRightTy rightTySuccess =>
      have rightTyEq : targetRightTy = rightTy :=
        Option.some.inj (rightTySuccess.symm.trans rightTyStrengthens)
      subst rightTyEq
      split
      next noLeftRawSuccess =>
        exact absurd (leftRawStrengthens.symm.trans noLeftRawSuccess)
          (by intro contra; cases contra)
      next targetLeftTyRaw leftRawSuccess =>
        have leftRawEq : targetLeftTyRaw = leftTyRaw :=
          Option.some.inj (leftRawSuccess.symm.trans leftRawStrengthens)
        subst leftRawEq
        split
        next noRightRawSuccess =>
          exact absurd (rightRawStrengthens.symm.trans noRightRawSuccess)
            (by intro contra; cases contra)
        next targetRightTyRaw rightRawSuccess =>
          have rightRawEq : targetRightTyRaw = rightTyRaw :=
            Option.some.inj (rightRawSuccess.symm.trans rightRawStrengthens)
          subst rightRawEq
          split
          next noProofSuccess =>
            exact absurd (proofIH.symm.trans noProofSuccess)
              (by intro contra; cases contra)
          next proofResult proofSuccess =>
            have proofEq : proofResult =
                StrengtheningResult.fromRename forwardRename typedRenaming
                  renameInverse renameInverseLeft renameInverseInjects
                  proof :=
              Option.some.inj (proofSuccess.symm.trans proofIH)
            subst proofEq
            rfl

/-- HoTT-special strength-T1 case: `Term.uaIntroHet`.

Carries `innerLevel` + `innerLevelLt` value-shape + 4 RawTerm
payloads (carrierARaw, carrierBRaw, forwardRaw, backwardRaw at outer
`back`) + 2 implicit Ty payloads (carrierA, carrierB at outer
`back`) + 1 Term IH (equivWitness at `Ty.equiv carrierA carrierB`).
No cast on rename — result `Ty.id (Ty.universe ...)` renames
structurally. -/
theorem strengthenTyped?_rename_eq_uaIntroHet
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
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    {carrierA carrierB : Ty level sourceScope}
    (carrierARaw carrierBRaw : RawTerm sourceScope)
    {forwardRaw backwardRaw : RawTerm sourceScope}
    (equivWitness : Term sourceCtx (Ty.equiv carrierA carrierB)
                       (RawTerm.equivIntro forwardRaw backwardRaw))
    (equivIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming equivWitness)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            equivWitness)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.uaIntroHet (context := sourceCtx) innerLevel innerLevelLt
            carrierARaw carrierBRaw equivWitness))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.uaIntroHet (context := sourceCtx) innerLevel innerLevelLt
            carrierARaw carrierBRaw equivWitness)) := by
  dsimp only [Term.rename, partialStrengthenTyped?]
  have carrierAStrengthens :
      (carrierA.rename forwardRename).partialStrengthen? renameInverse
        = some carrierA := by
    rw [Ty.partialStrengthen?_rename_some carrierA forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity carrierA]
  have carrierBStrengthens :
      (carrierB.rename forwardRename).partialStrengthen? renameInverse
        = some carrierB := by
    rw [Ty.partialStrengthen?_rename_some carrierB forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity carrierB]
  have carrierARawStrengthens :
      (carrierARaw.rename forwardRename).partialStrengthen? renameInverse
        = some carrierARaw := by
    rw [RawTerm.partialStrengthen?_rename_some carrierARaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity carrierARaw]
  have carrierBRawStrengthens :
      (carrierBRaw.rename forwardRename).partialStrengthen? renameInverse
        = some carrierBRaw := by
    rw [RawTerm.partialStrengthen?_rename_some carrierBRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity carrierBRaw]
  have forwardStrengthens :
      (forwardRaw.rename forwardRename).partialStrengthen? renameInverse
        = some forwardRaw := by
    rw [RawTerm.partialStrengthen?_rename_some forwardRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity forwardRaw]
  have backwardStrengthens :
      (backwardRaw.rename forwardRename).partialStrengthen? renameInverse
        = some backwardRaw := by
    rw [RawTerm.partialStrengthen?_rename_some backwardRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity backwardRaw]
  split
  next noCarrierASuccess =>
    exact absurd (carrierAStrengthens.symm.trans noCarrierASuccess)
      (by intro contra; cases contra)
  next targetCarrierA carrierASuccess =>
    have carrierAEq : targetCarrierA = carrierA :=
      Option.some.inj (carrierASuccess.symm.trans carrierAStrengthens)
    subst carrierAEq
    split
    next noCarrierBSuccess =>
      exact absurd (carrierBStrengthens.symm.trans noCarrierBSuccess)
        (by intro contra; cases contra)
    next targetCarrierB carrierBSuccess =>
      have carrierBEq : targetCarrierB = carrierB :=
        Option.some.inj (carrierBSuccess.symm.trans carrierBStrengthens)
      subst carrierBEq
      split
      next noCarrierARawSuccess =>
        exact absurd (carrierARawStrengthens.symm.trans noCarrierARawSuccess)
          (by intro contra; cases contra)
      next targetCarrierARaw carrierARawSuccess =>
        have carrierARawEq : targetCarrierARaw = carrierARaw :=
          Option.some.inj
            (carrierARawSuccess.symm.trans carrierARawStrengthens)
        subst carrierARawEq
        split
        next noCarrierBRawSuccess =>
          exact absurd
            (carrierBRawStrengthens.symm.trans noCarrierBRawSuccess)
            (by intro contra; cases contra)
        next targetCarrierBRaw carrierBRawSuccess =>
          have carrierBRawEq : targetCarrierBRaw = carrierBRaw :=
            Option.some.inj
              (carrierBRawSuccess.symm.trans carrierBRawStrengthens)
          subst carrierBRawEq
          split
          next noForwardSuccess =>
            exact absurd (forwardStrengthens.symm.trans noForwardSuccess)
              (by intro contra; cases contra)
          next targetForwardRaw forwardSuccess =>
            have forwardEq : targetForwardRaw = forwardRaw :=
              Option.some.inj (forwardSuccess.symm.trans forwardStrengthens)
            subst forwardEq
            split
            next noBackwardSuccess =>
              exact absurd
                (backwardStrengthens.symm.trans noBackwardSuccess)
                (by intro contra; cases contra)
            next targetBackwardRaw backwardSuccess =>
              have backwardEq : targetBackwardRaw = backwardRaw :=
                Option.some.inj
                  (backwardSuccess.symm.trans backwardStrengthens)
              subst backwardEq
              split
              next noEquivSuccess =>
                exact absurd (equivIH.symm.trans noEquivSuccess)
                  (by intro contra; cases contra)
              next equivResult equivSuccess =>
                have equivEq : equivResult =
                    StrengtheningResult.fromRename forwardRename
                      typedRenaming renameInverse renameInverseLeft
                      renameInverseInjects equivWitness :=
                  Option.some.inj (equivSuccess.symm.trans equivIH)
                subst equivEq
                rfl

/-- HoTT-special strength-T1 case: `Term.funextIntroHet`.

VALUE-shaped ctor (no Term IH).  Carries 2 outer Ty payloads
(domainType, codomainType at `back`) + 2 binder-shape RawTerm
payloads (applyARaw, applyBRaw under one binder via `back.lift`).
No cast on rename — the Ty.id wrapping Ty.arrow renames structurally
since no binder shift. -/
theorem strengthenTyped?_rename_eq_funextIntroHet
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
    (applyARaw applyBRaw : RawTerm (sourceScope + 1)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.funextIntroHet (context := sourceCtx) domainType codomainType
            applyARaw applyBRaw))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.funextIntroHet (context := sourceCtx) domainType codomainType
            applyARaw applyBRaw)) := by
  dsimp only [Term.rename, partialStrengthenTyped?]
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
  have applyAStrengthens :
      (applyARaw.rename forwardRename.lift).partialStrengthen?
          renameInverse.lift
        = some applyARaw := by
    rw [RawTerm.partialStrengthen?_rename_some applyARaw
      forwardRename.lift (@RawRenaming.identity sourceScope).lift
      renameInverse.lift
      (PartialRawRenaming.lift_rename_some renameInverseLeft),
      RawTerm.rename_pointwise
        (@RawRenaming.identity_lift_pointwise sourceScope) applyARaw,
      RawTerm.rename_identity applyARaw]
  have applyBStrengthens :
      (applyBRaw.rename forwardRename.lift).partialStrengthen?
          renameInverse.lift
        = some applyBRaw := by
    rw [RawTerm.partialStrengthen?_rename_some applyBRaw
      forwardRename.lift (@RawRenaming.identity sourceScope).lift
      renameInverse.lift
      (PartialRawRenaming.lift_rename_some renameInverseLeft),
      RawTerm.rename_pointwise
        (@RawRenaming.identity_lift_pointwise sourceScope) applyBRaw,
      RawTerm.rename_identity applyBRaw]
  split
  next noDomainSuccess =>
    exact absurd (domainStrengthens.symm.trans noDomainSuccess)
      (by intro contra; cases contra)
  next targetDomainType domainSuccess =>
    have domainEq : targetDomainType = domainType :=
      Option.some.inj (domainSuccess.symm.trans domainStrengthens)
    subst domainEq
    split
    next noCodomainSuccess =>
      exact absurd (codomainStrengthens.symm.trans noCodomainSuccess)
        (by intro contra; cases contra)
    next targetCodomainType codomainSuccess =>
      have codomainEq : targetCodomainType = codomainType :=
        Option.some.inj (codomainSuccess.symm.trans codomainStrengthens)
      subst codomainEq
      split
      next noApplyASuccess =>
        exact absurd (applyAStrengthens.symm.trans noApplyASuccess)
          (by intro contra; cases contra)
      next targetApplyARaw applyASuccess =>
        have applyAEq : targetApplyARaw = applyARaw :=
          Option.some.inj (applyASuccess.symm.trans applyAStrengthens)
        subst applyAEq
        split
        next noApplyBSuccess =>
          exact absurd (applyBStrengthens.symm.trans noApplyBSuccess)
            (by intro contra; cases contra)
        next targetApplyBRaw applyBSuccess =>
          have applyBEq : targetApplyBRaw = applyBRaw :=
            Option.some.inj (applyBSuccess.symm.trans applyBStrengthens)
          subst applyBEq
          rfl

end Term

end LeanFX2
