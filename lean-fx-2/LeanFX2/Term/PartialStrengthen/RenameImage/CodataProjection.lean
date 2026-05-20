import LeanFX2.Term.PartialStrengthen.RenameImage.TypeCodes

/-! # Term/PartialStrengthen/RenameImage/CodataProjection

Rename-image T1 equations for codata unfolding and sigma projection cases.
-/

namespace LeanFX2

namespace Term

/-- HoTT-special strength-T1 case: `Term.codataUnfold`.

Codata constructor: 1 implicit Ty payload (outputType) at outer
`back` + 2 Term IHs (initialState at `stateType` + transition at
`Ty.arrow stateType outputType`).  `stateType` is also implicit but
the dispatcher only strengthens `outputType`. -/
theorem strengthenTyped?_rename_eq_codataUnfold
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
    {stateType outputType : Ty level sourceScope}
    {stateRaw transitionRaw : RawTerm sourceScope}
    (initialState : Term sourceCtx stateType stateRaw)
    (transition : Term sourceCtx (Ty.arrow stateType outputType) transitionRaw)
    (stateIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming initialState)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            initialState))
    (transitionIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming transition)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            transition)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.codataUnfold (context := sourceCtx) initialState transition))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.codataUnfold (context := sourceCtx) initialState
            transition)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have outputStrengthens :
      (outputType.rename forwardRename).partialStrengthen? renameInverse
        = some outputType := by
    rw [Ty.partialStrengthen?_rename_some outputType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity outputType]
  split
  next noOutputSuccess =>
    exact absurd (outputStrengthens.symm.trans noOutputSuccess)
      (by intro contra; cases contra)
  next targetOutputType outputSuccess =>
    have outputEq : targetOutputType = outputType :=
      Option.some.inj (outputSuccess.symm.trans outputStrengthens)
    subst outputEq
    split
    next noStateSuccess =>
      exact absurd (stateIH.symm.trans noStateSuccess)
        (by intro contra; cases contra)
    next stateResult stateSuccess =>
      have stateEq : stateResult =
          StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            initialState :=
        Option.some.inj (stateSuccess.symm.trans stateIH)
      subst stateEq
      split
      next noTransitionSuccess =>
        exact absurd (transitionIH.symm.trans noTransitionSuccess)
          (by intro contra; cases contra)
      next transitionResult transitionSuccess =>
        have transitionEq : transitionResult =
            StrengtheningResult.fromRename forwardRename typedRenaming
              renameInverse renameInverseLeft renameInverseInjects
              transition :=
          Option.some.inj (transitionSuccess.symm.trans transitionIH)
        subst transitionEq
        rfl

/-- Binder-Ty strength-T1 case: `Term.fst`.

Carries 2 Ty payloads (firstType at outer `back`, secondType at
`back.lift` under one binder) + 1 Term IH (pairTerm at
`Ty.sigmaTy firstType secondType`).  The codomain Ty `secondType`
uses the same `rho.lift` survival recipe as `piTyCode` but lifted
to the Ty layer via `Ty.partialStrengthen?_rename_some`. -/
theorem strengthenTyped?_rename_eq_fst
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
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {pairRaw : RawTerm sourceScope}
    (pairTerm : Term sourceCtx (Ty.sigmaTy firstType secondType) pairRaw)
    (pairIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming pairTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            pairTerm)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming (Term.fst pairTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.fst pairTerm)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have firstStrengthens :
      (firstType.rename forwardRename).partialStrengthen? renameInverse
        = some firstType := by
    rw [Ty.partialStrengthen?_rename_some firstType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity firstType]
  have secondStrengthens :
      (secondType.rename forwardRename.lift).partialStrengthen?
          renameInverse.lift
        = some secondType := by
    rw [Ty.partialStrengthen?_rename_some secondType
      forwardRename.lift (@RawRenaming.identity sourceScope).lift
      renameInverse.lift
      (PartialRawRenaming.lift_rename_some renameInverseLeft),
      Ty.rename_pointwise
        (@RawRenaming.identity_lift_pointwise sourceScope) secondType,
      Ty.rename_identity secondType]
  split
  next noFirstSuccess =>
    exact absurd (firstStrengthens.symm.trans noFirstSuccess)
      (by intro contra; cases contra)
  next targetFirstType firstSuccess =>
    have firstEq : targetFirstType = firstType :=
      Option.some.inj (firstSuccess.symm.trans firstStrengthens)
    subst firstEq
    split
    next noSecondSuccess =>
      exact absurd (secondStrengthens.symm.trans noSecondSuccess)
        (by intro contra; cases contra)
    next targetSecondType secondSuccess =>
      have secondEq : targetSecondType = secondType :=
        Option.some.inj (secondSuccess.symm.trans secondStrengthens)
      subst secondEq
      split
      next noPairSuccess =>
        exact absurd (pairIH.symm.trans noPairSuccess)
          (by intro contra; cases contra)
      next pairResult pairSuccess =>
        have pairEq : pairResult =
            StrengtheningResult.fromRename forwardRename typedRenaming
              renameInverse renameInverseLeft renameInverseInjects
              pairTerm :=
          Option.some.inj (pairSuccess.symm.trans pairIH)
        subst pairEq
        rfl

end Term

end LeanFX2
