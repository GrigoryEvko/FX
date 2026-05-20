import LeanFX2.Term.PartialStrengthen.RenameImage.RecursiveBasics

/-! # Term/PartialStrengthen/RenameImage/RecursiveMatches

Rename-image T1 equations for list, option, and either eliminator cases.
-/

namespace LeanFX2

namespace Term

/-- 3-IH non-binder strength-T1 case: `Term.listElim`.

Combines an elementType Ty witness (unbinder) with three Term IHs
(scrutinee at `Ty.listType`, nil-branch at motive, cons-branch at
the nested arrow).  The dispatcher delegates through
`partialStrengthenTypedListElim` which uses a `ListElimOfSuccess`
two-stage helper — `subst` rewrites through both layers cleanly. -/
theorem strengthenTyped?_rename_eq_listElim
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
    {elementType motiveType : Ty level sourceScope}
    {scrutineeRaw nilRaw consRaw : RawTerm sourceScope}
    (scrutinee : Term sourceCtx (Ty.listType elementType) scrutineeRaw)
    (nilBranch : Term sourceCtx motiveType nilRaw)
    (consBranch :
      Term sourceCtx
        (Ty.arrow elementType (Ty.arrow (Ty.listType elementType) motiveType))
        consRaw)
    (scrutineeIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming scrutinee)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            scrutinee))
    (nilIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming nilBranch)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            nilBranch))
    (consIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming consBranch)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            consBranch)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.listElim scrutinee nilBranch consBranch))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.listElim scrutinee nilBranch consBranch)) := by
  dsimp only [Term.rename, partialStrengthenTyped?]
  have elementStrengthens :
      (elementType.rename forwardRename).partialStrengthen? renameInverse
        = some elementType := by
    rw [Ty.partialStrengthen?_rename_some elementType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity elementType]
  split
  next noElementSuccess =>
    exact absurd (elementStrengthens.symm.trans noElementSuccess)
      (by intro contra; cases contra)
  next targetElementType elementSuccess =>
    have elementEq : targetElementType = elementType :=
      Option.some.inj (elementSuccess.symm.trans elementStrengthens)
    subst elementEq
    split
    next noScrutSuccess =>
      exact absurd (scrutineeIH.symm.trans noScrutSuccess)
        (by intro contra; cases contra)
    next scrutResult scrutSuccess =>
      have scrutEq : scrutResult =
          StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects scrutinee :=
        Option.some.inj (scrutSuccess.symm.trans scrutineeIH)
      subst scrutEq
      split
      next noNilSuccess =>
        exact absurd (nilIH.symm.trans noNilSuccess)
          (by intro contra; cases contra)
      next nilResult nilSuccess =>
        have nilEq : nilResult =
            StrengtheningResult.fromRename forwardRename typedRenaming
              renameInverse renameInverseLeft renameInverseInjects nilBranch :=
          Option.some.inj (nilSuccess.symm.trans nilIH)
        subst nilEq
        split
        next noConsSuccess =>
          exact absurd (consIH.symm.trans noConsSuccess)
            (by intro contra; cases contra)
        next consResult consSuccess =>
          have consEq : consResult =
              StrengtheningResult.fromRename forwardRename typedRenaming
                renameInverse renameInverseLeft renameInverseInjects
                consBranch :=
            Option.some.inj (consSuccess.symm.trans consIH)
          subst consEq
          rfl

/-- 3-IH non-binder strength-T1 case: `Term.optionMatch`.

Combines an elementType Ty witness with three Term IHs (scrutinee at
`Ty.optionType`, none-branch at motive, some-branch at the arrow
`elementType -> motive`).  Same shape as `listElim`. -/
theorem strengthenTyped?_rename_eq_optionMatch
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
    {elementType motiveType : Ty level sourceScope}
    {scrutineeRaw noneRaw someRaw : RawTerm sourceScope}
    (scrutinee : Term sourceCtx (Ty.optionType elementType) scrutineeRaw)
    (noneBranch : Term sourceCtx motiveType noneRaw)
    (someBranch :
      Term sourceCtx (Ty.arrow elementType motiveType) someRaw)
    (scrutineeIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming scrutinee)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            scrutinee))
    (noneIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming noneBranch)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            noneBranch))
    (someIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming someBranch)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            someBranch)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.optionMatch scrutinee noneBranch someBranch))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.optionMatch scrutinee noneBranch someBranch)) := by
  dsimp only [Term.rename, partialStrengthenTyped?]
  have elementStrengthens :
      (elementType.rename forwardRename).partialStrengthen? renameInverse
        = some elementType := by
    rw [Ty.partialStrengthen?_rename_some elementType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity elementType]
  split
  next noElementSuccess =>
    exact absurd (elementStrengthens.symm.trans noElementSuccess)
      (by intro contra; cases contra)
  next targetElementType elementSuccess =>
    have elementEq : targetElementType = elementType :=
      Option.some.inj (elementSuccess.symm.trans elementStrengthens)
    subst elementEq
    split
    next noScrutSuccess =>
      exact absurd (scrutineeIH.symm.trans noScrutSuccess)
        (by intro contra; cases contra)
    next scrutResult scrutSuccess =>
      have scrutEq : scrutResult =
          StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects scrutinee :=
        Option.some.inj (scrutSuccess.symm.trans scrutineeIH)
      subst scrutEq
      split
      next noNoneSuccess =>
        exact absurd (noneIH.symm.trans noNoneSuccess)
          (by intro contra; cases contra)
      next noneResult noneSuccess =>
        have noneEq : noneResult =
            StrengtheningResult.fromRename forwardRename typedRenaming
              renameInverse renameInverseLeft renameInverseInjects
              noneBranch :=
          Option.some.inj (noneSuccess.symm.trans noneIH)
        subst noneEq
        split
        next noSomeSuccess =>
          exact absurd (someIH.symm.trans noSomeSuccess)
            (by intro contra; cases contra)
        next someResult someSuccess =>
          have someEq : someResult =
              StrengtheningResult.fromRename forwardRename typedRenaming
                renameInverse renameInverseLeft renameInverseInjects
                someBranch :=
            Option.some.inj (someSuccess.symm.trans someIH)
          subst someEq
          rfl

/-- 3-IH non-binder strength-T1 case: `Term.eitherMatch`.

Combines THREE Ty witnesses (leftType, rightType, motiveType — all
unbinder) with three Term IHs (scrutinee, leftBranch, rightBranch).
Six sequential subst-via-witness blocks; the longest atomic ctor in
the strength-T1 cascade. -/
theorem strengthenTyped?_rename_eq_eitherMatch
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
    {leftType rightType motiveType : Ty level sourceScope}
    {scrutineeRaw leftRaw rightRaw : RawTerm sourceScope}
    (scrutinee :
      Term sourceCtx (Ty.eitherType leftType rightType) scrutineeRaw)
    (leftBranch : Term sourceCtx (Ty.arrow leftType motiveType) leftRaw)
    (rightBranch : Term sourceCtx (Ty.arrow rightType motiveType) rightRaw)
    (scrutineeIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming scrutinee)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            scrutinee))
    (leftIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming leftBranch)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            leftBranch))
    (rightIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming rightBranch)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            rightBranch)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.eitherMatch scrutinee leftBranch rightBranch))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.eitherMatch scrutinee leftBranch rightBranch)) := by
  dsimp only [Term.rename, partialStrengthenTyped?]
  have leftTypeStrengthens :
      (leftType.rename forwardRename).partialStrengthen? renameInverse
        = some leftType := by
    rw [Ty.partialStrengthen?_rename_some leftType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity leftType]
  have rightTypeStrengthens :
      (rightType.rename forwardRename).partialStrengthen? renameInverse
        = some rightType := by
    rw [Ty.partialStrengthen?_rename_some rightType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity rightType]
  have motiveTypeStrengthens :
      (motiveType.rename forwardRename).partialStrengthen? renameInverse
        = some motiveType := by
    rw [Ty.partialStrengthen?_rename_some motiveType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity motiveType]
  split
  next noLeftSuccess =>
    exact absurd (leftTypeStrengthens.symm.trans noLeftSuccess)
      (by intro contra; cases contra)
  next targetLeftType leftSuccess =>
    have leftEq : targetLeftType = leftType :=
      Option.some.inj (leftSuccess.symm.trans leftTypeStrengthens)
    subst leftEq
    split
    next noRightSuccess =>
      exact absurd (rightTypeStrengthens.symm.trans noRightSuccess)
        (by intro contra; cases contra)
    next targetRightType rightSuccess =>
      have rightEq : targetRightType = rightType :=
        Option.some.inj (rightSuccess.symm.trans rightTypeStrengthens)
      subst rightEq
      split
      next noMotiveSuccess =>
        exact absurd (motiveTypeStrengthens.symm.trans noMotiveSuccess)
          (by intro contra; cases contra)
      next targetMotiveType motiveSuccess =>
        have motiveEq : targetMotiveType = motiveType :=
          Option.some.inj (motiveSuccess.symm.trans motiveTypeStrengthens)
        subst motiveEq
        split
        next noScrutSuccess =>
          exact absurd (scrutineeIH.symm.trans noScrutSuccess)
            (by intro contra; cases contra)
        next scrutResult scrutSuccess =>
          have scrutEq : scrutResult =
              StrengtheningResult.fromRename forwardRename typedRenaming
                renameInverse renameInverseLeft renameInverseInjects
                scrutinee :=
            Option.some.inj (scrutSuccess.symm.trans scrutineeIH)
          subst scrutEq
          split
          next noLeftBranchSuccess =>
            exact absurd (leftIH.symm.trans noLeftBranchSuccess)
              (by intro contra; cases contra)
          next leftResult leftBranchSuccess =>
            have leftBranchEq : leftResult =
                StrengtheningResult.fromRename forwardRename typedRenaming
                  renameInverse renameInverseLeft renameInverseInjects
                  leftBranch :=
              Option.some.inj (leftBranchSuccess.symm.trans leftIH)
            subst leftBranchEq
            split
            next noRightBranchSuccess =>
              exact absurd (rightIH.symm.trans noRightBranchSuccess)
                (by intro contra; cases contra)
            next rightResult rightBranchSuccess =>
              have rightBranchEq : rightResult =
                  StrengtheningResult.fromRename forwardRename typedRenaming
                    renameInverse renameInverseLeft renameInverseInjects
                    rightBranch :=
                Option.some.inj (rightBranchSuccess.symm.trans rightIH)
              subst rightBranchEq
              rfl

end Term

end LeanFX2
