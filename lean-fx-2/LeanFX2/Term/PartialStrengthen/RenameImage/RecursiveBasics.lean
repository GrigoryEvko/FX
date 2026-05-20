import LeanFX2.Term.PartialStrengthen.RenameImage.UnaryStructured

/-! # Term/PartialStrengthen/RenameImage/RecursiveBasics

Rename-image T1 equations for list construction, natural eliminators, and
non-dependent application.
-/

namespace LeanFX2

namespace Term

/-- 2-IH non-binder strength-T1 case: `Term.listCons`.

Combines a head Term IH (at `elementType`) with a tail Term IH (at
`Ty.listType elementType`).  No Ty witnesses needed: the dispatcher
recurses directly via `partialStrengthenTypedListCons`. -/
theorem strengthenTyped?_rename_eq_listCons
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
    {elementType : Ty level sourceScope}
    {headRaw tailRaw : RawTerm sourceScope}
    (headTerm : Term sourceCtx elementType headRaw)
    (tailTerm : Term sourceCtx (Ty.listType elementType) tailRaw)
    (headIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming headTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            headTerm))
    (tailIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming tailTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            tailTerm)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming (Term.listCons headTerm tailTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.listCons headTerm tailTerm)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  split
  next noHeadSuccess =>
    exact absurd (headIH.symm.trans noHeadSuccess)
      (by intro contra; cases contra)
  next headResult headSuccess =>
    have headEq : headResult =
        StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects headTerm :=
      Option.some.inj (headSuccess.symm.trans headIH)
    subst headEq
    split
    next noTailSuccess =>
      exact absurd (tailIH.symm.trans noTailSuccess)
        (by intro contra; cases contra)
    next tailResult tailSuccess =>
      have tailEq : tailResult =
          StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects tailTerm :=
        Option.some.inj (tailSuccess.symm.trans tailIH)
      subst tailEq
      rfl

/-- 3-IH non-binder strength-T1 case: `Term.natElim`.

Carries three Term IHs (scrutinee at `Ty.nat`, zero-branch at motive,
succ-branch at `Ty.arrow Ty.nat motive`).  The motiveType is closed —
the dispatcher does not strengthen it directly here; the term's typing
carries it.  No Ty witnesses required. -/
theorem strengthenTyped?_rename_eq_natElim
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
    {motiveType : Ty level sourceScope}
    {scrutineeRaw zeroRaw succRaw : RawTerm sourceScope}
    (scrutinee : Term sourceCtx Ty.nat scrutineeRaw)
    (zeroBranch : Term sourceCtx motiveType zeroRaw)
    (succBranch : Term sourceCtx (Ty.arrow Ty.nat motiveType) succRaw)
    (scrutineeIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming scrutinee)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            scrutinee))
    (zeroIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming zeroBranch)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            zeroBranch))
    (succIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming succBranch)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            succBranch)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.natElim scrutinee zeroBranch succBranch))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.natElim scrutinee zeroBranch succBranch)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
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
    next noZeroSuccess =>
      exact absurd (zeroIH.symm.trans noZeroSuccess)
        (by intro contra; cases contra)
    next zeroResult zeroSuccess =>
      have zeroEq : zeroResult =
          StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects zeroBranch :=
        Option.some.inj (zeroSuccess.symm.trans zeroIH)
      subst zeroEq
      split
      next noSuccSuccess =>
        exact absurd (succIH.symm.trans noSuccSuccess)
          (by intro contra; cases contra)
      next succResult succSuccess =>
        have succEq : succResult =
            StrengtheningResult.fromRename forwardRename typedRenaming
              renameInverse renameInverseLeft renameInverseInjects succBranch :=
          Option.some.inj (succSuccess.symm.trans succIH)
        subst succEq
        rfl

/-- 3-IH non-binder strength-T1 case: `Term.natRec`.

Mirror of `natElim` with the binary-succ branch (recursive carrier).
Same dispatcher shape — three Term IHs, no Ty witnesses. -/
theorem strengthenTyped?_rename_eq_natRec
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
    {motiveType : Ty level sourceScope}
    {scrutineeRaw zeroRaw succRaw : RawTerm sourceScope}
    (scrutinee : Term sourceCtx Ty.nat scrutineeRaw)
    (zeroBranch : Term sourceCtx motiveType zeroRaw)
    (succBranch :
      Term sourceCtx (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType))
        succRaw)
    (scrutineeIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming scrutinee)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            scrutinee))
    (zeroIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming zeroBranch)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            zeroBranch))
    (succIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming succBranch)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            succBranch)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.natRec scrutinee zeroBranch succBranch))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.natRec scrutinee zeroBranch succBranch)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
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
    next noZeroSuccess =>
      exact absurd (zeroIH.symm.trans noZeroSuccess)
        (by intro contra; cases contra)
    next zeroResult zeroSuccess =>
      have zeroEq : zeroResult =
          StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects zeroBranch :=
        Option.some.inj (zeroSuccess.symm.trans zeroIH)
      subst zeroEq
      split
      next noSuccSuccess =>
        exact absurd (succIH.symm.trans noSuccSuccess)
          (by intro contra; cases contra)
      next succResult succSuccess =>
        have succEq : succResult =
            StrengtheningResult.fromRename forwardRename typedRenaming
              renameInverse renameInverseLeft renameInverseInjects succBranch :=
          Option.some.inj (succSuccess.symm.trans succIH)
        subst succEq
        rfl

/-- 2-IH non-binder strength-T1 case: `Term.app`.

Non-dep function application: domainType and codomainType are both
unbinder.  Combines two Ty witnesses (domain, codomain) with two Term
IHs (function, argument).  Dispatcher delegates through
`partialStrengthenTypedApp` and its `AppOfSuccess` two-stage helper —
the `subst` pattern propagates equalities through both layers. -/
theorem strengthenTyped?_rename_eq_app
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
    {functionRaw argumentRaw : RawTerm sourceScope}
    (functionTerm :
      Term sourceCtx (Ty.arrow domainType codomainType) functionRaw)
    (argumentTerm : Term sourceCtx domainType argumentRaw)
    (functionIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming functionTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            functionTerm))
    (argumentIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming argumentTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            argumentTerm)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming (Term.app functionTerm argumentTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.app functionTerm argumentTerm)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
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
      next noFunctionSuccess =>
        exact absurd (functionIH.symm.trans noFunctionSuccess)
          (by intro contra; cases contra)
      next functionResult functionSuccess =>
        have functionEq : functionResult =
            StrengtheningResult.fromRename forwardRename typedRenaming
              renameInverse renameInverseLeft renameInverseInjects
              functionTerm :=
          Option.some.inj (functionSuccess.symm.trans functionIH)
        subst functionEq
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

end Term

end LeanFX2
