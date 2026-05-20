import LeanFX2.Term.StrengtheningImage.RenameImageUnary

/-! # Term/StrengtheningImage/RenameImageRecursive

Rename-image success bridges for recursive list, eliminator, application, and interval constructors.
-/

namespace LeanFX2

namespace Term

private abbrev renamingStrengthening
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
        targetPosition = forwardRename sourcePosition) :
    ContextStrengthening targetCtx sourceCtx :=
  ContextStrengthening.ofRenaming forwardRename typedRenaming
    renameInverse renameInverseLeft renameInverseInjects

private theorem option_isSome_false_of_eq_none
    {SomeType : Type} {optionValue : Option SomeType}
    (optionNone : optionValue = none)
    (optionIsSome : optionValue.isSome = true) :
    False := by
  rw [optionNone] at optionIsSome
  cases optionIsSome

private theorem option_some_ne_none {SomeType : Type} {someValue : SomeType} :
    ¬ some someValue = none := by
  intro contradiction
  cases contradiction

private theorem ty_partialStrengthen_rename_some
    {level sourceScope targetScope : Nat}
    (sourceType : Ty level sourceScope)
    (forwardRename : RawRenaming sourceScope targetScope)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition) :
    (sourceType.rename forwardRename).partialStrengthen? renameInverse =
      some sourceType := by
  rw [Ty.partialStrengthen?_rename_some sourceType forwardRename
    (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
    Ty.rename_identity sourceType]

/-- T3 reverse-image induction step for `Term.listCons`, consuming only
child `.isSome` witnesses. -/
theorem strengthenTyped?_rename_isSome_listCons_of_childIsSome
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
    (headIsSome :
      (partialStrengthenTyped?
          (Term.rename typedRenaming headTerm)
          (renamingStrengthening forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true)
    (tailIsSome :
      (partialStrengthenTyped?
          (Term.rename typedRenaming tailTerm)
          (renamingStrengthening forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.listCons headTerm tailTerm))
        (renamingStrengthening forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true := by
  dsimp only [renamingStrengthening, ContextStrengthening.ofRenaming] at *
  dsimp only [Term.rename, partialStrengthenTyped?]
  split
  next noHeadSuccess =>
    exact False.elim
      (option_isSome_false_of_eq_none noHeadSuccess headIsSome)
  next headResult headSuccess =>
    split
    next noTailSuccess =>
      exact False.elim
        (option_isSome_false_of_eq_none noTailSuccess tailIsSome)
    next tailResult tailSuccess =>
      rfl

/-- T3 reverse-image induction step for `Term.listCons`. -/
theorem strengthenTyped?_rename_isSome_listCons
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
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.listCons headTerm tailTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  strengthenTyped?_rename_isSome_listCons_of_childIsSome forwardRename
    typedRenaming renameInverse renameInverseLeft renameInverseInjects
    headTerm tailTerm (option_isSome_of_eq_some headIH)
    (option_isSome_of_eq_some tailIH)

/-- T3 reverse-image induction step for `Term.natElim`, consuming only
child `.isSome` witnesses. -/
theorem strengthenTyped?_rename_isSome_natElim_of_childIsSome
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
    (scrutineeIsSome :
      (partialStrengthenTyped?
          (Term.rename typedRenaming scrutinee)
          (renamingStrengthening forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true)
    (zeroIsSome :
      (partialStrengthenTyped?
          (Term.rename typedRenaming zeroBranch)
          (renamingStrengthening forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true)
    (succIsSome :
      (partialStrengthenTyped?
          (Term.rename typedRenaming succBranch)
          (renamingStrengthening forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.natElim scrutinee zeroBranch succBranch))
        (renamingStrengthening forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true := by
  dsimp only [renamingStrengthening, ContextStrengthening.ofRenaming] at *
  dsimp only [Term.rename, partialStrengthenTyped?]
  split
  next noScrutSuccess =>
    exact False.elim
      (option_isSome_false_of_eq_none noScrutSuccess scrutineeIsSome)
  next scrutResult scrutSuccess =>
    split
    next noZeroSuccess =>
      exact False.elim
        (option_isSome_false_of_eq_none noZeroSuccess zeroIsSome)
    next zeroResult zeroSuccess =>
      split
      next noSuccSuccess =>
        exact False.elim
          (option_isSome_false_of_eq_none noSuccSuccess succIsSome)
      next succResult succSuccess =>
        rfl

/-- T3 reverse-image induction step for `Term.natElim`. -/
theorem strengthenTyped?_rename_isSome_natElim
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
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.natElim scrutinee zeroBranch succBranch))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  strengthenTyped?_rename_isSome_natElim_of_childIsSome forwardRename
    typedRenaming renameInverse renameInverseLeft renameInverseInjects
    scrutinee zeroBranch succBranch (option_isSome_of_eq_some scrutineeIH)
    (option_isSome_of_eq_some zeroIH) (option_isSome_of_eq_some succIH)

/-- T3 reverse-image induction step for `Term.natRec`, consuming only
child `.isSome` witnesses. -/
theorem strengthenTyped?_rename_isSome_natRec_of_childIsSome
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
    (scrutineeIsSome :
      (partialStrengthenTyped?
          (Term.rename typedRenaming scrutinee)
          (renamingStrengthening forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true)
    (zeroIsSome :
      (partialStrengthenTyped?
          (Term.rename typedRenaming zeroBranch)
          (renamingStrengthening forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true)
    (succIsSome :
      (partialStrengthenTyped?
          (Term.rename typedRenaming succBranch)
          (renamingStrengthening forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.natRec scrutinee zeroBranch succBranch))
        (renamingStrengthening forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true := by
  dsimp only [renamingStrengthening, ContextStrengthening.ofRenaming] at *
  dsimp only [Term.rename, partialStrengthenTyped?]
  split
  next noScrutSuccess =>
    exact False.elim
      (option_isSome_false_of_eq_none noScrutSuccess scrutineeIsSome)
  next scrutResult scrutSuccess =>
    split
    next noZeroSuccess =>
      exact False.elim
        (option_isSome_false_of_eq_none noZeroSuccess zeroIsSome)
    next zeroResult zeroSuccess =>
      split
      next noSuccSuccess =>
        exact False.elim
          (option_isSome_false_of_eq_none noSuccSuccess succIsSome)
      next succResult succSuccess =>
        rfl

/-- T3 reverse-image induction step for `Term.natRec`. -/
theorem strengthenTyped?_rename_isSome_natRec
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
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.natRec scrutinee zeroBranch succBranch))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  strengthenTyped?_rename_isSome_natRec_of_childIsSome forwardRename
    typedRenaming renameInverse renameInverseLeft renameInverseInjects
    scrutinee zeroBranch succBranch (option_isSome_of_eq_some scrutineeIH)
    (option_isSome_of_eq_some zeroIH) (option_isSome_of_eq_some succIH)

/-- T3 reverse-image induction step for `Term.app`, consuming only child
`.isSome` witnesses. -/
theorem strengthenTyped?_rename_isSome_app_of_childIsSome
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
    (functionIsSome :
      (partialStrengthenTyped?
          (Term.rename typedRenaming functionTerm)
          (renamingStrengthening forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true)
    (argumentIsSome :
      (partialStrengthenTyped?
          (Term.rename typedRenaming argumentTerm)
          (renamingStrengthening forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.app functionTerm argumentTerm))
        (renamingStrengthening forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true := by
  dsimp only [renamingStrengthening, ContextStrengthening.ofRenaming] at *
  dsimp only [Term.rename, partialStrengthenTyped?]
  have domainStrengthens :
      (domainType.rename forwardRename).partialStrengthen? renameInverse =
        some domainType :=
    ty_partialStrengthen_rename_some domainType forwardRename
      renameInverse renameInverseLeft
  have codomainStrengthens :
      (codomainType.rename forwardRename).partialStrengthen? renameInverse =
        some codomainType :=
    ty_partialStrengthen_rename_some codomainType forwardRename
      renameInverse renameInverseLeft
  split
  next noDomainSuccess =>
    exact False.elim
      (option_some_ne_none (domainStrengthens.symm.trans noDomainSuccess))
  next targetDomainType domainSuccess =>
    split
    next noCodomainSuccess =>
      exact False.elim
        (option_some_ne_none
          (codomainStrengthens.symm.trans noCodomainSuccess))
    next targetCodomainType codomainSuccess =>
      split
      next noFunctionSuccess =>
        exact False.elim
          (option_isSome_false_of_eq_none noFunctionSuccess functionIsSome)
      next functionResult functionSuccess =>
        split
        next noArgumentSuccess =>
          exact False.elim
            (option_isSome_false_of_eq_none noArgumentSuccess argumentIsSome)
        next argumentResult argumentSuccess =>
          rfl

/-- T3 reverse-image induction step for `Term.app`. -/
theorem strengthenTyped?_rename_isSome_app
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
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.app functionTerm argumentTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  strengthenTyped?_rename_isSome_app_of_childIsSome forwardRename
    typedRenaming renameInverse renameInverseLeft renameInverseInjects
    functionTerm argumentTerm (option_isSome_of_eq_some functionIH)
    (option_isSome_of_eq_some argumentIH)

/-- T3 reverse-image induction step for `Term.listElim`, consuming only
child `.isSome` witnesses. -/
theorem strengthenTyped?_rename_isSome_listElim_of_childIsSome
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
    (scrutineeIsSome :
      (partialStrengthenTyped?
          (Term.rename typedRenaming scrutinee)
          (renamingStrengthening forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true)
    (nilIsSome :
      (partialStrengthenTyped?
          (Term.rename typedRenaming nilBranch)
          (renamingStrengthening forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true)
    (consIsSome :
      (partialStrengthenTyped?
          (Term.rename typedRenaming consBranch)
          (renamingStrengthening forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.listElim scrutinee nilBranch consBranch))
        (renamingStrengthening forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true := by
  dsimp only [renamingStrengthening, ContextStrengthening.ofRenaming] at *
  dsimp only [Term.rename, partialStrengthenTyped?]
  have elementStrengthens :
      (elementType.rename forwardRename).partialStrengthen? renameInverse =
        some elementType :=
    ty_partialStrengthen_rename_some elementType forwardRename
      renameInverse renameInverseLeft
  split
  next noElementSuccess =>
    exact False.elim
      (option_some_ne_none (elementStrengthens.symm.trans noElementSuccess))
  next targetElementType elementSuccess =>
    split
    next noScrutSuccess =>
      exact False.elim
        (option_isSome_false_of_eq_none noScrutSuccess scrutineeIsSome)
    next scrutResult scrutSuccess =>
      split
      next noNilSuccess =>
        exact False.elim
          (option_isSome_false_of_eq_none noNilSuccess nilIsSome)
      next nilResult nilSuccess =>
        split
        next noConsSuccess =>
          exact False.elim
            (option_isSome_false_of_eq_none noConsSuccess consIsSome)
        next consResult consSuccess =>
          rfl

/-- T3 reverse-image induction step for `Term.listElim`. -/
theorem strengthenTyped?_rename_isSome_listElim
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
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.listElim scrutinee nilBranch consBranch))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  strengthenTyped?_rename_isSome_listElim_of_childIsSome forwardRename
    typedRenaming renameInverse renameInverseLeft renameInverseInjects
    scrutinee nilBranch consBranch (option_isSome_of_eq_some scrutineeIH)
    (option_isSome_of_eq_some nilIH) (option_isSome_of_eq_some consIH)

/-- T3 reverse-image induction step for `Term.optionMatch`, consuming only
child `.isSome` witnesses. -/
theorem strengthenTyped?_rename_isSome_optionMatch_of_childIsSome
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
    (scrutineeIsSome :
      (partialStrengthenTyped?
          (Term.rename typedRenaming scrutinee)
          (renamingStrengthening forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true)
    (noneIsSome :
      (partialStrengthenTyped?
          (Term.rename typedRenaming noneBranch)
          (renamingStrengthening forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true)
    (someIsSome :
      (partialStrengthenTyped?
          (Term.rename typedRenaming someBranch)
          (renamingStrengthening forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.optionMatch scrutinee noneBranch someBranch))
        (renamingStrengthening forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true := by
  dsimp only [renamingStrengthening, ContextStrengthening.ofRenaming] at *
  dsimp only [Term.rename, partialStrengthenTyped?]
  have elementStrengthens :
      (elementType.rename forwardRename).partialStrengthen? renameInverse =
        some elementType :=
    ty_partialStrengthen_rename_some elementType forwardRename
      renameInverse renameInverseLeft
  split
  next noElementSuccess =>
    exact False.elim
      (option_some_ne_none (elementStrengthens.symm.trans noElementSuccess))
  next targetElementType elementSuccess =>
    split
    next noScrutSuccess =>
      exact False.elim
        (option_isSome_false_of_eq_none noScrutSuccess scrutineeIsSome)
    next scrutResult scrutSuccess =>
      split
      next noNoneSuccess =>
        exact False.elim
          (option_isSome_false_of_eq_none noNoneSuccess noneIsSome)
      next noneResult noneSuccess =>
        split
        next noSomeSuccess =>
          exact False.elim
            (option_isSome_false_of_eq_none noSomeSuccess someIsSome)
        next someResult someSuccess =>
          rfl

/-- T3 reverse-image induction step for `Term.optionMatch`. -/
theorem strengthenTyped?_rename_isSome_optionMatch
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
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.optionMatch scrutinee noneBranch someBranch))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  strengthenTyped?_rename_isSome_optionMatch_of_childIsSome forwardRename
    typedRenaming renameInverse renameInverseLeft renameInverseInjects
    scrutinee noneBranch someBranch (option_isSome_of_eq_some scrutineeIH)
    (option_isSome_of_eq_some noneIH) (option_isSome_of_eq_some someIH)

/-- T3 reverse-image induction step for `Term.eitherMatch`, consuming only
child `.isSome` witnesses. -/
theorem strengthenTyped?_rename_isSome_eitherMatch_of_childIsSome
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
    (scrutineeIsSome :
      (partialStrengthenTyped?
          (Term.rename typedRenaming scrutinee)
          (renamingStrengthening forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true)
    (leftIsSome :
      (partialStrengthenTyped?
          (Term.rename typedRenaming leftBranch)
          (renamingStrengthening forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true)
    (rightIsSome :
      (partialStrengthenTyped?
          (Term.rename typedRenaming rightBranch)
          (renamingStrengthening forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.eitherMatch scrutinee leftBranch rightBranch))
        (renamingStrengthening forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true := by
  dsimp only [renamingStrengthening, ContextStrengthening.ofRenaming] at *
  dsimp only [Term.rename, partialStrengthenTyped?]
  have leftTypeStrengthens :
      (leftType.rename forwardRename).partialStrengthen? renameInverse =
        some leftType :=
    ty_partialStrengthen_rename_some leftType forwardRename
      renameInverse renameInverseLeft
  have rightTypeStrengthens :
      (rightType.rename forwardRename).partialStrengthen? renameInverse =
        some rightType :=
    ty_partialStrengthen_rename_some rightType forwardRename
      renameInverse renameInverseLeft
  have motiveTypeStrengthens :
      (motiveType.rename forwardRename).partialStrengthen? renameInverse =
        some motiveType :=
    ty_partialStrengthen_rename_some motiveType forwardRename
      renameInverse renameInverseLeft
  split
  next noLeftSuccess =>
    exact False.elim
      (option_some_ne_none (leftTypeStrengthens.symm.trans noLeftSuccess))
  next targetLeftType leftSuccess =>
    split
    next noRightSuccess =>
      exact False.elim
        (option_some_ne_none
          (rightTypeStrengthens.symm.trans noRightSuccess))
    next targetRightType rightSuccess =>
      split
      next noMotiveSuccess =>
        exact False.elim
          (option_some_ne_none
            (motiveTypeStrengthens.symm.trans noMotiveSuccess))
      next targetMotiveType motiveSuccess =>
        split
        next noScrutSuccess =>
          exact False.elim
            (option_isSome_false_of_eq_none noScrutSuccess scrutineeIsSome)
        next scrutResult scrutSuccess =>
          split
          next noLeftBranchSuccess =>
            exact False.elim
              (option_isSome_false_of_eq_none
                noLeftBranchSuccess leftIsSome)
          next leftResult leftBranchSuccess =>
            split
            next noRightBranchSuccess =>
              exact False.elim
                (option_isSome_false_of_eq_none
                  noRightBranchSuccess rightIsSome)
            next rightResult rightBranchSuccess =>
              rfl

/-- T3 reverse-image induction step for `Term.eitherMatch`. -/
theorem strengthenTyped?_rename_isSome_eitherMatch
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
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.eitherMatch scrutinee leftBranch rightBranch))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  strengthenTyped?_rename_isSome_eitherMatch_of_childIsSome forwardRename
    typedRenaming renameInverse renameInverseLeft renameInverseInjects
    scrutinee leftBranch rightBranch (option_isSome_of_eq_some scrutineeIH)
    (option_isSome_of_eq_some leftIH) (option_isSome_of_eq_some rightIH)

/-- T3 reverse-image induction step for `Term.intervalMeet`, consuming only
child `.isSome` witnesses. -/
theorem strengthenTyped?_rename_isSome_intervalMeet_of_childIsSome
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
    {leftRaw rightRaw : RawTerm sourceScope}
    (leftValue : Term sourceCtx Ty.interval leftRaw)
    (rightValue : Term sourceCtx Ty.interval rightRaw)
    (leftIsSome :
      (partialStrengthenTyped?
          (Term.rename typedRenaming leftValue)
          (renamingStrengthening forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true)
    (rightIsSome :
      (partialStrengthenTyped?
          (Term.rename typedRenaming rightValue)
          (renamingStrengthening forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.intervalMeet leftValue rightValue))
        (renamingStrengthening forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true := by
  dsimp only [renamingStrengthening, ContextStrengthening.ofRenaming] at *
  dsimp only [Term.rename, partialStrengthenTyped?]
  split
  next noLeftSuccess =>
    exact False.elim
      (option_isSome_false_of_eq_none noLeftSuccess leftIsSome)
  next leftResult leftSuccess =>
    split
    next noRightSuccess =>
      exact False.elim
        (option_isSome_false_of_eq_none noRightSuccess rightIsSome)
    next rightResult rightSuccess =>
      rfl

/-- T3 reverse-image induction step for `Term.intervalMeet`. -/
theorem strengthenTyped?_rename_isSome_intervalMeet
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
    {leftRaw rightRaw : RawTerm sourceScope}
    (leftValue : Term sourceCtx Ty.interval leftRaw)
    (rightValue : Term sourceCtx Ty.interval rightRaw)
    (leftIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming leftValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            leftValue))
    (rightIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming rightValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            rightValue)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.intervalMeet leftValue rightValue))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  strengthenTyped?_rename_isSome_intervalMeet_of_childIsSome forwardRename
    typedRenaming renameInverse renameInverseLeft renameInverseInjects
    leftValue rightValue (option_isSome_of_eq_some leftIH)
    (option_isSome_of_eq_some rightIH)

/-- T3 reverse-image induction step for `Term.intervalJoin`, consuming only
child `.isSome` witnesses. -/
theorem strengthenTyped?_rename_isSome_intervalJoin_of_childIsSome
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
    {leftRaw rightRaw : RawTerm sourceScope}
    (leftValue : Term sourceCtx Ty.interval leftRaw)
    (rightValue : Term sourceCtx Ty.interval rightRaw)
    (leftIsSome :
      (partialStrengthenTyped?
          (Term.rename typedRenaming leftValue)
          (renamingStrengthening forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true)
    (rightIsSome :
      (partialStrengthenTyped?
          (Term.rename typedRenaming rightValue)
          (renamingStrengthening forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.intervalJoin leftValue rightValue))
        (renamingStrengthening forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true := by
  dsimp only [renamingStrengthening, ContextStrengthening.ofRenaming] at *
  dsimp only [Term.rename, partialStrengthenTyped?]
  split
  next noLeftSuccess =>
    exact False.elim
      (option_isSome_false_of_eq_none noLeftSuccess leftIsSome)
  next leftResult leftSuccess =>
    split
    next noRightSuccess =>
      exact False.elim
        (option_isSome_false_of_eq_none noRightSuccess rightIsSome)
    next rightResult rightSuccess =>
      rfl

/-- T3 reverse-image induction step for `Term.intervalJoin`. -/
theorem strengthenTyped?_rename_isSome_intervalJoin
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
    {leftRaw rightRaw : RawTerm sourceScope}
    (leftValue : Term sourceCtx Ty.interval leftRaw)
    (rightValue : Term sourceCtx Ty.interval rightRaw)
    (leftIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming leftValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            leftValue))
    (rightIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming rightValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            rightValue)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.intervalJoin leftValue rightValue))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  strengthenTyped?_rename_isSome_intervalJoin_of_childIsSome forwardRename
    typedRenaming renameInverse renameInverseLeft renameInverseInjects
    leftValue rightValue (option_isSome_of_eq_some leftIH)
    (option_isSome_of_eq_some rightIH)

end Term

end LeanFX2
