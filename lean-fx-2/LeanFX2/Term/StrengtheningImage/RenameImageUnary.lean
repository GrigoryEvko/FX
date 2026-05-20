import LeanFX2.Term.StrengtheningImage.RenameImageAtomic

/-! # Term/StrengtheningImage/RenameImageUnary

Rename-image success bridges for unary and single-child structured constructors.
-/

namespace LeanFX2

namespace Term

/-! ## Child-success recursive interfaces

The `_of_childIsSome` variants are the surface needed by recursive T3
packaging: cast-wrapped children often expose only `.isSome` through HEq
cast-invariance, not an exact `some (StrengtheningResult.fromRename ...)`
equation.  The historical exact-IH theorem names remain as wrappers below.
-/

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

/-- T3 reverse-image induction step for `Term.natSucc`. -/
theorem strengthenTyped?_rename_isSome_natSucc_of_childIsSome
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
    {predecessorRaw : RawTerm sourceScope}
    (predecessor : Term sourceCtx Ty.nat predecessorRaw)
    (predecessorIsSome :
      (partialStrengthenTyped?
          (Term.rename typedRenaming predecessor)
          (renamingStrengthening forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.natSucc predecessor))
        (renamingStrengthening forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true := by
  dsimp only [renamingStrengthening, ContextStrengthening.ofRenaming] at *
  dsimp only [Term.rename, partialStrengthenTyped?]
  split
  next noPredecessorSuccess =>
    exact False.elim
      (option_isSome_false_of_eq_none noPredecessorSuccess predecessorIsSome)
  next predecessorResult predecessorSuccess =>
    rfl

/-- T3 reverse-image induction step for `Term.natSucc`. -/
theorem strengthenTyped?_rename_isSome_natSucc
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
    {predecessorRaw : RawTerm sourceScope}
    (predecessor : Term sourceCtx Ty.nat predecessorRaw)
    (predecessorIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming predecessor)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            predecessor)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.natSucc predecessor))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  strengthenTyped?_rename_isSome_natSucc_of_childIsSome forwardRename
    typedRenaming renameInverse renameInverseLeft renameInverseInjects
    predecessor (option_isSome_of_eq_some predecessorIH)

/-- T3 reverse-image induction step for `Term.intervalOpp`. -/
theorem strengthenTyped?_rename_isSome_intervalOpp_of_childIsSome
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
    {innerRaw : RawTerm sourceScope}
    (innerValue : Term sourceCtx Ty.interval innerRaw)
    (innerIsSome :
      (partialStrengthenTyped?
          (Term.rename typedRenaming innerValue)
          (renamingStrengthening forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.intervalOpp innerValue))
        (renamingStrengthening forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true := by
  dsimp only [renamingStrengthening, ContextStrengthening.ofRenaming] at *
  dsimp only [Term.rename, partialStrengthenTyped?]
  split
  next noInnerSuccess =>
    exact False.elim
      (option_isSome_false_of_eq_none noInnerSuccess innerIsSome)
  next innerResult innerSuccess =>
    rfl

/-- T3 reverse-image induction step for `Term.intervalOpp`. -/
theorem strengthenTyped?_rename_isSome_intervalOpp
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
    {innerRaw : RawTerm sourceScope}
    (innerValue : Term sourceCtx Ty.interval innerRaw)
    (innerIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming innerValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            innerValue)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.intervalOpp innerValue))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  strengthenTyped?_rename_isSome_intervalOpp_of_childIsSome forwardRename
    typedRenaming renameInverse renameInverseLeft renameInverseInjects
    innerValue (option_isSome_of_eq_some innerIH)

/-- T3 reverse-image induction step for `Term.modIntro`. -/
theorem strengthenTyped?_rename_isSome_modIntro_of_childIsSome
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
    {innerType : Ty level sourceScope}
    {innerRaw : RawTerm sourceScope}
    (innerTerm : Term sourceCtx innerType innerRaw)
    (innerIsSome :
      (partialStrengthenTyped?
          (Term.rename typedRenaming innerTerm)
          (renamingStrengthening forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.modIntro innerTerm))
        (renamingStrengthening forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true := by
  dsimp only [renamingStrengthening, ContextStrengthening.ofRenaming] at *
  dsimp only [Term.rename, partialStrengthenTyped?]
  split
  next noInnerSuccess =>
    exact False.elim
      (option_isSome_false_of_eq_none noInnerSuccess innerIsSome)
  next innerResult innerSuccess =>
    rfl

/-- T3 reverse-image induction step for `Term.modIntro`. -/
theorem strengthenTyped?_rename_isSome_modIntro
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
    {innerType : Ty level sourceScope}
    {innerRaw : RawTerm sourceScope}
    (innerTerm : Term sourceCtx innerType innerRaw)
    (innerIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming innerTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            innerTerm)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.modIntro innerTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  strengthenTyped?_rename_isSome_modIntro_of_childIsSome forwardRename
    typedRenaming renameInverse renameInverseLeft renameInverseInjects
    innerTerm (option_isSome_of_eq_some innerIH)

/-- T3 reverse-image induction step for `Term.modElim`. -/
theorem strengthenTyped?_rename_isSome_modElim_of_childIsSome
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
    {innerType : Ty level sourceScope}
    {innerRaw : RawTerm sourceScope}
    (innerTerm : Term sourceCtx innerType innerRaw)
    (innerIsSome :
      (partialStrengthenTyped?
          (Term.rename typedRenaming innerTerm)
          (renamingStrengthening forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.modElim innerTerm))
        (renamingStrengthening forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true := by
  dsimp only [renamingStrengthening, ContextStrengthening.ofRenaming] at *
  dsimp only [Term.rename, partialStrengthenTyped?]
  split
  next noInnerSuccess =>
    exact False.elim
      (option_isSome_false_of_eq_none noInnerSuccess innerIsSome)
  next innerResult innerSuccess =>
    rfl

/-- T3 reverse-image induction step for `Term.modElim`. -/
theorem strengthenTyped?_rename_isSome_modElim
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
    {innerType : Ty level sourceScope}
    {innerRaw : RawTerm sourceScope}
    (innerTerm : Term sourceCtx innerType innerRaw)
    (innerIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming innerTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            innerTerm)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.modElim innerTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  strengthenTyped?_rename_isSome_modElim_of_childIsSome forwardRename
    typedRenaming renameInverse renameInverseLeft renameInverseInjects
    innerTerm (option_isSome_of_eq_some innerIH)

/-- T3 reverse-image induction step for `Term.subsume`. -/
theorem strengthenTyped?_rename_isSome_subsume_of_childIsSome
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
    {innerType : Ty level sourceScope}
    {innerRaw : RawTerm sourceScope}
    (innerTerm : Term sourceCtx innerType innerRaw)
    (innerIsSome :
      (partialStrengthenTyped?
          (Term.rename typedRenaming innerTerm)
          (renamingStrengthening forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.subsume innerTerm))
        (renamingStrengthening forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true := by
  dsimp only [renamingStrengthening, ContextStrengthening.ofRenaming] at *
  dsimp only [Term.rename, partialStrengthenTyped?]
  split
  next noInnerSuccess =>
    exact False.elim
      (option_isSome_false_of_eq_none noInnerSuccess innerIsSome)
  next innerResult innerSuccess =>
    rfl

/-- T3 reverse-image induction step for `Term.subsume`. -/
theorem strengthenTyped?_rename_isSome_subsume
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
    {innerType : Ty level sourceScope}
    {innerRaw : RawTerm sourceScope}
    (innerTerm : Term sourceCtx innerType innerRaw)
    (innerIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming innerTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            innerTerm)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.subsume innerTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  strengthenTyped?_rename_isSome_subsume_of_childIsSome forwardRename
    typedRenaming renameInverse renameInverseLeft renameInverseInjects
    innerTerm (option_isSome_of_eq_some innerIH)

/-- T3 reverse-image induction step for `Term.optionSome`. -/
theorem strengthenTyped?_rename_isSome_optionSome_of_childIsSome
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
    {valueRaw : RawTerm sourceScope}
    (valueTerm : Term sourceCtx elementType valueRaw)
    (valueIsSome :
      (partialStrengthenTyped?
          (Term.rename typedRenaming valueTerm)
          (renamingStrengthening forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.optionSome valueTerm))
        (renamingStrengthening forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true := by
  dsimp only [renamingStrengthening, ContextStrengthening.ofRenaming] at *
  dsimp only [Term.rename, partialStrengthenTyped?]
  split
  next noValueSuccess =>
    exact False.elim
      (option_isSome_false_of_eq_none noValueSuccess valueIsSome)
  next valueResult valueSuccess =>
    rfl

/-- T3 reverse-image induction step for `Term.optionSome`. -/
theorem strengthenTyped?_rename_isSome_optionSome
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
    {valueRaw : RawTerm sourceScope}
    (valueTerm : Term sourceCtx elementType valueRaw)
    (valueIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming valueTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            valueTerm)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.optionSome valueTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  strengthenTyped?_rename_isSome_optionSome_of_childIsSome forwardRename
    typedRenaming renameInverse renameInverseLeft renameInverseInjects
    valueTerm (option_isSome_of_eq_some valueIH)

/-- T3 reverse-image induction step for `Term.eitherInl`. -/
theorem strengthenTyped?_rename_isSome_eitherInl_of_childIsSome
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
    {leftType rightType : Ty level sourceScope}
    {valueRaw : RawTerm sourceScope}
    (valueTerm : Term sourceCtx leftType valueRaw)
    (valueIsSome :
      (partialStrengthenTyped?
          (Term.rename typedRenaming valueTerm)
          (renamingStrengthening forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.eitherInl (rightType := rightType) valueTerm))
        (renamingStrengthening forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true := by
  dsimp only [renamingStrengthening, ContextStrengthening.ofRenaming] at *
  dsimp only [Term.rename, partialStrengthenTyped?]
  have rightTypeStrengthens :
      (rightType.rename forwardRename).partialStrengthen? renameInverse =
        some rightType := by
    rw [Ty.partialStrengthen?_rename_some rightType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity rightType]
  split
  next noRightSuccess =>
    rw [noRightSuccess] at rightTypeStrengthens
    cases rightTypeStrengthens
  next targetRightType rightSuccess =>
    split
    next noValueSuccess =>
      exact False.elim
        (option_isSome_false_of_eq_none noValueSuccess valueIsSome)
    next valueResult valueSuccess =>
      rfl

/-- T3 reverse-image induction step for `Term.eitherInl`. -/
theorem strengthenTyped?_rename_isSome_eitherInl
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
    {leftType rightType : Ty level sourceScope}
    {valueRaw : RawTerm sourceScope}
    (valueTerm : Term sourceCtx leftType valueRaw)
    (valueIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming valueTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            valueTerm)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.eitherInl (rightType := rightType) valueTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  strengthenTyped?_rename_isSome_eitherInl_of_childIsSome forwardRename
    typedRenaming renameInverse renameInverseLeft renameInverseInjects
    valueTerm (option_isSome_of_eq_some valueIH)

/-- T3 reverse-image induction step for `Term.eitherInr`. -/
theorem strengthenTyped?_rename_isSome_eitherInr_of_childIsSome
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
    {leftType rightType : Ty level sourceScope}
    {valueRaw : RawTerm sourceScope}
    (valueTerm : Term sourceCtx rightType valueRaw)
    (valueIsSome :
      (partialStrengthenTyped?
          (Term.rename typedRenaming valueTerm)
          (renamingStrengthening forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.eitherInr (leftType := leftType) valueTerm))
        (renamingStrengthening forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true := by
  dsimp only [renamingStrengthening, ContextStrengthening.ofRenaming] at *
  dsimp only [Term.rename, partialStrengthenTyped?]
  have leftTypeStrengthens :
      (leftType.rename forwardRename).partialStrengthen? renameInverse =
        some leftType := by
    rw [Ty.partialStrengthen?_rename_some leftType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity leftType]
  split
  next noLeftSuccess =>
    rw [noLeftSuccess] at leftTypeStrengthens
    cases leftTypeStrengthens
  next targetLeftType leftSuccess =>
    split
    next noValueSuccess =>
      exact False.elim
        (option_isSome_false_of_eq_none noValueSuccess valueIsSome)
    next valueResult valueSuccess =>
      rfl

/-- T3 reverse-image induction step for `Term.eitherInr`. -/
theorem strengthenTyped?_rename_isSome_eitherInr
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
    {leftType rightType : Ty level sourceScope}
    {valueRaw : RawTerm sourceScope}
    (valueTerm : Term sourceCtx rightType valueRaw)
    (valueIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming valueTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            valueTerm)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.eitherInr (leftType := leftType) valueTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  strengthenTyped?_rename_isSome_eitherInr_of_childIsSome forwardRename
    typedRenaming renameInverse renameInverseLeft renameInverseInjects
    valueTerm (option_isSome_of_eq_some valueIH)

/-- T3 reverse-image induction step for `Term.sessionRecv`. -/
theorem strengthenTyped?_rename_isSome_sessionRecv_of_childIsSome
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
    {protocolStep : RawTerm sourceScope}
    {channelRaw : RawTerm sourceScope}
    (channel : Term sourceCtx (Ty.session protocolStep) channelRaw)
    (channelIsSome :
      (partialStrengthenTyped?
          (Term.rename typedRenaming channel)
          (renamingStrengthening forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.sessionRecv channel))
        (renamingStrengthening forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true := by
  dsimp only [renamingStrengthening, ContextStrengthening.ofRenaming] at *
  dsimp only [Term.rename, partialStrengthenTyped?]
  have protocolStrengthens :
      (protocolStep.rename forwardRename).partialStrengthen? renameInverse =
        some protocolStep := by
    rw [RawTerm.partialStrengthen?_rename_some protocolStep forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity protocolStep]
  split
  next noProtocolSuccess =>
    rw [noProtocolSuccess] at protocolStrengthens
    cases protocolStrengthens
  next targetProtocolStep protocolSuccess =>
    split
    next noChannelSuccess =>
      exact False.elim
        (option_isSome_false_of_eq_none noChannelSuccess channelIsSome)
    next channelResult channelSuccess =>
      rfl

/-- T3 reverse-image induction step for `Term.sessionRecv`. -/
theorem strengthenTyped?_rename_isSome_sessionRecv
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
    {protocolStep : RawTerm sourceScope}
    {channelRaw : RawTerm sourceScope}
    (channel : Term sourceCtx (Ty.session protocolStep) channelRaw)
    (channelIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming channel)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            channel)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.sessionRecv channel))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  strengthenTyped?_rename_isSome_sessionRecv_of_childIsSome forwardRename
    typedRenaming renameInverse renameInverseLeft renameInverseInjects
    channel (option_isSome_of_eq_some channelIH)

/-- T3 reverse-image induction step for `Term.cumulUp`. -/
theorem strengthenTyped?_rename_isSome_cumulUp_of_childIsSome
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
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {codeRaw : RawTerm sourceScope}
    (typeCode : Term sourceCtx (Ty.universe lowerLevel levelLeLow) codeRaw)
    (codeIsSome :
      (partialStrengthenTyped?
          (Term.rename typedRenaming typeCode)
          (renamingStrengthening forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.cumulUp lowerLevel higherLevel cumulMonotone levelLeLow
            levelLeHigh typeCode))
        (renamingStrengthening forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true := by
  dsimp only [renamingStrengthening, ContextStrengthening.ofRenaming] at *
  dsimp only [Term.rename, partialStrengthenTyped?]
  split
  next noCodeSuccess =>
    exact False.elim
      (option_isSome_false_of_eq_none noCodeSuccess codeIsSome)
  next codeResult codeSuccess =>
    rfl

/-- T3 reverse-image induction step for `Term.cumulUp`. -/
theorem strengthenTyped?_rename_isSome_cumulUp
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
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {codeRaw : RawTerm sourceScope}
    (typeCode : Term sourceCtx (Ty.universe lowerLevel levelLeLow) codeRaw)
    (codeIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming typeCode)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            typeCode)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.cumulUp lowerLevel higherLevel cumulMonotone levelLeLow
            levelLeHigh typeCode))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  strengthenTyped?_rename_isSome_cumulUp_of_childIsSome forwardRename
    typedRenaming renameInverse renameInverseLeft renameInverseInjects
    lowerLevel higherLevel cumulMonotone levelLeLow levelLeHigh typeCode
    (option_isSome_of_eq_some codeIH)

/-- T3 reverse-image induction step for `Term.recordProj`. -/
theorem strengthenTyped?_rename_isSome_recordProj_of_childIsSome
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
    {singleFieldType : Ty level sourceScope}
    {recordRaw : RawTerm sourceScope}
    (recordValue : Term sourceCtx (Ty.record singleFieldType) recordRaw)
    (recordIsSome :
      (partialStrengthenTyped?
          (Term.rename typedRenaming recordValue)
          (renamingStrengthening forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.recordProj recordValue))
        (renamingStrengthening forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true := by
  dsimp only [renamingStrengthening, ContextStrengthening.ofRenaming] at *
  dsimp only [Term.rename, partialStrengthenTyped?]
  have fieldStrengthens :
      (singleFieldType.rename forwardRename).partialStrengthen?
          renameInverse =
        some singleFieldType := by
    rw [Ty.partialStrengthen?_rename_some singleFieldType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity singleFieldType]
  split
  next noFieldSuccess =>
    rw [noFieldSuccess] at fieldStrengthens
    cases fieldStrengthens
  next targetFieldType fieldSuccess =>
    split
    next noRecordSuccess =>
      exact False.elim
        (option_isSome_false_of_eq_none noRecordSuccess recordIsSome)
    next recordResult recordSuccess =>
      rfl

/-- T3 reverse-image induction step for `Term.recordProj`. -/
theorem strengthenTyped?_rename_isSome_recordProj
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
    {singleFieldType : Ty level sourceScope}
    {recordRaw : RawTerm sourceScope}
    (recordValue : Term sourceCtx (Ty.record singleFieldType) recordRaw)
    (recordIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming recordValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            recordValue)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.recordProj recordValue))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  strengthenTyped?_rename_isSome_recordProj_of_childIsSome forwardRename
    typedRenaming renameInverse renameInverseLeft renameInverseInjects
    recordValue (option_isSome_of_eq_some recordIH)

/-- T3 reverse-image induction step for `Term.codataDest`. -/
theorem strengthenTyped?_rename_isSome_codataDest_of_childIsSome
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
    {codataRaw : RawTerm sourceScope}
    (codataValue : Term sourceCtx (Ty.codata stateType outputType) codataRaw)
    (codataIsSome :
      (partialStrengthenTyped?
          (Term.rename typedRenaming codataValue)
          (renamingStrengthening forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.codataDest codataValue))
        (renamingStrengthening forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true := by
  dsimp only [renamingStrengthening, ContextStrengthening.ofRenaming] at *
  dsimp only [Term.rename, partialStrengthenTyped?]
  have stateStrengthens :
      (stateType.rename forwardRename).partialStrengthen? renameInverse =
        some stateType := by
    rw [Ty.partialStrengthen?_rename_some stateType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity stateType]
  have outputStrengthens :
      (outputType.rename forwardRename).partialStrengthen? renameInverse =
        some outputType := by
    rw [Ty.partialStrengthen?_rename_some outputType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity outputType]
  split
  next noStateSuccess =>
    rw [noStateSuccess] at stateStrengthens
    cases stateStrengthens
  next targetStateType stateSuccess =>
    split
    next noOutputSuccess =>
      rw [noOutputSuccess] at outputStrengthens
      cases outputStrengthens
    next targetOutputType outputSuccess =>
      split
      next noCodataSuccess =>
        exact False.elim
          (option_isSome_false_of_eq_none noCodataSuccess codataIsSome)
      next codataResult codataSuccess =>
        rfl

/-- T3 reverse-image induction step for `Term.codataDest`. -/
theorem strengthenTyped?_rename_isSome_codataDest
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
    {codataRaw : RawTerm sourceScope}
    (codataValue : Term sourceCtx (Ty.codata stateType outputType) codataRaw)
    (codataIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming codataValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            codataValue)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.codataDest codataValue))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  strengthenTyped?_rename_isSome_codataDest_of_childIsSome forwardRename
    typedRenaming renameInverse renameInverseLeft renameInverseInjects
    codataValue (option_isSome_of_eq_some codataIH)

/-- T3 reverse-image induction step for `Term.recordIntro`. -/
theorem strengthenTyped?_rename_isSome_recordIntro_of_childIsSome
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
    {singleFieldType : Ty level sourceScope}
    {firstRaw : RawTerm sourceScope}
    (firstField : Term sourceCtx singleFieldType firstRaw)
    (fieldIsSome :
      (partialStrengthenTyped?
          (Term.rename typedRenaming firstField)
          (renamingStrengthening forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.recordIntro firstField))
        (renamingStrengthening forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true := by
  dsimp only [renamingStrengthening, ContextStrengthening.ofRenaming] at *
  dsimp only [Term.rename, partialStrengthenTyped?]
  split
  next noFieldSuccess =>
    exact False.elim
      (option_isSome_false_of_eq_none noFieldSuccess fieldIsSome)
  next fieldResult fieldSuccess =>
    rfl

/-- T3 reverse-image induction step for `Term.recordIntro`. -/
theorem strengthenTyped?_rename_isSome_recordIntro
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
    {singleFieldType : Ty level sourceScope}
    {firstRaw : RawTerm sourceScope}
    (firstField : Term sourceCtx singleFieldType firstRaw)
    (fieldIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming firstField)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            firstField)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.recordIntro firstField))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  strengthenTyped?_rename_isSome_recordIntro_of_childIsSome forwardRename
    typedRenaming renameInverse renameInverseLeft renameInverseInjects
    firstField (option_isSome_of_eq_some fieldIH)

/-- T3 reverse-image induction step for `Term.glueElim`. -/
theorem strengthenTyped?_rename_isSome_glueElim_of_childIsSome
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
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level sourceScope}
    {boundaryWitness gluedRaw : RawTerm sourceScope}
    (gluedValue : Term sourceCtx (Ty.glue baseType boundaryWitness) gluedRaw)
    (gluedIsSome :
      (partialStrengthenTyped?
          (Term.rename typedRenaming gluedValue)
          (renamingStrengthening forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.glueElim modeIsUnivalent gluedValue))
        (renamingStrengthening forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true := by
  dsimp only [renamingStrengthening, ContextStrengthening.ofRenaming] at *
  dsimp only [Term.rename, partialStrengthenTyped?]
  have baseStrengthens :
      (baseType.rename forwardRename).partialStrengthen? renameInverse =
        some baseType := by
    rw [Ty.partialStrengthen?_rename_some baseType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity baseType]
  have boundaryStrengthens :
      (boundaryWitness.rename forwardRename).partialStrengthen?
          renameInverse =
        some boundaryWitness := by
    rw [RawTerm.partialStrengthen?_rename_some boundaryWitness forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity boundaryWitness]
  split
  next noBaseSuccess =>
    rw [noBaseSuccess] at baseStrengthens
    cases baseStrengthens
  next targetBaseType baseSuccess =>
    split
    next noBoundarySuccess =>
      rw [noBoundarySuccess] at boundaryStrengthens
      cases boundaryStrengthens
    next targetBoundary boundarySuccess =>
      split
      next noGluedSuccess =>
        exact False.elim
          (option_isSome_false_of_eq_none noGluedSuccess gluedIsSome)
      next gluedResult gluedSuccess =>
        rfl

/-- T3 reverse-image induction step for `Term.glueElim`. -/
theorem strengthenTyped?_rename_isSome_glueElim
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
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level sourceScope}
    {boundaryWitness gluedRaw : RawTerm sourceScope}
    (gluedValue : Term sourceCtx (Ty.glue baseType boundaryWitness) gluedRaw)
    (gluedIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming gluedValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            gluedValue)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.glueElim modeIsUnivalent gluedValue))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  strengthenTyped?_rename_isSome_glueElim_of_childIsSome forwardRename
    typedRenaming renameInverse renameInverseLeft renameInverseInjects
    modeIsUnivalent gluedValue (option_isSome_of_eq_some gluedIH)

end Term

end LeanFX2
