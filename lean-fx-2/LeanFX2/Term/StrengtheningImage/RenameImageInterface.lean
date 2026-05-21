import LeanFX2.Term.StrengtheningImage.RenameImageCastWrapped

/-! # Term/StrengtheningImage/RenameImageInterface

Public T1 interface for rename-image strengthening.  The implementation
headline proves `.isSome`; this file packages that success as an actual
strengthening witness for downstream consumers.
-/

namespace LeanFX2

namespace Term

/-- Every typed rename has a strengthening-image witness. -/
theorem strengthenTyped?_rename_some
    {mode : Mode} {level : Nat}
    {sourceScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {sourceType : Ty level sourceScope}
    {sourceRaw : RawTerm sourceScope}
    (sourceTerm : Term sourceCtx sourceType sourceRaw)
    {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
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
    ∃ strengthenedTerm,
      partialStrengthenTyped?
          (Term.rename typedRenaming sourceTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects) =
        some strengthenedTerm := by
  have success :
      (partialStrengthenTyped?
          (Term.rename typedRenaming sourceTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true :=
    strengthenTyped?_rename_isSome sourceTerm forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects
  generalize resultEq :
      partialStrengthenTyped?
          (Term.rename typedRenaming sourceTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects) =
        strengthenedOption
  cases strengthenedOption with
  | none =>
      rw [resultEq] at success
      cases success
  | some strengthenedTerm =>
      exact ⟨strengthenedTerm, rfl⟩

end Term

end LeanFX2
