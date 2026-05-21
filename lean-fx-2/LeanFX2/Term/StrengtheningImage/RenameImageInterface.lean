import LeanFX2.Term.StrengtheningImage.RenameImageCastWrapped
import LeanFX2.Term.StrengtheningImage.ImageCore
import LeanFX2.Term.ProofIrrel
import LeanFX2.Term.RenameInjective.InductiveArms

/-! # Term/StrengtheningImage/RenameImageInterface

Public T1 interface for rename-image strengthening.  The implementation
first packages rename-image totality as existence, then uses T2 injectivity
to pin the computed witness to the canonical `StrengtheningResult.fromRename`
payload.
-/

namespace LeanFX2

namespace RawRenamingInjective

/-- A partial left inverse proves the corresponding total raw renaming is
injective. -/
theorem of_partialInverseLeft {sourceScope targetScope : Nat}
    (forwardRename : RawRenaming sourceScope targetScope)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition) :
    RawRenamingInjective forwardRename := by
  intro positionA positionB positionsRenameEq
  have inverseA := renameInverseLeft positionA
  have inverseB := renameInverseLeft positionB
  rw [positionsRenameEq] at inverseA
  rw [inverseB] at inverseA
  injection inverseA with positionsEq
  exact positionsEq.symm

end RawRenamingInjective

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

/-- Renaming-image iff for a fixed injective typed renaming.

For a term whose indices are already syntactic renamings of source indices,
successful strengthening through the renaming-induced strengthening is
equivalent to being an exact typed-renaming image. -/
theorem rename_image_iff_strengthenTyped?_some
    {mode : Mode} {level : Nat}
    {sourceScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {sourceType : Ty level sourceScope}
    {sourceRaw : RawTerm sourceScope}
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
        targetPosition = forwardRename sourcePosition)
    (renamedTerm :
      Term targetCtx (sourceType.rename forwardRename)
        (sourceRaw.rename forwardRename)) :
    (∃ sourceTerm : Term sourceCtx sourceType sourceRaw,
      renamedTerm = Term.rename typedRenaming sourceTerm) ↔
    ∃ result,
      partialStrengthenTyped? renamedTerm
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects) = some result := by
  let renamingStrengthening :=
    ContextStrengthening.ofRenaming forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects
  have forwardRenameInjective : RawRenamingInjective forwardRename :=
    RawRenamingInjective.of_partialInverseLeft forwardRename renameInverse
      renameInverseLeft
  refine ⟨?_, ?_⟩
  · intro imageWitness
    obtain ⟨sourceTerm, imageEq⟩ := imageWitness
    cases imageEq
    exact strengthenTyped?_rename_some sourceTerm forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects
  · intro strengtheningWitness
    obtain ⟨result, success⟩ := strengtheningWitness
    have soundness : HEq renamedTerm result.renamedTarget :=
      weaken_inv_of_strengthenTyped?_some renamingStrengthening result success
    cases result with
    | mk targetType targetRaw targetTerm typeStrengthens rawStrengthens
        typeRenames rawRenames =>
        have targetTypeEq : sourceType = targetType :=
          Ty.rename_injective_under_injective_renaming sourceType
            forwardRenameInjective targetType typeRenames
        have targetRawEq : sourceRaw = targetRaw :=
          RawTerm.rename_injective_under_injective_renaming sourceRaw
            forwardRenameInjective targetRaw rawRenames
        cases targetTypeEq
        cases targetRawEq
        refine ⟨targetTerm, ?_⟩
        have soundEq :
            renamedTerm =
              Term.rename renamingStrengthening.toTermRenaming targetTerm :=
          eq_of_heq soundness
        have renamedProofEq :
            Term.rename renamingStrengthening.toTermRenaming targetTerm =
              Term.rename typedRenaming targetTerm :=
          Term.rename_proof_irrel renamingStrengthening.toTermRenaming
            typedRenaming targetTerm
        rw [renamedProofEq] at soundEq
        exact soundEq

/-- Successful strengthening of a typed rename recovers the original term.

This is the direct T2 consumer: soundness gives equality of the two renamed
terms, proof irrelevance normalizes the renaming proof, and
`Term.rename_injective` cancels the injective renaming. -/
theorem strengthenTyped?_rename_result_target_heq
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
        targetPosition = forwardRename sourcePosition)
    (result : StrengtheningResult
      (ContextStrengthening.ofRenaming forwardRename typedRenaming
        renameInverse renameInverseLeft renameInverseInjects)
      (Term.rename typedRenaming sourceTerm))
    (success :
      partialStrengthenTyped?
        (Term.rename typedRenaming sourceTerm)
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects) = some result) :
    HEq result.targetTerm sourceTerm := by
  let renamingStrengthening :=
    ContextStrengthening.ofRenaming forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects
  have forwardRenameInjective : RawRenamingInjective forwardRename :=
    RawRenamingInjective.of_partialInverseLeft forwardRename renameInverse
      renameInverseLeft
  have soundness :
      HEq (Term.rename typedRenaming sourceTerm) result.renamedTarget :=
    weaken_inv_of_strengthenTyped?_some renamingStrengthening result success
  cases result with
  | mk targetType targetRaw targetTerm typeStrengthens rawStrengthens
      typeRenames rawRenames =>
      have targetTypeEq : sourceType = targetType :=
        Ty.rename_injective_under_injective_renaming sourceType
          forwardRenameInjective targetType typeRenames
      have targetRawEq : sourceRaw = targetRaw :=
        RawTerm.rename_injective_under_injective_renaming sourceRaw
          forwardRenameInjective targetRaw rawRenames
      cases targetTypeEq
      cases targetRawEq
      have soundEq :
          Term.rename typedRenaming sourceTerm =
            Term.rename renamingStrengthening.toTermRenaming targetTerm :=
        eq_of_heq soundness
      have renamedProofEq :
          Term.rename renamingStrengthening.toTermRenaming targetTerm =
            Term.rename typedRenaming targetTerm :=
        Term.rename_proof_irrel renamingStrengthening.toTermRenaming
          typedRenaming targetTerm
      rw [renamedProofEq] at soundEq
      have targetEq : sourceTerm = targetTerm :=
        Term.rename_injective typedRenaming forwardRenameInjective
          sourceTerm targetTerm soundEq
      cases targetEq
      exact HEq.rfl

/-- Successful strengthening of a typed rename has the canonical
`fromRename` payload.

The dispatcher may compute its witness through constructor-specific
proof terms, but the data fields are forced by the renaming inverse:
target type and raw are recovered by injectivity of the underlying
renaming, and the target term is recovered by `Term.rename_injective`.
The remaining fields are proof-irrelevant. -/
theorem strengthenTyped?_rename_result_eq_fromRename
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
        targetPosition = forwardRename sourcePosition)
    (result : StrengtheningResult
      (ContextStrengthening.ofRenaming forwardRename typedRenaming
        renameInverse renameInverseLeft renameInverseInjects)
      (Term.rename typedRenaming sourceTerm))
    (success :
      partialStrengthenTyped?
        (Term.rename typedRenaming sourceTerm)
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects) = some result) :
    result =
      StrengtheningResult.fromRename forwardRename typedRenaming
        renameInverse renameInverseLeft renameInverseInjects sourceTerm := by
  have forwardRenameInjective : RawRenamingInjective forwardRename :=
    RawRenamingInjective.of_partialInverseLeft forwardRename renameInverse
      renameInverseLeft
  have targetTermHEq :
      HEq result.targetTerm sourceTerm :=
    strengthenTyped?_rename_result_target_heq sourceTerm forwardRename
      typedRenaming renameInverse renameInverseLeft renameInverseInjects
      result success
  cases result with
  | mk targetType targetRaw targetTerm typeStrengthens rawStrengthens
      typeRenames rawRenames =>
      have targetTypeEq : sourceType = targetType :=
        Ty.rename_injective_under_injective_renaming sourceType
          forwardRenameInjective targetType typeRenames
      have targetRawEq : sourceRaw = targetRaw :=
        RawTerm.rename_injective_under_injective_renaming sourceRaw
          forwardRenameInjective targetRaw rawRenames
      cases targetTypeEq
      cases targetRawEq
      have targetTermEq : targetTerm = sourceTerm :=
        eq_of_heq targetTermHEq
      cases targetTermEq
      have typeStrengthensEq :
          typeStrengthens =
            (StrengtheningResult.fromRename forwardRename typedRenaming
              renameInverse renameInverseLeft renameInverseInjects
              sourceTerm).typeStrengthens := proof_irrel _ _
      have rawStrengthensEq :
          rawStrengthens =
            (StrengtheningResult.fromRename forwardRename typedRenaming
              renameInverse renameInverseLeft renameInverseInjects
              sourceTerm).rawStrengthens := proof_irrel _ _
      have typeRenamesEq :
          typeRenames =
            (StrengtheningResult.fromRename forwardRename typedRenaming
              renameInverse renameInverseLeft renameInverseInjects
              sourceTerm).typeRenames := proof_irrel _ _
      have rawRenamesEq :
          rawRenames =
            (StrengtheningResult.fromRename forwardRename typedRenaming
              renameInverse renameInverseLeft renameInverseInjects
              sourceTerm).rawRenames := proof_irrel _ _
      cases typeStrengthensEq
      cases rawStrengthensEq
      cases typeRenamesEq
      cases rawRenamesEq
      rfl

/-- T1, equation form: strengthening a typed renaming through its
renaming-induced strengthening deterministically recovers the original
term as `StrengtheningResult.fromRename`. -/
theorem strengthenTyped?_rename_eq
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
    partialStrengthenTyped?
        (Term.rename typedRenaming sourceTerm)
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects sourceTerm) := by
  obtain ⟨result, success⟩ :=
    strengthenTyped?_rename_some sourceTerm forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects
  have resultEq :
      result =
        StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects sourceTerm :=
    strengthenTyped?_rename_result_eq_fromRename sourceTerm forwardRename
      typedRenaming renameInverse renameInverseLeft renameInverseInjects
      result success
  rw [success, resultEq]

/-! ## Weakening-image corollaries

The newest-slot weakening is the canonical renaming-image instance of T1:
`RawRenaming.weaken` with partial inverse `PartialRawRenaming.dropNewest`.
These are the consumer-facing theorems for T4-style weaken-image totality.
-/

/-- T1 specialized to newest-slot weakening. -/
theorem strengthenTyped?_weaken_eq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (newType : Ty level scope)
    (sourceTerm : Term context sourceType sourceRaw) :
    strengthenTyped? (Term.weaken newType sourceTerm) =
      some
        (StrengtheningResult.fromRename RawRenaming.weaken
          (TermRenaming.weakenStep context newType)
          PartialRawRenaming.dropNewest
          PartialRawRenaming.dropNewest_weaken
          PartialRawRenaming.dropNewest_renamingInjectsBack
          sourceTerm) := by
  exact strengthenTyped?_rename_eq sourceTerm RawRenaming.weaken
    (TermRenaming.weakenStep context newType)
    PartialRawRenaming.dropNewest
    PartialRawRenaming.dropNewest_weaken
    PartialRawRenaming.dropNewest_renamingInjectsBack

/-- Newest-slot weakening always lies in the typed strengthening image. -/
theorem strengthenTyped?_weaken_isSome
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (newType : Ty level scope)
    (sourceTerm : Term context sourceType sourceRaw) :
    (strengthenTyped? (Term.weaken newType sourceTerm)).isSome = true := by
  rw [strengthenTyped?_weaken_eq newType sourceTerm]
  rfl

/-- Newest-slot unweakening cancels newest-slot weakening. -/
theorem unweaken?_weaken
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (newType : Ty level scope)
    (sourceTerm : Term context sourceType sourceRaw) :
    Term.unweaken? (Term.weaken newType sourceTerm) = some sourceTerm := by
  unfold Term.unweaken?
  rw [strengthenTyped?_weaken_eq newType sourceTerm]
  rfl

end Term

end LeanFX2
