import LeanFX2.Term.StrengtheningImage.RenameImageInterface

/-! # Term/StrengtheningImage/TotalOnWeakenHeadlines

Consumer-facing weaken-image totality headlines.
-/

namespace LeanFX2

namespace Term

/-- A typed term is total on newest-slot weakening when strengthening
succeeds after weakening by any new binder type. -/
def IsTotalOnWeaken {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm : Term context sourceType sourceRaw) : Prop :=
  ∀ (newType : Ty level scope),
    (strengthenTyped? (Term.weaken newType sourceTerm)).isSome

/-- T1 closes the total-on-weaken predicate for every typed term.

Newest-slot weakening is the `RawRenaming.weaken` instance of the
renaming-image theorem; no per-constructor totality proof is needed. -/
theorem isTotalOnWeaken_universal {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm : Term context sourceType sourceRaw) :
    IsTotalOnWeaken sourceTerm := by
  intro newType
  exact strengthenTyped?_weaken_isSome newType sourceTerm

/-- Generic totality package for a weakened source term. -/
theorem weaken_image_totality {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (newType : Ty level scope)
    (sourceTerm : Term context sourceType sourceRaw) :
    (∃ originalTerm,
        Term.unweaken? (Term.weaken newType sourceTerm) =
          some originalTerm) ∧
      ∃ result,
        strengthenTyped? (Term.weaken newType sourceTerm) = some result :=
  ⟨⟨sourceTerm, unweaken?_weaken newType sourceTerm⟩,
   ⟨StrengtheningResult.fromRename RawRenaming.weaken
      (TermRenaming.weakenStep context newType)
      PartialRawRenaming.dropNewest
      PartialRawRenaming.dropNewest_weaken
      PartialRawRenaming.dropNewest_renamingInjectsBack sourceTerm,
    strengthenTyped?_weaken_eq newType sourceTerm⟩⟩

end Term

end LeanFX2
