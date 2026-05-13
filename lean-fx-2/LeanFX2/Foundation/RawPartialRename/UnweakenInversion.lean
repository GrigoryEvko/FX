import LeanFX2.Foundation.RawPartialRename.Inversion

/-! # LeanFX2.Foundation.RawPartialRename.UnweakenInversion

The canonical headline used by downstream cd cascades.  Specializes
the generic `partialRename?_imp_rename` to the `(RawRenaming.weaken,
PartialRawRenaming.dropNewest)` pair, yielding the syntactic equation
`term = extracted.weaken` that the `Step.transpReflBeta` cd cascade
needs to convert an `unweaken? body = some inner` Option-match
witness into a definitional substitution equation.

## Root status

Kernel headline corollary; no axioms. -/

namespace LeanFX2

/-! ### Specialization: `dropNewest` injects back into the image of
`RawRenaming.weaken`.

The hypothesis required by `partialRename?_imp_rename` for the
`dropNewest` partial renaming.  By definition: `dropNewest ⟨0, _⟩ =
none` (impossible-to-witness branch) and `dropNewest ⟨k+1, _⟩ =
some ⟨k, _⟩`, while `RawRenaming.weaken ⟨k, _⟩ = ⟨k+1, _⟩` via
`Fin.succ`.  Pattern-match on the `Fin (scope+1)` index, discharge
the impossible branch via `cases`, and chain `injection` + `rfl`. -/
theorem PartialRawRenaming.dropNewest_renamingInjectsBack {scope : Nat} :
    ∀ (intermediatePos : Fin (scope + 1)) (sourcePos : Fin scope),
      PartialRawRenaming.dropNewest intermediatePos = some sourcePos →
      intermediatePos = RawRenaming.weaken sourcePos
  | ⟨0, _⟩, _, h => by cases h
  | ⟨_ + 1, _⟩, _, h => by
      injection h with sourceEq
      rw [← sourceEq]
      rfl

/-- Inversion for `unweaken?`: a successful `unweaken?` recovers the
syntactic equation `body = extracted.weaken`.  The headline lemma the
Step.transpReflBeta cd cascade needs to convert an Option-match
witness into a definitional substitution equation.  Strict
specialization of `partialRename?_imp_rename` to the canonical
`(RawRenaming.weaken, PartialRawRenaming.dropNewest)` pair. -/
theorem RawTerm.unweaken?_imp_weaken {scope : Nat}
    (term : RawTerm (scope + 1)) (extracted : RawTerm scope)
    (success : term.unweaken? = some extracted) :
    term = extracted.weaken :=
  RawTerm.partialRename?_imp_rename term RawRenaming.weaken
    PartialRawRenaming.dropNewest
    PartialRawRenaming.dropNewest_renamingInjectsBack
    extracted success

end LeanFX2
