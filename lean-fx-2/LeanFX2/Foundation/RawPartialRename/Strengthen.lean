import LeanFX2.Foundation.RawPartialRename.UnweakenInversion

/-! # Raw partial strengthening.

This module gives stable names to the strengthening side of
`RawTerm.partialRename?`.

* `RawTerm.partialStrengthen?` is the general multi-slot raw
  strengthening primitive.  It is definitionally the existing partial
  renaming function, viewed from the eliminator direction.
* `RawTerm.strengthen?` is the single-newest-slot specialization.
* `RawTerm.usesNewestSlot?` is the semantic predicate for whether the
  newest de Bruijn slot blocks strengthening.

The typed `Term` layer can safely build on these certificates without
pretending that raw strengthening alone reconstructs a typed predecessor:
the type index needs its own strengthening proof. -/

namespace LeanFX2

/-- General raw partial strengthening.

The `back` partial renaming describes which source variables survive in
the smaller target scope.  The result is `some strengthened` exactly when
every variable occurrence in `term` survives `back`, with binders handled
by `PartialRawRenaming.lift` inside `RawTerm.partialRename?`. -/
@[reducible] def RawTerm.partialStrengthen? {sourceScope targetScope : Nat}
    (term : RawTerm sourceScope)
    (back : PartialRawRenaming sourceScope targetScope) :
    Option (RawTerm targetScope) :=
  RawTerm.partialRename? term back

/-- Naming bridge: partial strengthening is the eliminator-facing view of
partial renaming. -/
theorem RawTerm.partialStrengthen?_eq_partialRename?
    {sourceScope targetScope : Nat}
    (term : RawTerm sourceScope)
    (back : PartialRawRenaming sourceScope targetScope) :
    RawTerm.partialStrengthen? term back =
      RawTerm.partialRename? term back := rfl

/-- A successful raw partial strengthening reconstructs the original raw
term by renaming the strengthened result forward, provided `back`
injects into the image of that forward renaming. -/
theorem RawTerm.partialStrengthen?_imp_rename
    {sourceScope intermediateScope : Nat}
    (body : RawTerm intermediateScope)
    (forwardRenaming : RawRenaming sourceScope intermediateScope)
    (back : PartialRawRenaming intermediateScope sourceScope)
    (renamingInjectsBack :
      ∀ (intermediatePos : Fin intermediateScope)
        (sourcePos : Fin sourceScope),
        back intermediatePos = some sourcePos →
        intermediatePos = forwardRenaming sourcePos)
    (extracted : RawTerm sourceScope)
    (success : RawTerm.partialStrengthen? body back = some extracted) :
    body = extracted.rename forwardRenaming :=
  RawTerm.partialRename?_imp_rename body forwardRenaming back
    renamingInjectsBack extracted success

/-- If a partial strengthening accepts every variable produced by a
total source renaming, it accepts the whole source-renamed raw term and
produces the corresponding target-renamed raw term. -/
theorem RawTerm.partialStrengthen?_rename_some
    {sourceScope middleScope targetScope : Nat}
    (term : RawTerm sourceScope)
    (sourceRenaming : RawRenaming sourceScope middleScope)
    (targetRenaming : RawRenaming sourceScope targetScope)
    (back : PartialRawRenaming middleScope targetScope)
    (renamingSurvives :
      ∀ position, back (sourceRenaming position) =
        some (targetRenaming position)) :
    RawTerm.partialStrengthen? (term.rename sourceRenaming) back =
      some (term.rename targetRenaming) :=
  RawTerm.partialRename?_rename_some term sourceRenaming targetRenaming
    back renamingSurvives

/-- Single-newest-slot raw strengthening.  This is the semantic twin of
`RawTerm.unweaken?`, with a name that matches typed strengthening
call-sites. -/
@[reducible] def RawTerm.strengthen? {scope : Nat}
    (term : RawTerm (scope + 1)) : Option (RawTerm scope) :=
  RawTerm.partialStrengthen? term PartialRawRenaming.dropNewest

/-- Does `term` mention the newest outer slot?

For de Bruijn scope `scope + 1`, newest slot means index `0` at the
outer level.  Under binders, `PartialRawRenaming.lift` preserves binder
index `0` and drops the shifted outer slot, so this predicate has the
right binder semantics for strengthening. -/
def RawTerm.usesNewestSlot? {scope : Nat}
    (term : RawTerm (scope + 1)) : Bool :=
  (RawTerm.strengthen? term).isNone

/-- Strengthening a weakened raw term recovers the original raw term. -/
theorem RawTerm.strengthen?_weaken {scope : Nat}
    (term : RawTerm scope) :
    RawTerm.strengthen? term.weaken = some term :=
  RawTerm.unweaken?_weaken term

/-- Successful single-slot strengthening gives the canonical weakening
equation. -/
theorem RawTerm.strengthen?_imp_weaken {scope : Nat}
    (term : RawTerm (scope + 1)) (extracted : RawTerm scope)
    (success : RawTerm.strengthen? term = some extracted) :
    term = extracted.weaken :=
  RawTerm.unweaken?_imp_weaken term extracted success

/-- A raw term that semantically avoids the newest slot is syntactically
a weakening of a term in the previous scope. -/
theorem RawTerm.not_usesNewestSlot?_imp_weaken {scope : Nat}
    (term : RawTerm (scope + 1))
    (slotIsUnused : RawTerm.usesNewestSlot? term = false) :
    ∃ extracted : RawTerm scope, term = extracted.weaken := by
  unfold RawTerm.usesNewestSlot? at slotIsUnused
  unfold RawTerm.strengthen? at slotIsUnused
  unfold RawTerm.partialStrengthen? at slotIsUnused
  cases success : RawTerm.partialRename? term PartialRawRenaming.dropNewest with
  | none =>
      rw [success] at slotIsUnused
      cases slotIsUnused
  | some extracted =>
      have unweakenSuccess : RawTerm.unweaken? term = some extracted := success
      exact ⟨extracted, RawTerm.unweaken?_imp_weaken term extracted unweakenSuccess⟩

/-- Weakened raw terms do not use the newest slot. -/
theorem RawTerm.weaken_not_usesNewestSlot? {scope : Nat}
    (term : RawTerm scope) :
    RawTerm.usesNewestSlot? term.weaken = false := by
  unfold RawTerm.usesNewestSlot?
  rw [RawTerm.strengthen?_weaken term]
  rfl

end LeanFX2
