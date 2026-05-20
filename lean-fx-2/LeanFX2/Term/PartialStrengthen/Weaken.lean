import LeanFX2.Term.PartialStrengthen.Dispatcher

/-! # Term/PartialStrengthen/Weaken

Typed newest-slot strengthening, unweakening, and use predicates built on
the universal partial-strengthening dispatcher.
-/

namespace LeanFX2

namespace Term

/-- Single-newest-slot typed strengthening.

This is the semantic strengthening variant for a term in
`context.cons newType`: it returns a fully typed predecessor exactly when
the type index, raw index, and every typed subterm survive
`PartialRawRenaming.dropNewest`.
-/
def strengthenTyped? {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {sourceType : Ty level (scope + 1)}
    {sourceRaw : RawTerm (scope + 1)}
    (sourceTerm : Term (context.cons newType) sourceType sourceRaw) :
    Option (StrengtheningResult
      (ContextStrengthening.dropNewest context newType) sourceTerm) :=
  partialStrengthenTyped? sourceTerm
    (ContextStrengthening.dropNewest context newType)

/-- Successful single-newest-slot typed strengthening gives the
canonical weakening equations for the source term's type and raw
indices.

This is the typed counterpart of
`Term.strengthen?_imp_indices_weaken`; it exposes the equations carried
by `StrengtheningResult` without making consumers destruct the result
record by hand.
-/
theorem strengthenTyped?_imp_indices_weaken
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {sourceType : Ty level (scope + 1)}
    {sourceRaw : RawTerm (scope + 1)}
    (sourceTerm : Term (context.cons newType) sourceType sourceRaw)
    (result : StrengtheningResult
      (ContextStrengthening.dropNewest context newType) sourceTerm)
    (_success : strengthenTyped? sourceTerm = some result) :
    sourceType = result.targetType.weaken ∧
      sourceRaw = result.targetRaw.weaken := by
  exact ⟨result.typeRenames, result.rawRenames⟩

/-- Typed newest-slot use predicate.

The predicate is deliberately defined by the typed strengthening
dispatcher, not only by raw syntax: `false` means a typed predecessor was
actually reconstructed through the context morphism.
-/
def usesNewestSlotTyped? {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {sourceType : Ty level (scope + 1)}
    {sourceRaw : RawTerm (scope + 1)}
    (sourceTerm : Term (context.cons newType) sourceType sourceRaw) :
    Bool :=
  (strengthenTyped? sourceTerm).isNone

/-- Structural typed unweakening.

When both indices are syntactically known weakenings, typed
strengthening reconstructs an exact predecessor at the original type and
raw indices.  The casts are justified by the existing all-constructors
type/raw facts `Ty.strengthen?_weaken` and `RawTerm.strengthen?_weaken`.
-/
def unweaken? {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType sourceType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (weakenedTerm :
      Term (context.cons newType) sourceType.weaken sourceRaw.weaken) :
    Option (Term context sourceType sourceRaw) :=
  match strengthenTyped? weakenedTerm with
  | none => none
  | some result =>
      match result with
      | StrengtheningResult.mk targetType targetRaw targetTerm
          typeStrengthens rawStrengthens _ _ =>
          have targetTypeEq : targetType = sourceType := by
            change sourceType.weaken.strengthen? = some targetType at typeStrengthens
            rw [Ty.strengthen?_weaken sourceType] at typeStrengthens
            cases typeStrengthens
            rfl
          have targetRawEq : targetRaw = sourceRaw := by
            change sourceRaw.weaken.strengthen? = some targetRaw at rawStrengthens
            rw [RawTerm.strengthen?_weaken sourceRaw] at rawStrengthens
            cases rawStrengthens
            rfl
          by
            cases targetTypeEq
            cases targetRawEq
            exact some targetTerm

/-- Semantic typed strengthening witness from the boolean predicate.

This is the typed counterpart of `not_usesNewestSlot?_imp_indices_weaken`:
the witness is a full `StrengtheningResult`, not just strengthened
indices.
-/
theorem not_usesNewestSlotTyped?_imp_strengthenTyped?_some
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {sourceType : Ty level (scope + 1)}
    {sourceRaw : RawTerm (scope + 1)}
    (sourceTerm : Term (context.cons newType) sourceType sourceRaw)
    (slotIsUnused : usesNewestSlotTyped? sourceTerm = false) :
    ∃ result : StrengtheningResult
        (ContextStrengthening.dropNewest context newType) sourceTerm,
      strengthenTyped? sourceTerm = some result := by
  unfold usesNewestSlotTyped? at slotIsUnused
  cases success : strengthenTyped? sourceTerm with
  | none =>
      rw [success] at slotIsUnused
      cases slotIsUnused
  | some result =>
      exact ⟨result, rfl⟩

end Term

end LeanFX2
