import LeanFX.Syntax.Strengthen
import LeanFX.Syntax.TypedTerm

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## Typed strengthening results.

`Ty.strengthen` and `RawTerm.strengthen` recover syntax from the image
of weakening.  Typed terms need one more piece of data: the recovered
type.  A term in an extended context has some extended type
`extendedType`; when strengthening succeeds we return the original type,
the proof that weakening it gives `extendedType`, and the recovered term
at that original type.
-/

/-- A successfully strengthened term packaged with its recovered type. -/
structure StrengthenedTerm {mode : Mode} {scope : Nat}
    (context : Ctx mode level scope) (extendedType : Ty level (scope + 1)) where
  /-- The type before weakening. -/
  originalType : Ty level scope
  /-- Weakening the recovered type reconstructs the extended type. -/
  typeEquality : originalType.weaken = extendedType
  /-- The recovered term at the recovered type. -/
  term : Term context originalType

namespace StrengthenedTerm

/-- If the extended type strengthens to a chosen expected type, the
recovered type in a `StrengthenedTerm` is that expected type. -/
theorem original_eq_of_strengthen {mode : Mode} {scope : Nat}
    {context : Ctx mode level scope}
    {extendedType : Ty level (scope + 1)} {expectedType : Ty level scope}
    (strengthenedTerm : StrengthenedTerm context extendedType)
    (expectedStrengthening : extendedType.strengthen = some expectedType) :
    strengthenedTerm.originalType = expectedType := by
  have recoveredStrengthening :
      extendedType.strengthen = some strengthenedTerm.originalType :=
    (Ty.strengthen_eq_some_iff_weaken
      extendedType strengthenedTerm.originalType).mpr strengthenedTerm.typeEquality
  exact Option.some.inj (recoveredStrengthening.symm.trans expectedStrengthening)

/-- Cast the recovered term to an expected type when the extended type
strengthens to that expected type. -/
def termAs {mode : Mode} {scope : Nat}
    {context : Ctx mode level scope}
    {extendedType : Ty level (scope + 1)} {expectedType : Ty level scope}
    (strengthenedTerm : StrengthenedTerm context extendedType)
    (expectedStrengthening : extendedType.strengthen = some expectedType) :
    Term context expectedType :=
  (original_eq_of_strengthen strengthenedTerm expectedStrengthening) ▸
    strengthenedTerm.term

end StrengthenedTerm

/-! ## Context compatibility for typed optional renaming. -/

/-- A typed optional renaming is compatible with source and target
contexts when every successful variable-position mapping also maps the
source variable type to the target variable type.  This is the typed
counterpart of `OptionalRenaming`: it supplies exactly the cast needed
to turn a successful variable mapping into a `Term.var` in the target
context. -/
def TermOptionalRenaming {mode : Mode} {sourceScope targetScope : Nat}
    (sourceContext : Ctx mode level sourceScope)
    (targetContext : Ctx mode level targetScope)
    (optionalRenaming : OptionalRenaming sourceScope targetScope) : Prop :=
  ∀ sourcePosition targetPosition,
    optionalRenaming sourcePosition = some targetPosition →
      (varType sourceContext sourcePosition).optRename optionalRenaming =
        some (varType targetContext targetPosition)

namespace TermOptionalRenaming

/-- Dropping the newest context variable is compatible with the prefix
context: variable 0 is unmapped, and every successor variable's type is
itself a weakening of the corresponding prefix variable type. -/
theorem unweaken {mode : Mode} {scope : Nat}
    (context : Ctx mode level scope) (newType : Ty level scope) :
    TermOptionalRenaming (context.cons newType) context
      OptionalRenaming.unweaken := by
  intro sourcePosition targetPosition positionMaps
  match sourcePosition with
  | ⟨0, _⟩ =>
      cases positionMaps
  | ⟨position + 1, isWithinSource⟩ =>
      cases positionMaps
      exact Ty.strengthen_weaken
        (varType context ⟨position, Nat.lt_of_succ_lt_succ isWithinSource⟩)

/-- Typed optional-renaming compatibility is stable under binders when
the binder type itself optional-renames successfully. -/
theorem lift {mode : Mode} {sourceScope targetScope : Nat}
    {sourceContext : Ctx mode level sourceScope}
    {targetContext : Ctx mode level targetScope}
    {optionalRenaming : OptionalRenaming sourceScope targetScope}
    {sourceType : Ty level sourceScope} {targetType : Ty level targetScope}
    (renamingIsCompatible :
      TermOptionalRenaming sourceContext targetContext optionalRenaming)
    (sourceTypeMaps : sourceType.optRename optionalRenaming = some targetType) :
    TermOptionalRenaming
      (sourceContext.cons sourceType) (targetContext.cons targetType)
      optionalRenaming.lift := by
  intro sourcePosition targetPosition positionMaps
  match sourcePosition with
  | ⟨0, _⟩ =>
      change some ⟨0, Nat.zero_lt_succ targetScope⟩ =
        some targetPosition at positionMaps
      cases positionMaps
      change sourceType.weaken.optRename optionalRenaming.lift =
        some targetType.weaken
      rw [Ty.weaken_optRename_lift optionalRenaming sourceType, sourceTypeMaps]
      rfl
  | ⟨sourceIndex + 1, isWithinSource⟩ =>
      let sourcePredecessor : Fin sourceScope :=
        ⟨sourceIndex, Nat.lt_of_succ_lt_succ isWithinSource⟩
      change Option.map Fin.succ (optionalRenaming sourcePredecessor) =
        some targetPosition at positionMaps
      cases predecessorMapping : optionalRenaming sourcePredecessor with
      | none =>
          rw [predecessorMapping] at positionMaps
          cases positionMaps
      | some targetPredecessor =>
          rw [predecessorMapping] at positionMaps
          cases positionMaps
          change
            (varType sourceContext sourcePredecessor).weaken.optRename
                optionalRenaming.lift =
              some (varType targetContext targetPredecessor).weaken
          rw [Ty.weaken_optRename_lift optionalRenaming
            (varType sourceContext sourcePredecessor)]
          rw [renamingIsCompatible sourcePredecessor
            targetPredecessor predecessorMapping]
          rfl

end TermOptionalRenaming

end LeanFX.Syntax
