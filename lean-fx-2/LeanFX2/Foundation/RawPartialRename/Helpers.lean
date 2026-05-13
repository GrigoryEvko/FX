import LeanFX2.Foundation.RenameIdentity

/-! # LeanFX2.Foundation.RawPartialRename.Helpers

`PartialRawRenaming` type, structural `lift`/`dropNewest` operators,
the two short post-lemmas that govern their interaction, and the
`Option.mapTwo`/`Option.mapThree` combinator helpers used to drive
the multi-child arms of `partialRename?`.

## Root status

Kernel pre-cascade infrastructure; no axioms. -/

namespace LeanFX2

/-- Partial renaming from one raw scope to another.  Returning `none`
means the source variable cannot be represented in the target scope. -/
def PartialRawRenaming (sourceScope targetScope : Nat) : Type :=
  Fin sourceScope → Option (Fin targetScope)

namespace PartialRawRenaming

/-- Lift a partial renaming under a raw binder.  The binder variable is
preserved; outer variables are delegated to the underlying partial
renaming and shifted when they survive. -/
@[reducible] def lift {sourceScope targetScope : Nat}
    (partialRenaming : PartialRawRenaming sourceScope targetScope) :
    PartialRawRenaming (sourceScope + 1) (targetScope + 1)
  | ⟨0, _⟩ => some ⟨0, Nat.zero_lt_succ _⟩
  | ⟨index + 1, indexLt⟩ =>
      match partialRenaming ⟨index, Nat.lt_of_succ_lt_succ indexLt⟩ with
      | some targetPosition => some (Fin.succ targetPosition)
      | none => none

/-- Drop the newest variable from a scope, if the variable being renamed
is not that newest variable. -/
@[reducible] def dropNewest {scope : Nat} :
    PartialRawRenaming (scope + 1) scope
  | ⟨0, _⟩ => none
  | ⟨index + 1, indexLt⟩ =>
      some ⟨index, Nat.lt_of_succ_lt_succ indexLt⟩

/-- Dropping after weakening recovers the original variable. -/
theorem dropNewest_weaken {scope : Nat} (position : Fin scope) :
    dropNewest (RawRenaming.weaken position) = some position := rfl

/-- Lifted dropping after lifted weakening recovers the original variable,
including the preserved binder case. -/
theorem lift_dropNewest_weaken_lift {scope : Nat} :
    ∀ position : Fin (scope + 1),
      (lift dropNewest) (RawRenaming.lift RawRenaming.weaken position) =
        some position
  | ⟨0, _⟩ => rfl
  | ⟨index + 1, indexLt⟩ => by
      cases index with
      | zero => rfl
      | succ priorIndex => rfl

end PartialRawRenaming

/-- Combine two optional results. -/
def Option.mapTwo
    {firstType secondType resultType : Type}
    (firstOption : Option firstType)
    (secondOption : Option secondType)
    (combine : firstType → secondType → resultType) :
    Option resultType :=
  match firstOption with
  | some firstValue =>
      match secondOption with
      | some secondValue => some (combine firstValue secondValue)
      | none => none
  | none => none

/-- Combine three optional results. -/
def Option.mapThree
    {firstType secondType thirdType resultType : Type}
    (firstOption : Option firstType)
    (secondOption : Option secondType)
    (thirdOption : Option thirdType)
    (combine : firstType → secondType → thirdType → resultType) :
    Option resultType :=
  match firstOption with
  | some firstValue =>
      match secondOption with
      | some secondValue =>
          match thirdOption with
          | some thirdValue => some (combine firstValue secondValue thirdValue)
          | none => none
      | none => none
  | none => none

end LeanFX2
