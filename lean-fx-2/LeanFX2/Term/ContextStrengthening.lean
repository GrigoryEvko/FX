import LeanFX2.Term.Rename
import LeanFX2.Foundation.TyStrengthen

/-! # Context strengthening morphisms.

`RawTerm.partialStrengthen?` and `Ty.partialStrengthen?` explain how
syntax survives a partial renaming.  A typed term also needs a context
contract: every surviving source variable must land at a target
variable whose `varType` is the strengthened source `varType`.

This module packages that contract and derives the forward
`TermRenaming` used by future typed strengthening soundness theorems.
-/

namespace LeanFX2

/-- A partial strengthening from `sourceCtx` to `targetCtx`.

`back` is the partial map from source variables to surviving target
variables.  `forward` embeds target variables back into source scope.
The two laws say `back` is a left inverse of `forward` on the target
and that every successful `back` result is explained by `forward`.
The final field is the typed-context law: surviving variable types
strengthen from the source context into the target context. -/
structure ContextStrengthening {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    (sourceCtx : Ctx mode level sourceScope)
    (targetCtx : Ctx mode level targetScope) where
  back : PartialRawRenaming sourceScope targetScope
  forward : RawRenaming targetScope sourceScope
  back_forward : ∀ targetPosition, back (forward targetPosition) = some targetPosition
  injectsBack :
    ∀ sourcePosition targetPosition,
      back sourcePosition = some targetPosition →
      sourcePosition = forward targetPosition
  varTypeStrengthens :
    ∀ sourcePosition targetPosition,
      back sourcePosition = some targetPosition →
      (varType sourceCtx sourcePosition).partialStrengthen? back =
        some (varType targetCtx targetPosition)

namespace ContextStrengthening

/-- Any context strengthening induces the forward typed renaming from the
target context back into the source context. -/
theorem toTermRenaming {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx) :
    TermRenaming targetCtx sourceCtx strengthening.forward := by
  intro targetPosition
  exact Ty.partialStrengthen?_imp_rename
    (varType sourceCtx (strengthening.forward targetPosition))
    strengthening.forward strengthening.back strengthening.injectsBack
    (varType targetCtx targetPosition)
    (strengthening.varTypeStrengthens
      (strengthening.forward targetPosition) targetPosition
      (strengthening.back_forward targetPosition))

/-- Canonical single-newest-slot strengthening from `context.cons
newType` back to `context`. -/
def dropNewest {mode : Mode} {level scope : Nat}
    (context : Ctx mode level scope) (newType : Ty level scope) :
    ContextStrengthening (context.cons newType) context where
  back := PartialRawRenaming.dropNewest
  forward := RawRenaming.weaken
  back_forward := PartialRawRenaming.dropNewest_weaken
  injectsBack := PartialRawRenaming.dropNewest_renamingInjectsBack
  varTypeStrengthens := by
    intro sourcePosition targetPosition survives
    cases sourcePosition with
    | mk sourceIndex sourceIsLt =>
      cases sourceIndex with
      | zero =>
          cases survives
      | succ previousIndex =>
          injection survives with targetEq
          rw [← targetEq]
          show (varType context ⟨previousIndex,
              Nat.lt_of_succ_lt_succ sourceIsLt⟩).weaken.strengthen? =
            some (varType context ⟨previousIndex,
              Nat.lt_of_succ_lt_succ sourceIsLt⟩)
          exact Ty.strengthen?_weaken
            (varType context ⟨previousIndex,
              Nat.lt_of_succ_lt_succ sourceIsLt⟩)

/-- The forward typed renaming induced by `dropNewest` is the ordinary
weakening step. -/
theorem dropNewest_toTermRenaming {mode : Mode} {level scope : Nat}
    (context : Ctx mode level scope) (newType : Ty level scope) :
    (dropNewest context newType).toTermRenaming =
      TermRenaming.weakenStep context newType := rfl

end ContextStrengthening

end LeanFX2
