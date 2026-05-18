import LeanFX2.Term.Rename
import LeanFX2.Foundation.TyStrengthen
import LeanFX2.Foundation.RenameIdentity

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

/-- Lift a context strengthening under one freshly-bound variable.

The new source binding must itself strengthen to the new target binding;
outer variables use the lifted partial/total renamings, while binder
position zero is preserved on both sides. -/
def lift {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (sourceNewType : Ty level sourceScope)
    (targetNewType : Ty level targetScope)
    (newTypeStrengthens :
      sourceNewType.partialStrengthen? strengthening.back =
        some targetNewType) :
    ContextStrengthening
      (sourceCtx.cons sourceNewType) (targetCtx.cons targetNewType) where
  back := strengthening.back.lift
  forward := strengthening.forward.lift
  back_forward := by
    intro targetPosition
    cases targetPosition with
    | mk targetIndex targetIsLt =>
        cases targetIndex with
        | zero => rfl
        | succ targetPriorIndex =>
            change
              strengthening.back.lift
                  (RawRenaming.lift strengthening.forward
                    ⟨targetPriorIndex + 1, targetIsLt⟩) =
                some ⟨targetPriorIndex + 1, targetIsLt⟩
            simp only [PartialRawRenaming.lift, RawRenaming.lift, Fin.succ]
            rw [strengthening.back_forward
              ⟨targetPriorIndex, Nat.lt_of_succ_lt_succ targetIsLt⟩]
  injectsBack :=
    PartialRawRenaming.lift_renamingInjectsBack strengthening.injectsBack
  varTypeStrengthens := by
    intro sourcePosition targetPosition survives
    cases sourcePosition with
    | mk sourceIndex sourceIsLt =>
        cases sourceIndex with
        | zero =>
            cases targetPosition with
            | mk targetIndex targetIsLt =>
                cases targetIndex with
                | zero =>
                    change
                      sourceNewType.weaken.partialStrengthen?
                          strengthening.back.lift =
                        some targetNewType.weaken
                    rw [Ty.partialStrengthen?_weaken_lift
                      sourceNewType strengthening.back,
                      newTypeStrengthens]
                    rfl
                | succ targetPriorIndex =>
                    cases survives
        | succ sourcePriorIndex =>
            cases targetPosition with
            | mk targetIndex targetIsLt =>
                cases targetIndex with
                | zero =>
                    simp only [PartialRawRenaming.lift] at survives
                    cases hBack :
                        strengthening.back
                          ⟨sourcePriorIndex,
                            Nat.lt_of_succ_lt_succ sourceIsLt⟩ with
                    | none =>
                        rw [hBack] at survives
                        cases survives
                    | some targetPriorPosition =>
                        rw [hBack] at survives
                        cases survives
                | succ targetPriorIndex =>
                    simp only [PartialRawRenaming.lift] at survives
                    have innerSurvives :
                        strengthening.back
                            ⟨sourcePriorIndex,
                              Nat.lt_of_succ_lt_succ sourceIsLt⟩ =
                          some
                            ⟨targetPriorIndex,
                              Nat.lt_of_succ_lt_succ targetIsLt⟩ := by
                      cases hBack :
                          strengthening.back
                            ⟨sourcePriorIndex,
                              Nat.lt_of_succ_lt_succ sourceIsLt⟩ with
                      | none =>
                          rw [hBack] at survives
                          cases survives
                      | some targetPriorPosition =>
                          cases targetPriorPosition with
                          | mk actualTargetIndex actualTargetIsLt =>
                              rw [hBack] at survives
                              injection survives with succEq
                              have indexEq :
                                  actualTargetIndex = targetPriorIndex :=
                                Nat.succ.inj (congrArg Fin.val succEq)
                              cases indexEq
                              rfl
                    change
                      Ty.partialStrengthen?
                          ((varType sourceCtx
                            ⟨sourcePriorIndex,
                              Nat.lt_of_succ_lt_succ sourceIsLt⟩).weaken)
                          strengthening.back.lift =
                        some
                          ((varType targetCtx
                              ⟨targetPriorIndex,
                                Nat.lt_of_succ_lt_succ targetIsLt⟩).weaken)
                    rw [Ty.partialStrengthen?_weaken_lift
                      (varType sourceCtx
                        ⟨sourcePriorIndex,
                          Nat.lt_of_succ_lt_succ sourceIsLt⟩)
                      strengthening.back,
                      strengthening.varTypeStrengthens
                        ⟨sourcePriorIndex,
                          Nat.lt_of_succ_lt_succ sourceIsLt⟩
                        ⟨targetPriorIndex,
                          Nat.lt_of_succ_lt_succ targetIsLt⟩
                        innerSurvives]
                    rfl

/-- Strengthening obtained from an injective typed renaming.

Given a total source-to-target `renaming` whose typed companion
`typedRenaming` preserves variable types, plus a partial left-inverse
`renameInverse : PartialRawRenaming targetScope sourceScope` witnessing
injectivity of `renaming`, build a `ContextStrengthening targetCtx
sourceCtx`.

The contract laws follow:
* `back := renameInverse`, `forward := renaming` — supplied as inputs.
* `back_forward` — exactly `renameInverseLeft` (the left-inverse law).
* `injectsBack` — exactly `renameInverseInjects` (the partial-inverse
  pointwise identification law).
* `varTypeStrengthens` — follows from
  `Ty.partialStrengthen?_rename_some` applied at `sourceRenaming :=
  renaming` and `targetRenaming := RawRenaming.identity`, then closed
  via `Ty.rename_identity`.

This is the keystone constructor for strength-T1
(`Term.strengthenTyped?_rename_eq`): the per-ctor structural induction
operates against the strengthening induced by an arbitrary injective
renaming, not just `dropNewest`. -/
def ofRenaming
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
    ContextStrengthening targetCtx sourceCtx where
  back := renameInverse
  forward := forwardRename
  back_forward := renameInverseLeft
  injectsBack := renameInverseInjects
  varTypeStrengthens := by
    intro targetPosition sourcePosition survives
    have positionIsImage :=
      renameInverseInjects targetPosition sourcePosition survives
    have typedEvidence := typedRenaming sourcePosition
    rw [positionIsImage, typedEvidence]
    have inverseAtIdentity :
        ∀ probe,
          renameInverse (forwardRename probe) =
            some (@RawRenaming.identity sourceScope probe) :=
      renameInverseLeft
    rw [Ty.partialStrengthen?_rename_some
      (varType sourceCtx sourcePosition) forwardRename
      (@RawRenaming.identity sourceScope) renameInverse inverseAtIdentity,
      Ty.rename_identity (varType sourceCtx sourcePosition)]

end ContextStrengthening

end LeanFX2
