import LeanFX2.Term.PartialStrengthen.Weaken
import LeanFX2.Term.PartialStrengthen.RenameImage.TypeCodes
import LeanFX2.Term.PartialStrengthen.RenameImage.RefineSession
import LeanFX2.Term.PartialStrengthen.RenameImage.Equivalence
import LeanFX2.Term.PartialStrengthen.RenameImage.Cubical
import LeanFX2.Term.PartialStrengthen.RenameImage.CodataProjection
import LeanFX2.Term.PartialStrengthen.RenameImage.Effects
import LeanFX2.Term.PartialStrengthen.RenameImage.CastWrapped
import LeanFX2.Term.HEqCongr.Compound.EliminatorsAndRecursive
import LeanFX2.Term.HEqCongr.Atomic.Base
import LeanFX2.Term.HEqCongr.Atomic.Cubical
import LeanFX2.Term.HEqCongr.Atomic.Structural
import LeanFX2.Term.HEqCongr.Atomic.TypeCodes
import LeanFX2.Term.HEqCongr.Atomic.HeterogeneousIntro
import LeanFX2.Term.Pointwise.PointwiseAndCompositionInfrastructure.CastHEq

/-! # Term/StrengtheningImage/Core

Core semantic soundness record and simple strengthening-producer soundness lemmas.
-/

namespace LeanFX2

namespace Term

universe u v

/-- Term-level semantic soundness for a typed strengthening result.

The target term, renamed through the strengthening's forward morphism, is
heterogeneously equal to the source term.  Heterogeneous equality is the
right equality here because `StrengtheningResult.renamedTarget` carries
the renamed target indices, while the source term carries the original
indices; the record's `typeRenames` and `rawRenames` fields explain that
these indices are propositionally equal. -/
structure StrengtheningSoundness {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sourceType : Ty level sourceScope}
    {sourceRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {sourceTerm : Term sourceCtx sourceType sourceRaw}
    (result : StrengtheningResult strengthening sourceTerm) where
  termRenames : HEq sourceTerm result.renamedTarget

/-- Heterogeneous equality between a value and a cast of that same value
on the right.  This isolates the `Eq.rec` bookkeeping used by the variable
case of `Term.rename`. -/
theorem heq_cast_right {indexType : Sort u} {motive : indexType → Sort v}
    {firstIndex secondIndex : indexType}
    (indexEq : firstIndex = secondIndex)
    (value : motive secondIndex) :
    HEq value (indexEq ▸ value) := by
  cases indexEq
  rfl

/-- Heterogeneous equality between a value and a cast of that same value
on the left.  Dependent eliminators use this orientation when `Term.rename`
casts a constructor built at the pre-commuted `subst0` type into the
post-commuted type. -/
theorem heq_cast_left {indexType : Sort u} {motive : indexType → Sort v}
    {firstIndex secondIndex : indexType}
    (indexEq : firstIndex = secondIndex)
    (value : motive firstIndex) :
    HEq value (indexEq ▸ value) := by
  cases indexEq
  rfl

/-- Renaming a variable is heterogeneously equal to the variable at the
renamed position.  `Term.rename` casts this variable across the
`TermRenaming` proof; this lemma packages the cast proof once for
strengthening soundness. -/
theorem rename_var_heq {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (position : Fin sourceScope) :
    HEq (Term.var (context := targetCtx) (rho position))
      (Term.rename termRenaming (Term.var (context := sourceCtx) position)) := by
  change HEq (Term.var (context := targetCtx) (rho position))
    ((termRenaming position).symm ▸
      Term.var (context := targetCtx) (rho position))
  exact heq_cast_right
    (motive := fun variableType =>
      Term targetCtx variableType (RawTerm.var (rho position)))
    (termRenaming position).symm
    (Term.var (context := targetCtx) (rho position))

/-- Soundness for the surviving-variable strengthening producer. -/
theorem partialStrengthenTypedVarOfSurvives_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (sourcePosition : Fin sourceScope)
    (targetPosition : Fin targetScope)
    (survives : strengthening.back sourcePosition = some targetPosition) :
    StrengtheningSoundness
      (partialStrengthenTypedVarOfSurvives strengthening sourcePosition
        targetPosition survives) := by
  refine ⟨?_⟩
  unfold StrengtheningResult.renamedTarget
  dsimp [partialStrengthenTypedVarOfSurvives]
  have positionEq : sourcePosition = strengthening.forward targetPosition :=
    strengthening.injectsBack sourcePosition targetPosition survives
  cases positionEq
  exact rename_var_heq strengthening.toTermRenaming targetPosition

/-- Soundness for closed unit strengthening. -/
theorem partialStrengthenTypedUnit_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx) :
    StrengtheningSoundness (partialStrengthenTypedUnit strengthening) := by
  exact ⟨HEq.rfl⟩

/-- Soundness for closed boolean-true strengthening. -/
theorem partialStrengthenTypedBoolTrue_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx) :
    StrengtheningSoundness (partialStrengthenTypedBoolTrue strengthening) := by
  exact ⟨HEq.rfl⟩

/-- Soundness for closed boolean-false strengthening. -/
theorem partialStrengthenTypedBoolFalse_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx) :
    StrengtheningSoundness (partialStrengthenTypedBoolFalse strengthening) := by
  exact ⟨HEq.rfl⟩

/-- Soundness for closed natural-zero strengthening. -/
theorem partialStrengthenTypedNatZero_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx) :
    StrengtheningSoundness (partialStrengthenTypedNatZero strengthening) := by
  exact ⟨HEq.rfl⟩

/-- Soundness for closed interval-zero strengthening. -/
theorem partialStrengthenTypedInterval0_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx) :
    StrengtheningSoundness (partialStrengthenTypedInterval0 strengthening) := by
  exact ⟨HEq.rfl⟩

/-- Soundness for closed interval-one strengthening. -/
theorem partialStrengthenTypedInterval1_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx) :
    StrengtheningSoundness (partialStrengthenTypedInterval1 strengthening) := by
  exact ⟨HEq.rfl⟩

/-- Soundness for list-nil strengthening at a strengthened element type. -/
theorem partialStrengthenTypedListNilOfType_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (elementType : Ty level sourceScope)
    (targetElementType : Ty level targetScope)
    (elementTypeStrengthens :
      elementType.partialStrengthen? strengthening.back =
        some targetElementType) :
    StrengtheningSoundness
      (partialStrengthenTypedListNilOfType strengthening elementType
        targetElementType elementTypeStrengthens) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedListNilOfType,
    StrengtheningResult.renamedTarget]
  have elementTypeRenames :
      elementType = targetElementType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename elementType strengthening.forward
      strengthening.back strengthening.injectsBack targetElementType
      elementTypeStrengthens
  exact Term.listNil_HEq_congr elementTypeRenames

/-- Soundness for option-none strengthening at a strengthened element type. -/
theorem partialStrengthenTypedOptionNoneOfType_sound {mode : Mode}
    {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (elementType : Ty level sourceScope)
    (targetElementType : Ty level targetScope)
    (elementTypeStrengthens :
      elementType.partialStrengthen? strengthening.back =
        some targetElementType) :
    StrengtheningSoundness
      (partialStrengthenTypedOptionNoneOfType strengthening elementType
        targetElementType elementTypeStrengthens) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedOptionNoneOfType,
    StrengtheningResult.renamedTarget]
  have elementTypeRenames :
      elementType = targetElementType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename elementType strengthening.forward
      strengthening.back strengthening.injectsBack targetElementType
      elementTypeStrengthens
  exact Term.optionNone_HEq_congr elementTypeRenames

/-- Soundness for natural-successor strengthening. -/
theorem partialStrengthenTypedNatSucc_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {predecessorRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {predecessor : Term sourceCtx Ty.nat predecessorRaw}
    {predecessorResult : StrengtheningResult strengthening predecessor}
    (predecessorSound : StrengtheningSoundness predecessorResult) :
    StrengtheningSoundness
      (partialStrengthenTypedNatSucc predecessorResult) := by
  cases predecessorResult with
  | mk targetType targetRaw targetTerm typeStrengthens rawStrengthens
      typeRenames rawRenames =>
      cases typeStrengthens
      refine ⟨?_⟩
      dsimp [partialStrengthenTypedNatSucc, StrengtheningResult.renamedTarget]
        at predecessorSound ⊢
      exact Term.natSucc_HEq_congr rawRenames
        predecessorSound.termRenames

/-- Soundness for option-some strengthening. -/
theorem partialStrengthenTypedOptionSome_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {elementType : Ty level sourceScope}
    {valueRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {valueTerm : Term sourceCtx elementType valueRaw}
    {valueResult : StrengtheningResult strengthening valueTerm}
    (valueSound : StrengtheningSoundness valueResult) :
    StrengtheningSoundness
      (partialStrengthenTypedOptionSome valueResult) := by
  cases valueResult with
  | mk targetType targetRaw targetTerm typeStrengthens rawStrengthens
      typeRenames rawRenames =>
      refine ⟨?_⟩
      dsimp [partialStrengthenTypedOptionSome,
          StrengtheningResult.renamedTarget] at valueSound ⊢
      exact Term.optionSome_HEq_congr typeRenames rawRenames
        valueSound.termRenames

end Term

end LeanFX2
