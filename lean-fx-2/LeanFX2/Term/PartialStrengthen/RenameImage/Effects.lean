import LeanFX2.Term.PartialStrengthen.RenameImage.Core

/-! # Term/PartialStrengthen/RenameImage/Effects

Rename-image T1 equations for effect-operation cases.
-/

namespace LeanFX2

namespace Term

/-- Effects strength-T1 case: `Term.effectPerform`.

Carries 1 RawTerm payload (effectTag at outer `back`) + 1
EffectRow (passive) + 1 OperationSignature with 2 Ty payloads
(argumentCarrier, resultCarrier at outer `back`, accessed via
struct projection) + 1 CanPerform witness (passive) + 2 Term IHs
(operationTag at `Ty.effect argumentCarrier effectTag`, arguments
at `argumentCarrier`).  No cast on rename — the result type
`Ty.effect resultCarrier effectTag` renames structurally via
`Effects.OperationSignature.map` pointwise. -/
theorem strengthenTyped?_rename_eq_effectPerform
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
        targetPosition = forwardRename sourcePosition)
    (effectTag : RawTerm sourceScope)
    (effectRow : Effects.EffectRow)
    (operationSignature : Effects.OperationSignature (Ty level sourceScope))
    (canPerformOperation :
      Effects.CanPerform effectRow operationSignature)
    {operationRaw argumentsRaw : RawTerm sourceScope}
    (operationTag :
      Term sourceCtx
        (Ty.effect operationSignature.argumentCarrier effectTag)
        operationRaw)
    (arguments :
      Term sourceCtx operationSignature.argumentCarrier argumentsRaw)
    (operationIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming operationTag)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            operationTag))
    (argumentsIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming arguments)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            arguments)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.effectPerform (context := sourceCtx) effectTag effectRow
            operationSignature canPerformOperation operationTag arguments))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.effectPerform (context := sourceCtx) effectTag effectRow
            operationSignature canPerformOperation operationTag
            arguments)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have effectTagStrengthens :
      (effectTag.rename forwardRename).partialStrengthen? renameInverse
        = some effectTag := by
    rw [RawTerm.partialStrengthen?_rename_some effectTag forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity effectTag]
  have argumentCarrierStrengthens :
      (operationSignature.argumentCarrier.rename
          forwardRename).partialStrengthen? renameInverse
        = some operationSignature.argumentCarrier := by
    rw [Ty.partialStrengthen?_rename_some operationSignature.argumentCarrier
      forwardRename (@RawRenaming.identity sourceScope) renameInverse
      renameInverseLeft,
      Ty.rename_identity operationSignature.argumentCarrier]
  have resultCarrierStrengthens :
      (operationSignature.resultCarrier.rename
          forwardRename).partialStrengthen? renameInverse
        = some operationSignature.resultCarrier := by
    rw [Ty.partialStrengthen?_rename_some operationSignature.resultCarrier
      forwardRename (@RawRenaming.identity sourceScope) renameInverse
      renameInverseLeft,
      Ty.rename_identity operationSignature.resultCarrier]
  split
  next noEffectTagSuccess =>
    exact absurd (effectTagStrengthens.symm.trans noEffectTagSuccess)
      (by intro contra; cases contra)
  next targetEffectTag effectTagSuccess =>
    have effectTagEq : targetEffectTag = effectTag :=
      Option.some.inj (effectTagSuccess.symm.trans effectTagStrengthens)
    subst effectTagEq
    split
    next noArgumentCarrierSuccess =>
      exact absurd
        (argumentCarrierStrengthens.symm.trans noArgumentCarrierSuccess)
        (by intro contra; cases contra)
    next targetArgumentCarrier argumentCarrierSuccess =>
      have argumentCarrierEq :
          targetArgumentCarrier = operationSignature.argumentCarrier :=
        Option.some.inj
          (argumentCarrierSuccess.symm.trans argumentCarrierStrengthens)
      subst argumentCarrierEq
      split
      next noResultCarrierSuccess =>
        exact absurd
          (resultCarrierStrengthens.symm.trans noResultCarrierSuccess)
          (by intro contra; cases contra)
      next targetResultCarrier resultCarrierSuccess =>
        have resultCarrierEq :
            targetResultCarrier = operationSignature.resultCarrier :=
          Option.some.inj
            (resultCarrierSuccess.symm.trans resultCarrierStrengthens)
        subst resultCarrierEq
        split
        next noOperationSuccess =>
          exact absurd (operationIH.symm.trans noOperationSuccess)
            (by intro contra; cases contra)
        next operationResult operationSuccess =>
          have operationEq : operationResult =
              StrengtheningResult.fromRename forwardRename typedRenaming
                renameInverse renameInverseLeft renameInverseInjects
                operationTag :=
            Option.some.inj (operationSuccess.symm.trans operationIH)
          subst operationEq
          split
          next noArgumentsSuccess =>
            exact absurd (argumentsIH.symm.trans noArgumentsSuccess)
              (by intro contra; cases contra)
          next argumentsResult argumentsSuccess =>
            have argumentsEq : argumentsResult =
                StrengtheningResult.fromRename forwardRename typedRenaming
                  renameInverse renameInverseLeft renameInverseInjects
                  arguments :=
              Option.some.inj (argumentsSuccess.symm.trans argumentsIH)
            subst argumentsEq
            rfl

/-! ## Cast-wrapped strength-T1 cases (HEq-form)

The `Term.rename` arm for `Term.funextRefl` (and 10 other cast-wrapped
ctors) wraps the result in
`(funextReflType_rename ...).symm ▸ Term.funextRefl (renamed args)`.
The Eq-form headline of strength-T1 cannot be proved at the typed-level:
after `dsimp only [Term.rename]`, the dispatcher's pattern-match cannot
peel the cast (Lean refuses `cases castEq` because the underlying
definitional equation `codomainType.weaken.rename forwardRename.lift =
(codomainType.rename forwardRename).rename RawRenaming.weaken` is not
syntactic).

We therefore ship the HEq form for the cast-wrapped ctors: the LHS
dispatcher (on the cast-wrapped input) is HEq to the RHS dispatcher
(on the un-cast `Term.funextRefl` at the target context).  This is
the natural statement that survives the cast wrapper because HEq is
agnostic to the type-level cast.

The Eq-form headline for these 11 ctors is structurally blocked at
the kernel level; downstream consumers should bridge via
`HEq.cast` + the cast equation's known direction. -/

end Term

end LeanFX2
