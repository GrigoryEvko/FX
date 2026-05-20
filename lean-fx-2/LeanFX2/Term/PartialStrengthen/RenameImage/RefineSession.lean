import LeanFX2.Term.PartialStrengthen.RenameImage.Core

/-! # Term/PartialStrengthen/RenameImage/RefineSession

Rename-image T1 equations for refinement and session structural cases.
-/

namespace LeanFX2

namespace Term

/-- HoTT-special strength-T1 case: `Term.refineIntro`.

Carries 1 binder-shape RawTerm payload (`predicate` at `scope+1` via
`back.lift`) plus 2 Term IHs (`baseValue` at `baseType` + `predicateProof`
at `Ty.unit`). -/
theorem strengthenTyped?_rename_eq_refineIntro
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
    {baseType : Ty level sourceScope}
    (predicate : RawTerm (sourceScope + 1))
    {valueRaw proofRaw : RawTerm sourceScope}
    (baseValue : Term sourceCtx baseType valueRaw)
    (predicateProof : Term sourceCtx Ty.unit proofRaw)
    (baseIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming baseValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            baseValue))
    (proofIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming predicateProof)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            predicateProof)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.refineIntro (context := sourceCtx) predicate baseValue
            predicateProof))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.refineIntro (context := sourceCtx) predicate baseValue
            predicateProof)) := by
  dsimp only [Term.rename, partialStrengthenTyped?]
  have predicateStrengthens :
      (predicate.rename forwardRename.lift).partialStrengthen?
          renameInverse.lift
        = some predicate := by
    rw [RawTerm.partialStrengthen?_rename_some predicate
      forwardRename.lift (@RawRenaming.identity sourceScope).lift
      renameInverse.lift
      (PartialRawRenaming.lift_rename_some renameInverseLeft),
      RawTerm.rename_pointwise
        (@RawRenaming.identity_lift_pointwise sourceScope) predicate,
      RawTerm.rename_identity predicate]
  split
  next noPredicateSuccess =>
    exact absurd (predicateStrengthens.symm.trans noPredicateSuccess)
      (by intro contra; cases contra)
  next targetPredicate predicateSuccess =>
    have predicateEq : targetPredicate = predicate :=
      Option.some.inj (predicateSuccess.symm.trans predicateStrengthens)
    subst predicateEq
    split
    next noBaseSuccess =>
      exact absurd (baseIH.symm.trans noBaseSuccess)
        (by intro contra; cases contra)
    next baseResult baseSuccess =>
      have baseEq : baseResult =
          StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects baseValue :=
        Option.some.inj (baseSuccess.symm.trans baseIH)
      subst baseEq
      split
      next noProofSuccess =>
        exact absurd (proofIH.symm.trans noProofSuccess)
          (by intro contra; cases contra)
      next proofResult proofSuccess =>
        have proofEq : proofResult =
            StrengtheningResult.fromRename forwardRename typedRenaming
              renameInverse renameInverseLeft renameInverseInjects
              predicateProof :=
          Option.some.inj (proofSuccess.symm.trans proofIH)
        subst proofEq
        rfl

/-- HoTT-special strength-T1 case: `Term.refineElim`.

Carries 1 Ty payload (`baseType` at outer `back`) + 1 binder-shape
RawTerm payload (`predicate` at `back.lift`) + 1 Term IH
(`refinedValue` at `Ty.refine baseType predicate`).  Both `baseType`
and `predicate` are implicit on the ctor — they reconstruct from the
refinedValue's type. -/
theorem strengthenTyped?_rename_eq_refineElim
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
    {baseType : Ty level sourceScope}
    {predicate : RawTerm (sourceScope + 1)}
    {refinedRaw : RawTerm sourceScope}
    (refinedValue : Term sourceCtx (Ty.refine baseType predicate) refinedRaw)
    (refinedIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming refinedValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            refinedValue)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.refineElim (context := sourceCtx) (baseType := baseType)
            (predicate := predicate) refinedValue))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.refineElim (context := sourceCtx) (baseType := baseType)
            (predicate := predicate) refinedValue)) := by
  dsimp only [Term.rename, partialStrengthenTyped?]
  have baseStrengthens :
      (baseType.rename forwardRename).partialStrengthen? renameInverse
        = some baseType := by
    rw [Ty.partialStrengthen?_rename_some baseType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity baseType]
  have predicateStrengthens :
      (predicate.rename forwardRename.lift).partialStrengthen?
          renameInverse.lift
        = some predicate := by
    rw [RawTerm.partialStrengthen?_rename_some predicate
      forwardRename.lift (@RawRenaming.identity sourceScope).lift
      renameInverse.lift
      (PartialRawRenaming.lift_rename_some renameInverseLeft),
      RawTerm.rename_pointwise
        (@RawRenaming.identity_lift_pointwise sourceScope) predicate,
      RawTerm.rename_identity predicate]
  split
  next noBaseSuccess =>
    exact absurd (baseStrengthens.symm.trans noBaseSuccess)
      (by intro contra; cases contra)
  next targetBaseType baseSuccess =>
    have baseEq : targetBaseType = baseType :=
      Option.some.inj (baseSuccess.symm.trans baseStrengthens)
    subst baseEq
    split
    next noPredicateSuccess =>
      exact absurd (predicateStrengthens.symm.trans noPredicateSuccess)
        (by intro contra; cases contra)
    next targetPredicate predicateSuccess =>
      have predicateEq : targetPredicate = predicate :=
        Option.some.inj (predicateSuccess.symm.trans predicateStrengthens)
      subst predicateEq
      split
      next noRefinedSuccess =>
        exact absurd (refinedIH.symm.trans noRefinedSuccess)
          (by intro contra; cases contra)
      next refinedResult refinedSuccess =>
        have refinedEq : refinedResult =
            StrengtheningResult.fromRename forwardRename typedRenaming
              renameInverse renameInverseLeft renameInverseInjects
              refinedValue :=
          Option.some.inj (refinedSuccess.symm.trans refinedIH)
        subst refinedEq
        rfl

/-- HoTT-special strength-T1 case: `Term.sessionSend`.

Carries 1 outer-scope RawTerm payload (`protocolStep` at `back`) + 2
Term IHs (`channel` at `Ty.session protocolStep` + `payload` at
`payloadType`).  The `payloadType` itself is implicit — reconstructed
from the payload's type. -/
theorem strengthenTyped?_rename_eq_sessionSend
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
    (protocolStep : RawTerm sourceScope)
    {payloadType : Ty level sourceScope}
    {channelRaw payloadRaw : RawTerm sourceScope}
    (channel : Term sourceCtx (Ty.session protocolStep) channelRaw)
    (payload : Term sourceCtx payloadType payloadRaw)
    (channelIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming channel)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            channel))
    (payloadIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming payload)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            payload)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.sessionSend (context := sourceCtx) protocolStep channel
            payload))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.sessionSend (context := sourceCtx) protocolStep channel
            payload)) := by
  dsimp only [Term.rename, partialStrengthenTyped?]
  have protocolStrengthens :
      (protocolStep.rename forwardRename).partialStrengthen? renameInverse
        = some protocolStep := by
    rw [RawTerm.partialStrengthen?_rename_some protocolStep forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity protocolStep]
  split
  next noProtocolSuccess =>
    exact absurd (protocolStrengthens.symm.trans noProtocolSuccess)
      (by intro contra; cases contra)
  next targetProtocolStep protocolSuccess =>
    have protocolEq : targetProtocolStep = protocolStep :=
      Option.some.inj (protocolSuccess.symm.trans protocolStrengthens)
    subst protocolEq
    split
    next noChannelSuccess =>
      exact absurd (channelIH.symm.trans noChannelSuccess)
        (by intro contra; cases contra)
    next channelResult channelSuccess =>
      have channelEq : channelResult =
          StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects channel :=
        Option.some.inj (channelSuccess.symm.trans channelIH)
      subst channelEq
      split
      next noPayloadSuccess =>
        exact absurd (payloadIH.symm.trans noPayloadSuccess)
          (by intro contra; cases contra)
      next payloadResult payloadSuccess =>
        have payloadEq : payloadResult =
            StrengtheningResult.fromRename forwardRename typedRenaming
              renameInverse renameInverseLeft renameInverseInjects payload :=
          Option.some.inj (payloadSuccess.symm.trans payloadIH)
        subst payloadEq
        rfl

end Term

end LeanFX2
