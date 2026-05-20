import LeanFX2.Term.PartialStrengthen.RenameImage.TypeCodes

/-! # Typed partial strengthening.

This module is the typed-term reconstruction layer above
`RawTerm.partialStrengthen?`, `Ty.partialStrengthen?`, and
`ContextStrengthening`.

The first exported artifact is `Term.StrengtheningResult`: a target
typed term together with the exact type/raw strengthening successes and
the forward renaming equations.  The constructors below cover the
closed atomic terms and the variable case; recursive constructors are
added in later files against the same result type.
-/

namespace LeanFX2

namespace Term

/-- HoTT-special strength-T1 case: `Term.funextReflAtId`.

Carries 2 Ty payloads at the outer scope (domainType, codomainType)
plus 1 RawTerm payload under one binder (applyRaw via `back.lift`).
The codomain RawTerm `applyRaw` uses the same `rho.lift` survival
recipe as `piTyCode`. -/
theorem strengthenTyped?_rename_eq_funextReflAtId
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
    {domainType codomainType : Ty level sourceScope}
    (applyRaw : RawTerm (sourceScope + 1)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.funextReflAtId (context := sourceCtx) domainType codomainType
            applyRaw))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.funextReflAtId (context := sourceCtx) domainType codomainType
            applyRaw)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have domainStrengthens :
      (domainType.rename forwardRename).partialStrengthen? renameInverse
        = some domainType := by
    rw [Ty.partialStrengthen?_rename_some domainType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity domainType]
  have codomainStrengthens :
      (codomainType.rename forwardRename).partialStrengthen? renameInverse
        = some codomainType := by
    rw [Ty.partialStrengthen?_rename_some codomainType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity codomainType]
  have applyStrengthens :
      (applyRaw.rename forwardRename.lift).partialStrengthen?
          renameInverse.lift
        = some applyRaw := by
    rw [RawTerm.partialStrengthen?_rename_some applyRaw
      forwardRename.lift (@RawRenaming.identity sourceScope).lift
      renameInverse.lift
      (PartialRawRenaming.lift_rename_some renameInverseLeft),
      RawTerm.rename_pointwise
        (@RawRenaming.identity_lift_pointwise sourceScope) applyRaw,
      RawTerm.rename_identity applyRaw]
  split
  next noDomainSuccess =>
    exact absurd (domainStrengthens.symm.trans noDomainSuccess)
      (by intro contra; cases contra)
  next targetDomainType domainSuccess =>
    have domainEq : targetDomainType = domainType :=
      Option.some.inj (domainSuccess.symm.trans domainStrengthens)
    subst domainEq
    split
    next noCodomainSuccess =>
      exact absurd (codomainStrengthens.symm.trans noCodomainSuccess)
        (by intro contra; cases contra)
    next targetCodomainType codomainSuccess =>
      have codomainEq : targetCodomainType = codomainType :=
        Option.some.inj (codomainSuccess.symm.trans codomainStrengthens)
      subst codomainEq
      split
      next noApplySuccess =>
        exact absurd (applyStrengthens.symm.trans noApplySuccess)
          (by intro contra; cases contra)
      next targetApplyRaw applySuccess =>
        have applyEq : targetApplyRaw = applyRaw :=
          Option.some.inj (applySuccess.symm.trans applyStrengthens)
        subst applyEq
        rfl

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
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
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
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
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
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
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

/-- HoTT-special strength-T1 case: `Term.equivApp`.

Carries 2 Ty payloads (`carrierA + carrierB` at outer `back`) + 2 Term
IHs (`equivTerm` at `Ty.equiv carrierA carrierB` + `argumentTerm` at
`carrierA`).  Both Ty payloads are implicit on the ctor. -/
theorem strengthenTyped?_rename_eq_equivApp
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
    {carrierA carrierB : Ty level sourceScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    (equivTerm : Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw)
    (argumentTerm : Term sourceCtx carrierA argumentRaw)
    (equivIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming equivTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            equivTerm))
    (argumentIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming argumentTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            argumentTerm)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.equivApp (context := sourceCtx) equivTerm argumentTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.equivApp (context := sourceCtx) equivTerm argumentTerm)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have carrierAStrengthens :
      (carrierA.rename forwardRename).partialStrengthen? renameInverse
        = some carrierA := by
    rw [Ty.partialStrengthen?_rename_some carrierA forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity carrierA]
  have carrierBStrengthens :
      (carrierB.rename forwardRename).partialStrengthen? renameInverse
        = some carrierB := by
    rw [Ty.partialStrengthen?_rename_some carrierB forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity carrierB]
  split
  next noCarrierASuccess =>
    exact absurd (carrierAStrengthens.symm.trans noCarrierASuccess)
      (by intro contra; cases contra)
  next targetCarrierA carrierASuccess =>
    have carrierAEq : targetCarrierA = carrierA :=
      Option.some.inj (carrierASuccess.symm.trans carrierAStrengthens)
    subst carrierAEq
    split
    next noCarrierBSuccess =>
      exact absurd (carrierBStrengthens.symm.trans noCarrierBSuccess)
        (by intro contra; cases contra)
    next targetCarrierB carrierBSuccess =>
      have carrierBEq : targetCarrierB = carrierB :=
        Option.some.inj (carrierBSuccess.symm.trans carrierBStrengthens)
      subst carrierBEq
      split
      next noEquivSuccess =>
        exact absurd (equivIH.symm.trans noEquivSuccess)
          (by intro contra; cases contra)
      next equivResult equivSuccess =>
        have equivEq : equivResult =
            StrengtheningResult.fromRename forwardRename typedRenaming
              renameInverse renameInverseLeft renameInverseInjects
              equivTerm :=
          Option.some.inj (equivSuccess.symm.trans equivIH)
        subst equivEq
        split
        next noArgumentSuccess =>
          exact absurd (argumentIH.symm.trans noArgumentSuccess)
            (by intro contra; cases contra)
        next argumentResult argumentSuccess =>
          have argumentEq : argumentResult =
              StrengtheningResult.fromRename forwardRename typedRenaming
                renameInverse renameInverseLeft renameInverseInjects
                argumentTerm :=
            Option.some.inj (argumentSuccess.symm.trans argumentIH)
          subst argumentEq
          rfl

/-- HoTT-special strength-T1 case: `Term.transp`.

Cubical transp carries 2 Ty payloads (sourceType, targetType) + 2
RawTerm payloads (sourceTypeRaw, targetTypeRaw), all at outer
`back`, plus 2 Term IHs (typePath, sourceValue).  No binder lift, no
`▸` cast. -/
theorem strengthenTyped?_rename_eq_transp
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
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType targetType : Ty level sourceScope)
    (sourceTypeRaw targetTypeRaw : RawTerm sourceScope)
    {pathRaw sourceRaw : RawTerm sourceScope}
    (typePath :
      Term sourceCtx
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw)
        pathRaw)
    (sourceValue : Term sourceCtx sourceType sourceRaw)
    (pathIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming typePath)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            typePath))
    (sourceIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming sourceValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            sourceValue)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.transp (context := sourceCtx) modeIsUnivalent universeLevel
            universeLevelLt sourceType targetType sourceTypeRaw targetTypeRaw
            typePath sourceValue))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.transp (context := sourceCtx) modeIsUnivalent universeLevel
            universeLevelLt sourceType targetType sourceTypeRaw targetTypeRaw
            typePath sourceValue)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have sourceTypeStrengthens :
      (sourceType.rename forwardRename).partialStrengthen? renameInverse
        = some sourceType := by
    rw [Ty.partialStrengthen?_rename_some sourceType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity sourceType]
  have targetTypeStrengthens :
      (targetType.rename forwardRename).partialStrengthen? renameInverse
        = some targetType := by
    rw [Ty.partialStrengthen?_rename_some targetType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity targetType]
  have sourceTypeRawStrengthens :
      (sourceTypeRaw.rename forwardRename).partialStrengthen? renameInverse
        = some sourceTypeRaw := by
    rw [RawTerm.partialStrengthen?_rename_some sourceTypeRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity sourceTypeRaw]
  have targetTypeRawStrengthens :
      (targetTypeRaw.rename forwardRename).partialStrengthen? renameInverse
        = some targetTypeRaw := by
    rw [RawTerm.partialStrengthen?_rename_some targetTypeRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity targetTypeRaw]
  split
  next noSourceTypeSuccess =>
    exact absurd (sourceTypeStrengthens.symm.trans noSourceTypeSuccess)
      (by intro contra; cases contra)
  next targetSourceType sourceTypeSuccess =>
    have sourceTypeEq : targetSourceType = sourceType :=
      Option.some.inj (sourceTypeSuccess.symm.trans sourceTypeStrengthens)
    subst sourceTypeEq
    split
    next noTargetTypeSuccess =>
      exact absurd (targetTypeStrengthens.symm.trans noTargetTypeSuccess)
        (by intro contra; cases contra)
    next targetTargetType targetTypeSuccess =>
      have targetTypeEq : targetTargetType = targetType :=
        Option.some.inj (targetTypeSuccess.symm.trans targetTypeStrengthens)
      subst targetTypeEq
      split
      next noSourceTypeRawSuccess =>
        exact absurd
          (sourceTypeRawStrengthens.symm.trans noSourceTypeRawSuccess)
          (by intro contra; cases contra)
      next targetSourceTypeRaw sourceTypeRawSuccess =>
        have sourceTypeRawEq : targetSourceTypeRaw = sourceTypeRaw :=
          Option.some.inj
            (sourceTypeRawSuccess.symm.trans sourceTypeRawStrengthens)
        subst sourceTypeRawEq
        split
        next noTargetTypeRawSuccess =>
          exact absurd
            (targetTypeRawStrengthens.symm.trans noTargetTypeRawSuccess)
            (by intro contra; cases contra)
        next targetTargetTypeRaw targetTypeRawSuccess =>
          have targetTypeRawEq : targetTargetTypeRaw = targetTypeRaw :=
            Option.some.inj
              (targetTypeRawSuccess.symm.trans targetTypeRawStrengthens)
          subst targetTypeRawEq
          split
          next noPathSuccess =>
            exact absurd (pathIH.symm.trans noPathSuccess)
              (by intro contra; cases contra)
          next pathResult pathSuccess =>
            have pathEq : pathResult =
                StrengtheningResult.fromRename forwardRename typedRenaming
                  renameInverse renameInverseLeft renameInverseInjects
                  typePath :=
              Option.some.inj (pathSuccess.symm.trans pathIH)
            subst pathEq
            split
            next noSourceSuccess =>
              exact absurd (sourceIH.symm.trans noSourceSuccess)
                (by intro contra; cases contra)
            next sourceResult sourceSuccess =>
              have sourceEq : sourceResult =
                  StrengtheningResult.fromRename forwardRename typedRenaming
                    renameInverse renameInverseLeft renameInverseInjects
                    sourceValue :=
                Option.some.inj (sourceSuccess.symm.trans sourceIH)
              subst sourceEq
              rfl

/-- HoTT-special strength-T1 case: `Term.hcompPath`.

Cubical homogeneous path composition: 1 implicit Ty payload
(carrierType at outer `back`) + 2 explicit RawTerm payloads
(leftEndpoint, rightEndpoint at outer `back`) + 2 Term IHs
(sidesPath at `Ty.path carrierType leftEndpoint rightEndpoint` +
capValue at `carrierType`). -/
theorem strengthenTyped?_rename_eq_hcompPath
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
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    (leftEndpoint rightEndpoint : RawTerm sourceScope)
    {sidesPathRaw capRaw : RawTerm sourceScope}
    (sidesPath :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint)
        sidesPathRaw)
    (capValue : Term sourceCtx carrierType capRaw)
    (sidesIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming sidesPath)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            sidesPath))
    (capIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming capValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            capValue)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.hcompPath (context := sourceCtx) modeIsUnivalent
            leftEndpoint rightEndpoint sidesPath capValue))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.hcompPath (context := sourceCtx) modeIsUnivalent
            leftEndpoint rightEndpoint sidesPath capValue)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have carrierStrengthens :
      (carrierType.rename forwardRename).partialStrengthen? renameInverse
        = some carrierType := by
    rw [Ty.partialStrengthen?_rename_some carrierType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity carrierType]
  have leftStrengthens :
      (leftEndpoint.rename forwardRename).partialStrengthen? renameInverse
        = some leftEndpoint := by
    rw [RawTerm.partialStrengthen?_rename_some leftEndpoint forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity leftEndpoint]
  have rightStrengthens :
      (rightEndpoint.rename forwardRename).partialStrengthen? renameInverse
        = some rightEndpoint := by
    rw [RawTerm.partialStrengthen?_rename_some rightEndpoint forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity rightEndpoint]
  split
  next noCarrierSuccess =>
    exact absurd (carrierStrengthens.symm.trans noCarrierSuccess)
      (by intro contra; cases contra)
  next targetCarrierType carrierSuccess =>
    have carrierEq : targetCarrierType = carrierType :=
      Option.some.inj (carrierSuccess.symm.trans carrierStrengthens)
    subst carrierEq
    split
    next noLeftSuccess =>
      exact absurd (leftStrengthens.symm.trans noLeftSuccess)
        (by intro contra; cases contra)
    next targetLeftEndpoint leftSuccess =>
      have leftEq : targetLeftEndpoint = leftEndpoint :=
        Option.some.inj (leftSuccess.symm.trans leftStrengthens)
      subst leftEq
      split
      next noRightSuccess =>
        exact absurd (rightStrengthens.symm.trans noRightSuccess)
          (by intro contra; cases contra)
      next targetRightEndpoint rightSuccess =>
        have rightEq : targetRightEndpoint = rightEndpoint :=
          Option.some.inj (rightSuccess.symm.trans rightStrengthens)
        subst rightEq
        split
        next noSidesSuccess =>
          exact absurd (sidesIH.symm.trans noSidesSuccess)
            (by intro contra; cases contra)
        next sidesResult sidesSuccess =>
          have sidesEq : sidesResult =
              StrengtheningResult.fromRename forwardRename typedRenaming
                renameInverse renameInverseLeft renameInverseInjects
                sidesPath :=
            Option.some.inj (sidesSuccess.symm.trans sidesIH)
          subst sidesEq
          split
          next noCapSuccess =>
            exact absurd (capIH.symm.trans noCapSuccess)
              (by intro contra; cases contra)
          next capResult capSuccess =>
            have capEq : capResult =
                StrengtheningResult.fromRename forwardRename typedRenaming
                  renameInverse renameInverseLeft renameInverseInjects
                  capValue :=
              Option.some.inj (capSuccess.symm.trans capIH)
            subst capEq
            rfl

/-- HoTT-special strength-T1 case: `Term.glueIntro`.

Cubical glue introduction: 1 Ty payload (baseType) + 1 RawTerm
payload (boundaryWitness), both at outer `back`, + 2 Term IHs
(baseValue at `baseType`, partialValue at `baseType`). -/
theorem strengthenTyped?_rename_eq_glueIntro
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
    (modeIsUnivalent : mode = Mode.univalent)
    (baseType : Ty level sourceScope)
    (boundaryWitness : RawTerm sourceScope)
    {baseRaw partialRaw : RawTerm sourceScope}
    (baseValue : Term sourceCtx baseType baseRaw)
    (partialValue : Term sourceCtx baseType partialRaw)
    (baseIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming baseValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            baseValue))
    (partialIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming partialValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            partialValue)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.glueIntro (context := sourceCtx) modeIsUnivalent baseType
            boundaryWitness baseValue partialValue))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.glueIntro (context := sourceCtx) modeIsUnivalent baseType
            boundaryWitness baseValue partialValue)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have baseTypeStrengthens :
      (baseType.rename forwardRename).partialStrengthen? renameInverse
        = some baseType := by
    rw [Ty.partialStrengthen?_rename_some baseType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity baseType]
  have boundaryStrengthens :
      (boundaryWitness.rename forwardRename).partialStrengthen? renameInverse
        = some boundaryWitness := by
    rw [RawTerm.partialStrengthen?_rename_some boundaryWitness forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity boundaryWitness]
  split
  next noBaseTypeSuccess =>
    exact absurd (baseTypeStrengthens.symm.trans noBaseTypeSuccess)
      (by intro contra; cases contra)
  next targetBaseType baseTypeSuccess =>
    have baseTypeEq : targetBaseType = baseType :=
      Option.some.inj (baseTypeSuccess.symm.trans baseTypeStrengthens)
    subst baseTypeEq
    split
    next noBoundarySuccess =>
      exact absurd (boundaryStrengthens.symm.trans noBoundarySuccess)
        (by intro contra; cases contra)
    next targetBoundaryWitness boundarySuccess =>
      have boundaryEq : targetBoundaryWitness = boundaryWitness :=
        Option.some.inj (boundarySuccess.symm.trans boundaryStrengthens)
      subst boundaryEq
      split
      next noBaseValueSuccess =>
        exact absurd (baseIH.symm.trans noBaseValueSuccess)
          (by intro contra; cases contra)
      next baseValueResult baseValueSuccess =>
        have baseValueEq : baseValueResult =
            StrengtheningResult.fromRename forwardRename typedRenaming
              renameInverse renameInverseLeft renameInverseInjects
              baseValue :=
          Option.some.inj (baseValueSuccess.symm.trans baseIH)
        subst baseValueEq
        split
        next noPartialSuccess =>
          exact absurd (partialIH.symm.trans noPartialSuccess)
            (by intro contra; cases contra)
        next partialResult partialSuccess =>
          have partialEq : partialResult =
              StrengtheningResult.fromRename forwardRename typedRenaming
                renameInverse renameInverseLeft renameInverseInjects
                partialValue :=
            Option.some.inj (partialSuccess.symm.trans partialIH)
          subst partialEq
          rfl

/-- HoTT-special strength-T1 case: `Term.pathApp`.

Path application: 1 implicit Ty (carrierType) + 2 implicit RawTerm
(leftEndpoint, rightEndpoint) at outer `back`, + 2 Term IHs
(pathTerm at `Ty.path carrierType leftEndpoint rightEndpoint` +
intervalTerm at `Ty.interval`). -/
theorem strengthenTyped?_rename_eq_pathApp
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
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {pathRaw intervalRaw : RawTerm sourceScope}
    (pathTerm : Term sourceCtx
      (Ty.path carrierType leftEndpoint rightEndpoint) pathRaw)
    (intervalTerm : Term sourceCtx Ty.interval intervalRaw)
    (pathIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming pathTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            pathTerm))
    (intervalIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming intervalTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            intervalTerm)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.pathApp (context := sourceCtx) modeIsUnivalent pathTerm
            intervalTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.pathApp (context := sourceCtx) modeIsUnivalent pathTerm
            intervalTerm)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have carrierStrengthens :
      (carrierType.rename forwardRename).partialStrengthen? renameInverse
        = some carrierType := by
    rw [Ty.partialStrengthen?_rename_some carrierType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity carrierType]
  have leftStrengthens :
      (leftEndpoint.rename forwardRename).partialStrengthen? renameInverse
        = some leftEndpoint := by
    rw [RawTerm.partialStrengthen?_rename_some leftEndpoint forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity leftEndpoint]
  have rightStrengthens :
      (rightEndpoint.rename forwardRename).partialStrengthen? renameInverse
        = some rightEndpoint := by
    rw [RawTerm.partialStrengthen?_rename_some rightEndpoint forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity rightEndpoint]
  split
  next noCarrierSuccess =>
    exact absurd (carrierStrengthens.symm.trans noCarrierSuccess)
      (by intro contra; cases contra)
  next targetCarrierType carrierSuccess =>
    have carrierEq : targetCarrierType = carrierType :=
      Option.some.inj (carrierSuccess.symm.trans carrierStrengthens)
    subst carrierEq
    split
    next noLeftSuccess =>
      exact absurd (leftStrengthens.symm.trans noLeftSuccess)
        (by intro contra; cases contra)
    next targetLeftEndpoint leftSuccess =>
      have leftEq : targetLeftEndpoint = leftEndpoint :=
        Option.some.inj (leftSuccess.symm.trans leftStrengthens)
      subst leftEq
      split
      next noRightSuccess =>
        exact absurd (rightStrengthens.symm.trans noRightSuccess)
          (by intro contra; cases contra)
      next targetRightEndpoint rightSuccess =>
        have rightEq : targetRightEndpoint = rightEndpoint :=
          Option.some.inj (rightSuccess.symm.trans rightStrengthens)
        subst rightEq
        split
        next noPathSuccess =>
          exact absurd (pathIH.symm.trans noPathSuccess)
            (by intro contra; cases contra)
        next pathResult pathSuccess =>
          have pathEq : pathResult =
              StrengtheningResult.fromRename forwardRename typedRenaming
                renameInverse renameInverseLeft renameInverseInjects
                pathTerm :=
            Option.some.inj (pathSuccess.symm.trans pathIH)
          subst pathEq
          split
          next noIntervalSuccess =>
            exact absurd (intervalIH.symm.trans noIntervalSuccess)
              (by intro contra; cases contra)
          next intervalResult intervalSuccess =>
            have intervalEq : intervalResult =
                StrengtheningResult.fromRename forwardRename typedRenaming
                  renameInverse renameInverseLeft renameInverseInjects
                  intervalTerm :=
              Option.some.inj (intervalSuccess.symm.trans intervalIH)
            subst intervalEq
            rfl

/-- HoTT-special strength-T1 case: `Term.codataUnfold`.

Codata constructor: 1 implicit Ty payload (outputType) at outer
`back` + 2 Term IHs (initialState at `stateType` + transition at
`Ty.arrow stateType outputType`).  `stateType` is also implicit but
the dispatcher only strengthens `outputType`. -/
theorem strengthenTyped?_rename_eq_codataUnfold
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
    {stateType outputType : Ty level sourceScope}
    {stateRaw transitionRaw : RawTerm sourceScope}
    (initialState : Term sourceCtx stateType stateRaw)
    (transition : Term sourceCtx (Ty.arrow stateType outputType) transitionRaw)
    (stateIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming initialState)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            initialState))
    (transitionIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming transition)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            transition)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.codataUnfold (context := sourceCtx) initialState transition))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.codataUnfold (context := sourceCtx) initialState
            transition)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have outputStrengthens :
      (outputType.rename forwardRename).partialStrengthen? renameInverse
        = some outputType := by
    rw [Ty.partialStrengthen?_rename_some outputType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity outputType]
  split
  next noOutputSuccess =>
    exact absurd (outputStrengthens.symm.trans noOutputSuccess)
      (by intro contra; cases contra)
  next targetOutputType outputSuccess =>
    have outputEq : targetOutputType = outputType :=
      Option.some.inj (outputSuccess.symm.trans outputStrengthens)
    subst outputEq
    split
    next noStateSuccess =>
      exact absurd (stateIH.symm.trans noStateSuccess)
        (by intro contra; cases contra)
    next stateResult stateSuccess =>
      have stateEq : stateResult =
          StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            initialState :=
        Option.some.inj (stateSuccess.symm.trans stateIH)
      subst stateEq
      split
      next noTransitionSuccess =>
        exact absurd (transitionIH.symm.trans noTransitionSuccess)
          (by intro contra; cases contra)
      next transitionResult transitionSuccess =>
        have transitionEq : transitionResult =
            StrengtheningResult.fromRename forwardRename typedRenaming
              renameInverse renameInverseLeft renameInverseInjects
              transition :=
          Option.some.inj (transitionSuccess.symm.trans transitionIH)
        subst transitionEq
        rfl

/-- Binder-Ty strength-T1 case: `Term.fst`.

Carries 2 Ty payloads (firstType at outer `back`, secondType at
`back.lift` under one binder) + 1 Term IH (pairTerm at
`Ty.sigmaTy firstType secondType`).  The codomain Ty `secondType`
uses the same `rho.lift` survival recipe as `piTyCode` but lifted
to the Ty layer via `Ty.partialStrengthen?_rename_some`. -/
theorem strengthenTyped?_rename_eq_fst
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
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {pairRaw : RawTerm sourceScope}
    (pairTerm : Term sourceCtx (Ty.sigmaTy firstType secondType) pairRaw)
    (pairIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming pairTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            pairTerm)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming (Term.fst pairTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.fst pairTerm)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have firstStrengthens :
      (firstType.rename forwardRename).partialStrengthen? renameInverse
        = some firstType := by
    rw [Ty.partialStrengthen?_rename_some firstType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity firstType]
  have secondStrengthens :
      (secondType.rename forwardRename.lift).partialStrengthen?
          renameInverse.lift
        = some secondType := by
    rw [Ty.partialStrengthen?_rename_some secondType
      forwardRename.lift (@RawRenaming.identity sourceScope).lift
      renameInverse.lift
      (PartialRawRenaming.lift_rename_some renameInverseLeft),
      Ty.rename_pointwise
        (@RawRenaming.identity_lift_pointwise sourceScope) secondType,
      Ty.rename_identity secondType]
  split
  next noFirstSuccess =>
    exact absurd (firstStrengthens.symm.trans noFirstSuccess)
      (by intro contra; cases contra)
  next targetFirstType firstSuccess =>
    have firstEq : targetFirstType = firstType :=
      Option.some.inj (firstSuccess.symm.trans firstStrengthens)
    subst firstEq
    split
    next noSecondSuccess =>
      exact absurd (secondStrengthens.symm.trans noSecondSuccess)
        (by intro contra; cases contra)
    next targetSecondType secondSuccess =>
      have secondEq : targetSecondType = secondType :=
        Option.some.inj (secondSuccess.symm.trans secondStrengthens)
      subst secondEq
      split
      next noPairSuccess =>
        exact absurd (pairIH.symm.trans noPairSuccess)
          (by intro contra; cases contra)
      next pairResult pairSuccess =>
        have pairEq : pairResult =
            StrengtheningResult.fromRename forwardRename typedRenaming
              renameInverse renameInverseLeft renameInverseInjects
              pairTerm :=
          Option.some.inj (pairSuccess.symm.trans pairIH)
        subst pairEq
        rfl

/-- HoTT-special strength-T1 case: `Term.equivApply`.

Carries 2 outer Ty payloads (carrierA + carrierB at `back`) + 2 Term
IHs (equivTerm at `Ty.equiv carrierA carrierB`, argumentTerm at
carrierA).  No cast on rename — result type `carrierB` renames
structurally; same precedent as `equivApp`. -/
theorem strengthenTyped?_rename_eq_equivApply
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
    {carrierA carrierB : Ty level sourceScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    (equivTerm : Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw)
    (argumentTerm : Term sourceCtx carrierA argumentRaw)
    (equivIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming equivTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            equivTerm))
    (argumentIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming argumentTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            argumentTerm)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming (Term.equivApply equivTerm argumentTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.equivApply equivTerm argumentTerm)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have carrierAStrengthens :
      (carrierA.rename forwardRename).partialStrengthen? renameInverse
        = some carrierA := by
    rw [Ty.partialStrengthen?_rename_some carrierA forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity carrierA]
  have carrierBStrengthens :
      (carrierB.rename forwardRename).partialStrengthen? renameInverse
        = some carrierB := by
    rw [Ty.partialStrengthen?_rename_some carrierB forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity carrierB]
  split
  next noCarrierASuccess =>
    exact absurd (carrierAStrengthens.symm.trans noCarrierASuccess)
      (by intro contra; cases contra)
  next targetCarrierA carrierASuccess =>
    have carrierAEq : targetCarrierA = carrierA :=
      Option.some.inj (carrierASuccess.symm.trans carrierAStrengthens)
    subst carrierAEq
    split
    next noCarrierBSuccess =>
      exact absurd (carrierBStrengthens.symm.trans noCarrierBSuccess)
        (by intro contra; cases contra)
    next targetCarrierB carrierBSuccess =>
      have carrierBEq : targetCarrierB = carrierB :=
        Option.some.inj (carrierBSuccess.symm.trans carrierBStrengthens)
      subst carrierBEq
      split
      next noEquivSuccess =>
        exact absurd (equivIH.symm.trans noEquivSuccess)
          (by intro contra; cases contra)
      next equivResult equivSuccess =>
        have equivEq : equivResult =
            StrengtheningResult.fromRename forwardRename typedRenaming
              renameInverse renameInverseLeft renameInverseInjects
              equivTerm :=
          Option.some.inj (equivSuccess.symm.trans equivIH)
        subst equivEq
        split
        next noArgumentSuccess =>
          exact absurd (argumentIH.symm.trans noArgumentSuccess)
            (by intro contra; cases contra)
        next argumentResult argumentSuccess =>
          have argumentEq : argumentResult =
              StrengtheningResult.fromRename forwardRename typedRenaming
                renameInverse renameInverseLeft renameInverseInjects
                argumentTerm :=
            Option.some.inj (argumentSuccess.symm.trans argumentIH)
          subst argumentEq
          rfl

/-- HoTT-special strength-T1 case: `Term.uaToEquiv`.

Carries `innerLevel` + `innerLevelLt` value-shape + 2 Ty payloads
(leftTy, rightTy at outer `back`) + 2 RawTerm payloads
(leftTyRaw, rightTyRaw at outer `back`) + 1 Term IH (proof at
`Ty.id (Ty.universe innerLevel innerLevelLt) leftTyRaw rightTyRaw`).
No cast on rename — result `Ty.equiv leftTy rightTy` renames
structurally. -/
theorem strengthenTyped?_rename_eq_uaToEquiv
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
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (leftTy rightTy : Ty level sourceScope)
    (leftTyRaw rightTyRaw : RawTerm sourceScope)
    {proofRaw : RawTerm sourceScope}
    (proof : Term sourceCtx
      (Ty.id (Ty.universe innerLevel innerLevelLt) leftTyRaw rightTyRaw)
      proofRaw)
    (proofIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming proof)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            proof)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.uaToEquiv (context := sourceCtx) innerLevel innerLevelLt
            leftTy rightTy leftTyRaw rightTyRaw proof))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.uaToEquiv (context := sourceCtx) innerLevel innerLevelLt
            leftTy rightTy leftTyRaw rightTyRaw proof)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have leftTyStrengthens :
      (leftTy.rename forwardRename).partialStrengthen? renameInverse
        = some leftTy := by
    rw [Ty.partialStrengthen?_rename_some leftTy forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity leftTy]
  have rightTyStrengthens :
      (rightTy.rename forwardRename).partialStrengthen? renameInverse
        = some rightTy := by
    rw [Ty.partialStrengthen?_rename_some rightTy forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity rightTy]
  have leftRawStrengthens :
      (leftTyRaw.rename forwardRename).partialStrengthen? renameInverse
        = some leftTyRaw := by
    rw [RawTerm.partialStrengthen?_rename_some leftTyRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity leftTyRaw]
  have rightRawStrengthens :
      (rightTyRaw.rename forwardRename).partialStrengthen? renameInverse
        = some rightTyRaw := by
    rw [RawTerm.partialStrengthen?_rename_some rightTyRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity rightTyRaw]
  split
  next noLeftTySuccess =>
    exact absurd (leftTyStrengthens.symm.trans noLeftTySuccess)
      (by intro contra; cases contra)
  next targetLeftTy leftTySuccess =>
    have leftTyEq : targetLeftTy = leftTy :=
      Option.some.inj (leftTySuccess.symm.trans leftTyStrengthens)
    subst leftTyEq
    split
    next noRightTySuccess =>
      exact absurd (rightTyStrengthens.symm.trans noRightTySuccess)
        (by intro contra; cases contra)
    next targetRightTy rightTySuccess =>
      have rightTyEq : targetRightTy = rightTy :=
        Option.some.inj (rightTySuccess.symm.trans rightTyStrengthens)
      subst rightTyEq
      split
      next noLeftRawSuccess =>
        exact absurd (leftRawStrengthens.symm.trans noLeftRawSuccess)
          (by intro contra; cases contra)
      next targetLeftTyRaw leftRawSuccess =>
        have leftRawEq : targetLeftTyRaw = leftTyRaw :=
          Option.some.inj (leftRawSuccess.symm.trans leftRawStrengthens)
        subst leftRawEq
        split
        next noRightRawSuccess =>
          exact absurd (rightRawStrengthens.symm.trans noRightRawSuccess)
            (by intro contra; cases contra)
        next targetRightTyRaw rightRawSuccess =>
          have rightRawEq : targetRightTyRaw = rightTyRaw :=
            Option.some.inj (rightRawSuccess.symm.trans rightRawStrengthens)
          subst rightRawEq
          split
          next noProofSuccess =>
            exact absurd (proofIH.symm.trans noProofSuccess)
              (by intro contra; cases contra)
          next proofResult proofSuccess =>
            have proofEq : proofResult =
                StrengtheningResult.fromRename forwardRename typedRenaming
                  renameInverse renameInverseLeft renameInverseInjects
                  proof :=
              Option.some.inj (proofSuccess.symm.trans proofIH)
            subst proofEq
            rfl

/-- HoTT-special strength-T1 case: `Term.uaIntroHet`.

Carries `innerLevel` + `innerLevelLt` value-shape + 4 RawTerm
payloads (carrierARaw, carrierBRaw, forwardRaw, backwardRaw at outer
`back`) + 2 implicit Ty payloads (carrierA, carrierB at outer
`back`) + 1 Term IH (equivWitness at `Ty.equiv carrierA carrierB`).
No cast on rename — result `Ty.id (Ty.universe ...)` renames
structurally. -/
theorem strengthenTyped?_rename_eq_uaIntroHet
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
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    {carrierA carrierB : Ty level sourceScope}
    (carrierARaw carrierBRaw : RawTerm sourceScope)
    {forwardRaw backwardRaw : RawTerm sourceScope}
    (equivWitness : Term sourceCtx (Ty.equiv carrierA carrierB)
                       (RawTerm.equivIntro forwardRaw backwardRaw))
    (equivIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming equivWitness)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            equivWitness)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.uaIntroHet (context := sourceCtx) innerLevel innerLevelLt
            carrierARaw carrierBRaw equivWitness))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.uaIntroHet (context := sourceCtx) innerLevel innerLevelLt
            carrierARaw carrierBRaw equivWitness)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have carrierAStrengthens :
      (carrierA.rename forwardRename).partialStrengthen? renameInverse
        = some carrierA := by
    rw [Ty.partialStrengthen?_rename_some carrierA forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity carrierA]
  have carrierBStrengthens :
      (carrierB.rename forwardRename).partialStrengthen? renameInverse
        = some carrierB := by
    rw [Ty.partialStrengthen?_rename_some carrierB forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity carrierB]
  have carrierARawStrengthens :
      (carrierARaw.rename forwardRename).partialStrengthen? renameInverse
        = some carrierARaw := by
    rw [RawTerm.partialStrengthen?_rename_some carrierARaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity carrierARaw]
  have carrierBRawStrengthens :
      (carrierBRaw.rename forwardRename).partialStrengthen? renameInverse
        = some carrierBRaw := by
    rw [RawTerm.partialStrengthen?_rename_some carrierBRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity carrierBRaw]
  have forwardStrengthens :
      (forwardRaw.rename forwardRename).partialStrengthen? renameInverse
        = some forwardRaw := by
    rw [RawTerm.partialStrengthen?_rename_some forwardRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity forwardRaw]
  have backwardStrengthens :
      (backwardRaw.rename forwardRename).partialStrengthen? renameInverse
        = some backwardRaw := by
    rw [RawTerm.partialStrengthen?_rename_some backwardRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity backwardRaw]
  split
  next noCarrierASuccess =>
    exact absurd (carrierAStrengthens.symm.trans noCarrierASuccess)
      (by intro contra; cases contra)
  next targetCarrierA carrierASuccess =>
    have carrierAEq : targetCarrierA = carrierA :=
      Option.some.inj (carrierASuccess.symm.trans carrierAStrengthens)
    subst carrierAEq
    split
    next noCarrierBSuccess =>
      exact absurd (carrierBStrengthens.symm.trans noCarrierBSuccess)
        (by intro contra; cases contra)
    next targetCarrierB carrierBSuccess =>
      have carrierBEq : targetCarrierB = carrierB :=
        Option.some.inj (carrierBSuccess.symm.trans carrierBStrengthens)
      subst carrierBEq
      split
      next noCarrierARawSuccess =>
        exact absurd (carrierARawStrengthens.symm.trans noCarrierARawSuccess)
          (by intro contra; cases contra)
      next targetCarrierARaw carrierARawSuccess =>
        have carrierARawEq : targetCarrierARaw = carrierARaw :=
          Option.some.inj
            (carrierARawSuccess.symm.trans carrierARawStrengthens)
        subst carrierARawEq
        split
        next noCarrierBRawSuccess =>
          exact absurd
            (carrierBRawStrengthens.symm.trans noCarrierBRawSuccess)
            (by intro contra; cases contra)
        next targetCarrierBRaw carrierBRawSuccess =>
          have carrierBRawEq : targetCarrierBRaw = carrierBRaw :=
            Option.some.inj
              (carrierBRawSuccess.symm.trans carrierBRawStrengthens)
          subst carrierBRawEq
          split
          next noForwardSuccess =>
            exact absurd (forwardStrengthens.symm.trans noForwardSuccess)
              (by intro contra; cases contra)
          next targetForwardRaw forwardSuccess =>
            have forwardEq : targetForwardRaw = forwardRaw :=
              Option.some.inj (forwardSuccess.symm.trans forwardStrengthens)
            subst forwardEq
            split
            next noBackwardSuccess =>
              exact absurd
                (backwardStrengthens.symm.trans noBackwardSuccess)
                (by intro contra; cases contra)
            next targetBackwardRaw backwardSuccess =>
              have backwardEq : targetBackwardRaw = backwardRaw :=
                Option.some.inj
                  (backwardSuccess.symm.trans backwardStrengthens)
              subst backwardEq
              split
              next noEquivSuccess =>
                exact absurd (equivIH.symm.trans noEquivSuccess)
                  (by intro contra; cases contra)
              next equivResult equivSuccess =>
                have equivEq : equivResult =
                    StrengtheningResult.fromRename forwardRename
                      typedRenaming renameInverse renameInverseLeft
                      renameInverseInjects equivWitness :=
                  Option.some.inj (equivSuccess.symm.trans equivIH)
                subst equivEq
                rfl

/-- HoTT-special strength-T1 case: `Term.funextIntroHet`.

VALUE-shaped ctor (no Term IH).  Carries 2 outer Ty payloads
(domainType, codomainType at `back`) + 2 binder-shape RawTerm
payloads (applyARaw, applyBRaw under one binder via `back.lift`).
No cast on rename — the Ty.id wrapping Ty.arrow renames structurally
since no binder shift. -/
theorem strengthenTyped?_rename_eq_funextIntroHet
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
    (domainType codomainType : Ty level sourceScope)
    (applyARaw applyBRaw : RawTerm (sourceScope + 1)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.funextIntroHet (context := sourceCtx) domainType codomainType
            applyARaw applyBRaw))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.funextIntroHet (context := sourceCtx) domainType codomainType
            applyARaw applyBRaw)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have domainStrengthens :
      (domainType.rename forwardRename).partialStrengthen? renameInverse
        = some domainType := by
    rw [Ty.partialStrengthen?_rename_some domainType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity domainType]
  have codomainStrengthens :
      (codomainType.rename forwardRename).partialStrengthen? renameInverse
        = some codomainType := by
    rw [Ty.partialStrengthen?_rename_some codomainType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity codomainType]
  have applyAStrengthens :
      (applyARaw.rename forwardRename.lift).partialStrengthen?
          renameInverse.lift
        = some applyARaw := by
    rw [RawTerm.partialStrengthen?_rename_some applyARaw
      forwardRename.lift (@RawRenaming.identity sourceScope).lift
      renameInverse.lift
      (PartialRawRenaming.lift_rename_some renameInverseLeft),
      RawTerm.rename_pointwise
        (@RawRenaming.identity_lift_pointwise sourceScope) applyARaw,
      RawTerm.rename_identity applyARaw]
  have applyBStrengthens :
      (applyBRaw.rename forwardRename.lift).partialStrengthen?
          renameInverse.lift
        = some applyBRaw := by
    rw [RawTerm.partialStrengthen?_rename_some applyBRaw
      forwardRename.lift (@RawRenaming.identity sourceScope).lift
      renameInverse.lift
      (PartialRawRenaming.lift_rename_some renameInverseLeft),
      RawTerm.rename_pointwise
        (@RawRenaming.identity_lift_pointwise sourceScope) applyBRaw,
      RawTerm.rename_identity applyBRaw]
  split
  next noDomainSuccess =>
    exact absurd (domainStrengthens.symm.trans noDomainSuccess)
      (by intro contra; cases contra)
  next targetDomainType domainSuccess =>
    have domainEq : targetDomainType = domainType :=
      Option.some.inj (domainSuccess.symm.trans domainStrengthens)
    subst domainEq
    split
    next noCodomainSuccess =>
      exact absurd (codomainStrengthens.symm.trans noCodomainSuccess)
        (by intro contra; cases contra)
    next targetCodomainType codomainSuccess =>
      have codomainEq : targetCodomainType = codomainType :=
        Option.some.inj (codomainSuccess.symm.trans codomainStrengthens)
      subst codomainEq
      split
      next noApplyASuccess =>
        exact absurd (applyAStrengthens.symm.trans noApplyASuccess)
          (by intro contra; cases contra)
      next targetApplyARaw applyASuccess =>
        have applyAEq : targetApplyARaw = applyARaw :=
          Option.some.inj (applyASuccess.symm.trans applyAStrengthens)
        subst applyAEq
        split
        next noApplyBSuccess =>
          exact absurd (applyBStrengthens.symm.trans noApplyBSuccess)
            (by intro contra; cases contra)
        next targetApplyBRaw applyBSuccess =>
          have applyBEq : targetApplyBRaw = applyBRaw :=
            Option.some.inj (applyBSuccess.symm.trans applyBStrengthens)
          subst applyBEq
          rfl

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

/-- Cast-wrapped strength-T1 case (HEq form): `Term.var`.

The variable rename arm casts the target variable across the
`TermRenaming` evidence for this position.  The dispatcher itself is
cast-invariant at HEq, so the cast-wrapped renamed variable and the
uncast target variable have HEq-related strengthening results.
-/
theorem strengthenTyped?_rename_heq_var
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
    (sourcePosition : Fin sourceScope) :
    HEq
      (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.var (context := sourceCtx) sourcePosition))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects))
      (partialStrengthenTyped?
        (Term.var (context := targetCtx) (forwardRename sourcePosition))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)) := by
  dsimp only [Term.rename]
  exact
    partialStrengthenTyped?_castInvariantHEq
      (Term.var (context := targetCtx) (forwardRename sourcePosition))
      (typedRenaming sourcePosition)
      (ContextStrengthening.ofRenaming forwardRename typedRenaming
        renameInverse renameInverseLeft renameInverseInjects)

/-- Cast-wrapped strength-T1 case (HEq form): `Term.appPi`.

The dependent application rename arm wraps the whole result in the
non-rfl `Ty.subst0_rename_commute ...` cast.  The HEq statement peels
that top-level cast and compares against the uncast renamed
application. -/
theorem strengthenTyped?_rename_heq_appPi
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
    {domainType : Ty level sourceScope}
    {codomainType : Ty level (sourceScope + 1)}
    {functionRaw argumentRaw : RawTerm sourceScope}
    (functionTerm : Term sourceCtx (Ty.piTy domainType codomainType)
      functionRaw)
    (argumentTerm : Term sourceCtx domainType argumentRaw) :
    HEq
      (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.appPi functionTerm argumentTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects))
      (partialStrengthenTyped?
        (Term.appPi
          (Term.rename typedRenaming functionTerm)
          (Term.rename typedRenaming argumentTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)) := by
  dsimp only [Term.rename]
  exact
    partialStrengthenTyped?_castInvariantHEq
      (Term.appPi
        (Term.rename typedRenaming functionTerm)
        (Term.rename typedRenaming argumentTerm))
      (Ty.subst0_rename_commute codomainType domainType argumentRaw
        forwardRename).symm
      (ContextStrengthening.ofRenaming forwardRename typedRenaming
        renameInverse renameInverseLeft renameInverseInjects)

/-- Cast-wrapped strength-T1 case (HEq form): `Term.snd`.

The second projection rename arm wraps the whole result in the non-rfl
`Ty.subst0_rename_commute` cast for the projected second component
type.  The HEq form exposes that the cast-wrapped dispatcher result is
the same computation as the uncast renamed `snd`.
-/
theorem strengthenTyped?_rename_heq_snd
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
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {pairRaw : RawTerm sourceScope}
    (pairTerm : Term sourceCtx (Ty.sigmaTy firstType secondType) pairRaw) :
    HEq
      (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.snd pairTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects))
      (partialStrengthenTyped?
        (Term.snd (Term.rename typedRenaming pairTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)) := by
  dsimp only [Term.rename]
  exact
    partialStrengthenTyped?_castInvariantHEq
      (Term.snd (Term.rename typedRenaming pairTerm))
      (Ty.subst0_rename_commute secondType firstType
        (RawTerm.fst pairRaw) forwardRename).symm
      (ContextStrengthening.ofRenaming forwardRename typedRenaming
        renameInverse renameInverseLeft renameInverseInjects)

/-- Cast-wrapped strength-T1 case (HEq form): `Term.pair`.

The pair rename arm does not wrap the outer pair in a cast; instead the
second component is cast across `Ty.subst0_rename_commute` so its
dependent Σ component type matches the first component's renamed raw.
The HEq form records the dispatcher computation on that exact renamed
pair shape. -/
theorem strengthenTyped?_rename_heq_pair
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
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {firstRaw secondRaw : RawTerm sourceScope}
    (firstValue : Term sourceCtx firstType firstRaw)
    (secondValue :
      Term sourceCtx (secondType.subst0 firstType firstRaw) secondRaw) :
    HEq
      (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.pair firstValue secondValue))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects))
      (partialStrengthenTyped?
        (Term.pair
          (Term.rename typedRenaming firstValue)
          (Ty.subst0_rename_commute secondType firstType firstRaw
            forwardRename ▸
            Term.rename typedRenaming secondValue))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)) := by
  dsimp only [Term.rename]
  exact HEq.rfl

/-- Cast-wrapped strength-T1 case (HEq form): `Term.lam`.

The lambda rename arm casts the renamed body across
`Ty.weaken_rename_commute` before rebuilding the lambda.  The HEq form
records the dispatcher result for that exact renamed lambda shape. -/
theorem strengthenTyped?_rename_heq_lam
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
    {domainType codomainType : Ty level sourceScope}
    {bodyRaw : RawTerm (sourceScope + 1)}
    (body :
      Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw) :
    HEq
      (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.lam body))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects))
      (partialStrengthenTyped?
        (Term.lam
          (Ty.weaken_rename_commute forwardRename codomainType ▸
            Term.rename (typedRenaming.lift domainType) body))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)) := by
  dsimp only [Term.rename]
  exact HEq.rfl

/-- Cast-wrapped strength-T1 case (HEq form): `Term.lamPi`.

Dependent lambda rename is structurally direct once the renaming is lifted
under the domain binder.  The HEq form keeps it in the same cast-wall
family as the other binder constructors so T1 can account for every
renamed binder uniformly. -/
theorem strengthenTyped?_rename_heq_lamPi
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
    {domainType : Ty level sourceScope}
    {codomainType : Ty level (sourceScope + 1)}
    {bodyRaw : RawTerm (sourceScope + 1)}
    (body : Term (sourceCtx.cons domainType) codomainType bodyRaw) :
    HEq
      (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.lamPi body))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects))
      (partialStrengthenTyped?
        (Term.lamPi
          (Term.rename (typedRenaming.lift domainType) body))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)) := by
  dsimp only [Term.rename]
  exact HEq.rfl

/-- Cast-wrapped strength-T1 case (HEq form): `Term.pathLam`.

Path lambda rename mirrors ordinary lambda rename: the lifted body is
transported across `Ty.weaken_rename_commute` for the path carrier. -/
theorem strengthenTyped?_rename_heq_pathLam
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
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    (leftEndpoint rightEndpoint : RawTerm sourceScope)
    {bodyRaw : RawTerm (sourceScope + 1)}
    (body :
      Term (sourceCtx.cons Ty.interval) carrierType.weaken bodyRaw) :
    HEq
      (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.pathLam modeIsUnivalent carrierType leftEndpoint
            rightEndpoint body))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects))
      (partialStrengthenTyped?
        (Term.pathLam modeIsUnivalent (carrierType.rename forwardRename)
          (leftEndpoint.rename forwardRename)
          (rightEndpoint.rename forwardRename)
          (Ty.weaken_rename_commute forwardRename carrierType ▸
            Term.rename (typedRenaming.lift Ty.interval) body))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)) := by
  dsimp only [Term.rename]
  exact HEq.rfl

/-- Cast-wrapped strength-T1 case (HEq form): `Term.oeqFunext`.

The observational funext rename arm casts the pointwise proof through
`oeqFunextPointwiseType_rename` before rebuilding the constructor. -/
theorem strengthenTyped?_rename_heq_oeqFunext
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
    (domainType codomainType : Ty level sourceScope)
    (leftFunctionRaw rightFunctionRaw : RawTerm sourceScope)
    {pointwiseRaw : RawTerm sourceScope}
    (pointwiseProof :
      Term sourceCtx
        (oeqFunextPointwiseType domainType codomainType
          leftFunctionRaw rightFunctionRaw)
        pointwiseRaw) :
    HEq
      (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.oeqFunext domainType codomainType
            leftFunctionRaw rightFunctionRaw pointwiseProof))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects))
      (partialStrengthenTyped?
        (Term.oeqFunext
          (domainType.rename forwardRename)
          (codomainType.rename forwardRename)
          (leftFunctionRaw.rename forwardRename)
          (rightFunctionRaw.rename forwardRename)
          (oeqFunextPointwiseType_rename forwardRename domainType
            codomainType leftFunctionRaw rightFunctionRaw ▸
            Term.rename typedRenaming pointwiseProof))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)) := by
  dsimp only [Term.rename]
  exact HEq.rfl

/-- Cast-wrapped strength-T1 case (HEq form): `Term.equivIntroHet`.

The heterogeneous equivalence introduction rename arm structurally
renames the forward and backward maps, and casts both inverse proofs
through their dedicated inverse-type rename lemmas. -/
theorem strengthenTyped?_rename_heq_equivIntroHet
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
    {carrierA carrierB : Ty level sourceScope}
    {forwardRaw backwardRaw leftInvRaw rightInvRaw : RawTerm sourceScope}
    (forward :
      Term sourceCtx (Ty.arrow carrierA carrierB) forwardRaw)
    (backward :
      Term sourceCtx (Ty.arrow carrierB carrierA) backwardRaw)
    (leftInv :
      Term sourceCtx
        (equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw)
        leftInvRaw)
    (rightInv :
      Term sourceCtx
        (equivIntroHetRightInverseType carrierB forwardRaw backwardRaw)
        rightInvRaw) :
    HEq
      (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.equivIntroHet forward backward leftInv rightInv))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects))
      (partialStrengthenTyped?
        (Term.equivIntroHet
          (Term.rename typedRenaming forward)
          (Term.rename typedRenaming backward)
          (equivIntroHetLeftInverseType_rename forwardRename carrierA
            forwardRaw backwardRaw ▸
            Term.rename typedRenaming leftInv)
          (equivIntroHetRightInverseType_rename forwardRename carrierB
            forwardRaw backwardRaw ▸
            Term.rename typedRenaming rightInv))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)) := by
  dsimp only [Term.rename]
  exact HEq.rfl

/-- Cast-wrapped strength-T1 case (HEq form): `Term.boolElim`.

The Boolean eliminator rename arm has a top-level non-rfl
`Ty.subst0_rename_commute` cast for the motive instantiated at the
scrutinee.  The branch casts remain inside the uncast eliminator; this
lemma only removes the outer cast wrapper so later per-branch soundness
can be handled at the subterm level.
-/
theorem strengthenTyped?_rename_heq_boolElim
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
    {motiveType : Ty level (sourceScope + 1)}
    {scrutineeRaw thenRaw elseRaw : RawTerm sourceScope}
    (scrutinee : Term sourceCtx Ty.bool scrutineeRaw)
    (thenBranch :
      Term sourceCtx (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw)
    (elseBranch :
      Term sourceCtx (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw) :
    HEq
      (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.boolElim scrutinee thenBranch elseBranch))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects))
      (partialStrengthenTyped?
        (Term.boolElim
          (motiveType := motiveType.rename forwardRename.lift)
          (Term.rename typedRenaming scrutinee)
          (Ty.subst0_rename_commute motiveType Ty.bool
            RawTerm.boolTrue forwardRename ▸
            Term.rename typedRenaming thenBranch)
          (Ty.subst0_rename_commute motiveType Ty.bool
            RawTerm.boolFalse forwardRename ▸
            Term.rename typedRenaming elseBranch))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)) := by
  dsimp only [Term.rename]
  exact
    partialStrengthenTyped?_castInvariantHEq
      (Term.boolElim
        (motiveType := motiveType.rename forwardRename.lift)
        (Term.rename typedRenaming scrutinee)
        (Ty.subst0_rename_commute motiveType Ty.bool
          RawTerm.boolTrue forwardRename ▸
          Term.rename typedRenaming thenBranch)
        (Ty.subst0_rename_commute motiveType Ty.bool
          RawTerm.boolFalse forwardRename ▸
          Term.rename typedRenaming elseBranch))
      (Ty.subst0_rename_commute motiveType Ty.bool scrutineeRaw
        forwardRename).symm
      (ContextStrengthening.ofRenaming forwardRename typedRenaming
        renameInverse renameInverseLeft renameInverseInjects)

/-- Cast-wrapped strength-T1 case (HEq form): `Term.funextRefl`.

Closed value-shape ctor (no Term subterms).  Three Ty/raw payloads:
`domainType`, `codomainType`, `applyRaw` at `scope+1`.  Rename arm
wraps the result in `(funextReflType_rename rho ...).symm ▸ Term.funextRefl
(renamed args)`.

The HEq form abstracts over the cast: the dispatcher on the cast-
wrapped input is HEq to the dispatcher on the un-cast `Term.funextRefl`
applied to the renamed payloads.  Proof: cast-invariance of the
dispatcher (`partialStrengthenTyped?_castInvariantHEq`) gives the HEq;
the un-cast dispatcher equation closes via the standard `split` chain.
-/
theorem strengthenTyped?_rename_heq_funextRefl
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
    {domainType codomainType : Ty level sourceScope}
    (applyRaw : RawTerm (sourceScope + 1)) :
    HEq
      (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.funextRefl (context := sourceCtx) domainType codomainType
            applyRaw))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects))
      (partialStrengthenTyped?
        (Term.funextRefl (context := targetCtx)
          (domainType.rename forwardRename)
          (codomainType.rename forwardRename)
          (applyRaw.rename forwardRename.lift))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)) := by
  dsimp only [Term.rename]
  -- After dsimp, LHS becomes:
  --   partialStrengthenTyped?
  --     ((funextReflType_rename ...).symm ▸ Term.funextRefl (renamed args))
  --     σ
  -- Apply cast-invariance HEq to peel the cast wrapper.
  exact
    partialStrengthenTyped?_castInvariantHEq
      (Term.funextRefl (context := targetCtx)
        (domainType.rename forwardRename)
        (codomainType.rename forwardRename)
        (applyRaw.rename forwardRename.lift))
      (funextReflType_rename forwardRename domainType codomainType applyRaw).symm
      (ContextStrengthening.ofRenaming forwardRename typedRenaming
        renameInverse renameInverseLeft renameInverseInjects)

end Term

end LeanFX2
