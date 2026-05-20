import LeanFX2.Term.PartialStrengthen.RenameImage.Core

/-! # Term/PartialStrengthen/RenameImage/Cubical

Rename-image T1 equations for cubical transport, composition, glue, and path application cases.
-/

namespace LeanFX2

namespace Term

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

end Term

end LeanFX2
