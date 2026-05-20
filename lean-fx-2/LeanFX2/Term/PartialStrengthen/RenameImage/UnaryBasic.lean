import LeanFX2.Term.PartialStrengthen.RenameImage.Atomic

/-! # Term/PartialStrengthen/RenameImage/UnaryBasic

Rename-image T1 equations for basic one-subterm non-binder cases.
-/

namespace LeanFX2

namespace Term

/-- 1-IH non-binder strength-T1 case: `Term.natSucc`.

The dispatcher recurses on the predecessor through `partialStrengthenTyped?`
and combines the inner success with `partialStrengthenTypedNatSucc`.  The
inductive hypothesis supplies the predecessor's renaming-image equation;
the post-IH proof rewrites the inner match and then closes by `rfl`. -/
theorem strengthenTyped?_rename_eq_natSucc
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
    {predecessorRaw : RawTerm sourceScope}
    (predecessor : Term sourceCtx Ty.nat predecessorRaw)
    (predecessorIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming predecessor)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            predecessor)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming (Term.natSucc predecessor))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.natSucc predecessor)) := by
  dsimp only [Term.rename, partialStrengthenTyped?]
  split
  next noPredecessorSuccess =>
    exact absurd (predecessorIH.symm.trans noPredecessorSuccess)
      (by intro contra; cases contra)
  next predecessorResult predecessorSuccess =>
    have resultEq : predecessorResult =
        StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects predecessor :=
      Option.some.inj (predecessorSuccess.symm.trans predecessorIH)
    subst resultEq
    rfl

/-- 1-IH non-binder strength-T1 case: `Term.intervalOpp`.

Same shape as `natSucc`: dispatcher recurses on the inner interval value
and combines through `partialStrengthenTypedIntervalOpp`.  The Ty payload
is the closed type `Ty.interval`, so no Ty-witness is needed. -/
theorem strengthenTyped?_rename_eq_intervalOpp
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
    {innerRaw : RawTerm sourceScope}
    (innerValue : Term sourceCtx Ty.interval innerRaw)
    (innerIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming innerValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            innerValue)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming (Term.intervalOpp innerValue))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.intervalOpp innerValue)) := by
  dsimp only [Term.rename, partialStrengthenTyped?]
  split
  next noInnerSuccess =>
    exact absurd (innerIH.symm.trans noInnerSuccess)
      (by intro contra; cases contra)
  next innerResult innerSuccess =>
    have resultEq : innerResult =
        StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects innerValue :=
      Option.some.inj (innerSuccess.symm.trans innerIH)
    subst resultEq
    rfl

/-- 1-IH non-binder strength-T1 case: `Term.modIntro`.

Modal introduction wraps a single inner Term IH; no Ty payload (innerType
is inferred from the inner term's typing).  The dispatcher arm recurses
on the inner term and combines through `partialStrengthenTypedModIntro`. -/
theorem strengthenTyped?_rename_eq_modIntro
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
    {innerType : Ty level sourceScope}
    {innerRaw : RawTerm sourceScope}
    (innerTerm : Term sourceCtx innerType innerRaw)
    (innerIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming innerTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            innerTerm)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming (Term.modIntro innerTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.modIntro innerTerm)) := by
  dsimp only [Term.rename, partialStrengthenTyped?]
  split
  next noInnerSuccess =>
    exact absurd (innerIH.symm.trans noInnerSuccess)
      (by intro contra; cases contra)
  next innerResult innerSuccess =>
    have resultEq : innerResult =
        StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects innerTerm :=
      Option.some.inj (innerSuccess.symm.trans innerIH)
    subst resultEq
    rfl

/-- 1-IH non-binder strength-T1 case: `Term.modElim`. -/
theorem strengthenTyped?_rename_eq_modElim
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
    {innerType : Ty level sourceScope}
    {innerRaw : RawTerm sourceScope}
    (innerTerm : Term sourceCtx innerType innerRaw)
    (innerIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming innerTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            innerTerm)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming (Term.modElim innerTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.modElim innerTerm)) := by
  dsimp only [Term.rename, partialStrengthenTyped?]
  split
  next noInnerSuccess =>
    exact absurd (innerIH.symm.trans noInnerSuccess)
      (by intro contra; cases contra)
  next innerResult innerSuccess =>
    have resultEq : innerResult =
        StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects innerTerm :=
      Option.some.inj (innerSuccess.symm.trans innerIH)
    subst resultEq
    rfl

/-- 1-IH non-binder strength-T1 case: `Term.subsume`. -/
theorem strengthenTyped?_rename_eq_subsume
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
    {innerType : Ty level sourceScope}
    {innerRaw : RawTerm sourceScope}
    (innerTerm : Term sourceCtx innerType innerRaw)
    (innerIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming innerTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            innerTerm)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming (Term.subsume innerTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.subsume innerTerm)) := by
  dsimp only [Term.rename, partialStrengthenTyped?]
  split
  next noInnerSuccess =>
    exact absurd (innerIH.symm.trans noInnerSuccess)
      (by intro contra; cases contra)
  next innerResult innerSuccess =>
    have resultEq : innerResult =
        StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects innerTerm :=
      Option.some.inj (innerSuccess.symm.trans innerIH)
    subst resultEq
    rfl

/-- 1-IH non-binder strength-T1 case: `Term.optionSome`.

Wraps a single Term IH; the elementType is implicit (carried through the
inner term's typing).  Dispatcher recurses on the value and combines
through `partialStrengthenTypedOptionSome`. -/
theorem strengthenTyped?_rename_eq_optionSome
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
    {elementType : Ty level sourceScope}
    {valueRaw : RawTerm sourceScope}
    (valueTerm : Term sourceCtx elementType valueRaw)
    (valueIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming valueTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            valueTerm)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming (Term.optionSome valueTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.optionSome valueTerm)) := by
  dsimp only [Term.rename, partialStrengthenTyped?]
  split
  next noValueSuccess =>
    exact absurd (valueIH.symm.trans noValueSuccess)
      (by intro contra; cases contra)
  next valueResult valueSuccess =>
    have resultEq : valueResult =
        StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects valueTerm :=
      Option.some.inj (valueSuccess.symm.trans valueIH)
    subst resultEq
    rfl

/-- 1-IH non-binder strength-T1 case: `Term.eitherInl`.

Carries an inner Term IH plus an unused right-type Ty payload.  The
dispatcher first matches the right-type's renaming-image (via
subst-via-witness) then recurses on the value Term. -/
theorem strengthenTyped?_rename_eq_eitherInl
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
    {leftType rightType : Ty level sourceScope}
    {valueRaw : RawTerm sourceScope}
    (valueTerm : Term sourceCtx leftType valueRaw)
    (valueIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming valueTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            valueTerm)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.eitherInl (rightType := rightType) valueTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.eitherInl (rightType := rightType) valueTerm)) := by
  dsimp only [Term.rename, partialStrengthenTyped?]
  have rightTypeStrengthens :
      (rightType.rename forwardRename).partialStrengthen? renameInverse
        = some rightType := by
    rw [Ty.partialStrengthen?_rename_some rightType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity rightType]
  split
  next noRightSuccess =>
    exact absurd (rightTypeStrengthens.symm.trans noRightSuccess)
      (by intro contra; cases contra)
  next targetRightType rightSuccess =>
    have rightEq : targetRightType = rightType :=
      Option.some.inj (rightSuccess.symm.trans rightTypeStrengthens)
    subst rightEq
    split
    next noValueSuccess =>
      exact absurd (valueIH.symm.trans noValueSuccess)
        (by intro contra; cases contra)
    next valueResult valueSuccess =>
      have resultEq : valueResult =
          StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects valueTerm :=
        Option.some.inj (valueSuccess.symm.trans valueIH)
      subst resultEq
      rfl

/-- 1-IH non-binder strength-T1 case: `Term.eitherInr`.

Mirror of `eitherInl`: unused left-type Ty payload plus inner Term IH. -/
theorem strengthenTyped?_rename_eq_eitherInr
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
    {leftType rightType : Ty level sourceScope}
    {valueRaw : RawTerm sourceScope}
    (valueTerm : Term sourceCtx rightType valueRaw)
    (valueIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming valueTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            valueTerm)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.eitherInr (leftType := leftType) valueTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.eitherInr (leftType := leftType) valueTerm)) := by
  dsimp only [Term.rename, partialStrengthenTyped?]
  have leftTypeStrengthens :
      (leftType.rename forwardRename).partialStrengthen? renameInverse
        = some leftType := by
    rw [Ty.partialStrengthen?_rename_some leftType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity leftType]
  split
  next noLeftSuccess =>
    exact absurd (leftTypeStrengthens.symm.trans noLeftSuccess)
      (by intro contra; cases contra)
  next targetLeftType leftSuccess =>
    have leftEq : targetLeftType = leftType :=
      Option.some.inj (leftSuccess.symm.trans leftTypeStrengthens)
    subst leftEq
    split
    next noValueSuccess =>
      exact absurd (valueIH.symm.trans noValueSuccess)
        (by intro contra; cases contra)
    next valueResult valueSuccess =>
      have resultEq : valueResult =
          StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects valueTerm :=
        Option.some.inj (valueSuccess.symm.trans valueIH)
      subst resultEq
      rfl

/-- 1-IH non-binder strength-T1 case: `Term.sessionRecv`.

Carries an inner channel Term IH plus an unused protocolStep RawTerm
payload.  The dispatcher first matches the protocolStep's renaming-image
(via subst-via-witness at the raw layer) then recurses on the channel. -/
theorem strengthenTyped?_rename_eq_sessionRecv
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
    {protocolStep : RawTerm sourceScope}
    {channelRaw : RawTerm sourceScope}
    (channel : Term sourceCtx (Ty.session protocolStep) channelRaw)
    (channelIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming channel)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            channel)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming (Term.sessionRecv channel))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.sessionRecv channel)) := by
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
      have resultEq : channelResult =
          StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects channel :=
        Option.some.inj (channelSuccess.symm.trans channelIH)
      subst resultEq
      rfl

/-- 1-IH non-binder strength-T1 case: `Term.cumulUp`.

Cumulativity promotion wraps a single Term IH plus value-level universe
data (lower/higher levels, monotonicity proof, level-fits-in-universe
witnesses); none of those are scope-indexed, so no Ty/Raw witness is
needed.  Dispatcher recurses on the type-code and combines through
`partialStrengthenTypedCumulUp`. -/
theorem strengthenTyped?_rename_eq_cumulUp
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
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {codeRaw : RawTerm sourceScope}
    (typeCode : Term sourceCtx (Ty.universe lowerLevel levelLeLow) codeRaw)
    (codeIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming typeCode)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            typeCode)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.cumulUp lowerLevel higherLevel cumulMonotone levelLeLow
            levelLeHigh typeCode))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.cumulUp lowerLevel higherLevel cumulMonotone levelLeLow
            levelLeHigh typeCode)) := by
  dsimp only [Term.rename, partialStrengthenTyped?]
  split
  next noCodeSuccess =>
    exact absurd (codeIH.symm.trans noCodeSuccess)
      (by intro contra; cases contra)
  next codeResult codeSuccess =>
    have resultEq : codeResult =
        StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects typeCode :=
      Option.some.inj (codeSuccess.symm.trans codeIH)
    subst resultEq
    rfl

end Term

end LeanFX2
