import LeanFX2.Term.PartialStrengthen.RenameImage.UnaryBasic

/-! # Term/PartialStrengthen/RenameImage/UnaryStructured

Rename-image T1 equations for structured one-subterm non-binder cases.
-/

namespace LeanFX2

namespace Term

/-- 1-IH non-binder strength-T1 case: `Term.recordProj`.

Single-field record projection wraps a record Term IH and a Ty payload
(`singleFieldType`).  Dispatcher matches the singleFieldType's renaming-
image first (via subst-via-witness), then recurses on the record value. -/
theorem strengthenTyped?_rename_eq_recordProj
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
    {singleFieldType : Ty level sourceScope}
    {recordRaw : RawTerm sourceScope}
    (recordValue : Term sourceCtx (Ty.record singleFieldType) recordRaw)
    (recordIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming recordValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            recordValue)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming (Term.recordProj recordValue))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.recordProj recordValue)) := by
  dsimp only [Term.rename, partialStrengthenTyped?]
  have fieldStrengthens :
      (singleFieldType.rename forwardRename).partialStrengthen? renameInverse
        = some singleFieldType := by
    rw [Ty.partialStrengthen?_rename_some singleFieldType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity singleFieldType]
  split
  next noFieldSuccess =>
    exact absurd (fieldStrengthens.symm.trans noFieldSuccess)
      (by intro contra; cases contra)
  next targetFieldType fieldSuccess =>
    have fieldEq : targetFieldType = singleFieldType :=
      Option.some.inj (fieldSuccess.symm.trans fieldStrengthens)
    subst fieldEq
    split
    next noRecordSuccess =>
      exact absurd (recordIH.symm.trans noRecordSuccess)
        (by intro contra; cases contra)
    next recordResult recordSuccess =>
      have resultEq : recordResult =
          StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects recordValue :=
        Option.some.inj (recordSuccess.symm.trans recordIH)
      subst resultEq
      rfl

/-- 1-IH non-binder strength-T1 case: `Term.codataDest`.

Codata destruction wraps a single codata Term IH and two Ty payloads
(`stateType`, `outputType`).  Dispatcher matches the two Ty's renaming-
images first (via two sequential subst-via-witness steps), then recurses
on the codata value. -/
theorem strengthenTyped?_rename_eq_codataDest
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
    {codataRaw : RawTerm sourceScope}
    (codataValue : Term sourceCtx (Ty.codata stateType outputType) codataRaw)
    (codataIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming codataValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            codataValue)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming (Term.codataDest codataValue))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.codataDest codataValue)) := by
  dsimp only [Term.rename, partialStrengthenTyped?]
  have stateStrengthens :
      (stateType.rename forwardRename).partialStrengthen? renameInverse
        = some stateType := by
    rw [Ty.partialStrengthen?_rename_some stateType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity stateType]
  have outputStrengthens :
      (outputType.rename forwardRename).partialStrengthen? renameInverse
        = some outputType := by
    rw [Ty.partialStrengthen?_rename_some outputType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity outputType]
  split
  next noStateSuccess =>
    exact absurd (stateStrengthens.symm.trans noStateSuccess)
      (by intro contra; cases contra)
  next targetStateType stateSuccess =>
    have stateEq : targetStateType = stateType :=
      Option.some.inj (stateSuccess.symm.trans stateStrengthens)
    subst stateEq
    split
    next noOutputSuccess =>
      exact absurd (outputStrengthens.symm.trans noOutputSuccess)
        (by intro contra; cases contra)
    next targetOutputType outputSuccess =>
      have outputEq : targetOutputType = outputType :=
        Option.some.inj (outputSuccess.symm.trans outputStrengthens)
      subst outputEq
      split
      next noCodataSuccess =>
        exact absurd (codataIH.symm.trans noCodataSuccess)
          (by intro contra; cases contra)
      next codataResult codataSuccess =>
        have resultEq : codataResult =
            StrengtheningResult.fromRename forwardRename typedRenaming
              renameInverse renameInverseLeft renameInverseInjects
              codataValue :=
          Option.some.inj (codataSuccess.symm.trans codataIH)
        subst resultEq
        rfl

/-- 1-IH non-binder strength-T1 case: `Term.recordIntro`.

Single-field record introduction wraps a single Term IH for the field
value; `singleFieldType` is implicit (carried through the field's
typing).  Same shape as `optionSome` — dispatcher recurses on the field
and combines through `partialStrengthenTypedRecordIntro`. -/
theorem strengthenTyped?_rename_eq_recordIntro
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
    {singleFieldType : Ty level sourceScope}
    {firstRaw : RawTerm sourceScope}
    (firstField : Term sourceCtx singleFieldType firstRaw)
    (fieldIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming firstField)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            firstField)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming (Term.recordIntro firstField))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.recordIntro firstField)) := by
  dsimp only [Term.rename, partialStrengthenTyped?]
  split
  next noFieldSuccess =>
    exact absurd (fieldIH.symm.trans noFieldSuccess)
      (by intro contra; cases contra)
  next fieldResult fieldSuccess =>
    have resultEq : fieldResult =
        StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects firstField :=
      Option.some.inj (fieldSuccess.symm.trans fieldIH)
    subst resultEq
    rfl

/-- 1-IH non-binder strength-T1 case: `Term.glueElim`.

Cubical glue elimination wraps a single glued-value Term IH plus a Ty
payload (`baseType`), a RawTerm payload (`boundaryWitness`), and a mode-
univalence equality.  Dispatcher first matches baseType, then
boundaryWitness, then recurses on the glued value. -/
theorem strengthenTyped?_rename_eq_glueElim
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
    {baseType : Ty level sourceScope}
    {boundaryWitness gluedRaw : RawTerm sourceScope}
    (gluedValue : Term sourceCtx (Ty.glue baseType boundaryWitness) gluedRaw)
    (gluedIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming gluedValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            gluedValue)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming (Term.glueElim modeIsUnivalent gluedValue))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.glueElim modeIsUnivalent gluedValue)) := by
  dsimp only [Term.rename, partialStrengthenTyped?]
  have baseStrengthens :
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
  next noBaseSuccess =>
    exact absurd (baseStrengthens.symm.trans noBaseSuccess)
      (by intro contra; cases contra)
  next targetBaseType baseSuccess =>
    have baseEq : targetBaseType = baseType :=
      Option.some.inj (baseSuccess.symm.trans baseStrengthens)
    subst baseEq
    split
    next noBoundarySuccess =>
      exact absurd (boundaryStrengthens.symm.trans noBoundarySuccess)
        (by intro contra; cases contra)
    next targetBoundary boundarySuccess =>
      have boundaryEq : targetBoundary = boundaryWitness :=
        Option.some.inj (boundarySuccess.symm.trans boundaryStrengthens)
      subst boundaryEq
      split
      next noGluedSuccess =>
        exact absurd (gluedIH.symm.trans noGluedSuccess)
          (by intro contra; cases contra)
      next gluedResult gluedSuccess =>
        have resultEq : gluedResult =
            StrengtheningResult.fromRename forwardRename typedRenaming
              renameInverse renameInverseLeft renameInverseInjects
              gluedValue :=
          Option.some.inj (gluedSuccess.symm.trans gluedIH)
        subst resultEq
        rfl

end Term

end LeanFX2
