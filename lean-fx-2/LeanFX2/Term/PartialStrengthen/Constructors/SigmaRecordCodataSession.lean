import LeanFX2.Term.PartialStrengthen.Constructors.Identity

/-! # Term/PartialStrengthen/Constructors/SigmaRecordCodataSession

Typed partial-strengthening producers for sigma pairs and projections,
records, codata, and session send/receive terms.
-/

namespace LeanFX2

namespace Term

/-- Sigma pair strengthens by strengthening both components and the
binder-indexed second component type. -/
def partialStrengthenTypedPair {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {targetSecondType : Ty level (targetScope + 1)}
    {firstRaw secondRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {firstValue : Term sourceCtx firstType firstRaw}
    {secondValue :
      Term sourceCtx (secondType.subst0 firstType firstRaw) secondRaw}
    (secondTypeStrengthens :
      secondType.partialStrengthen? strengthening.back.lift =
        some targetSecondType)
    (firstResult : StrengtheningResult strengthening firstValue)
    (secondResult : StrengtheningResult strengthening secondValue) :
    StrengtheningResult strengthening
      (Term.pair firstValue secondValue) := by
  cases firstResult with
  | mk targetFirstType targetFirstRaw targetFirstTerm firstTypeStrengthens
      firstRawStrengthens firstTypeRenames firstRawRenames =>
      cases secondResult with
      | mk targetSecondValueType targetSecondRaw targetSecondTerm
          secondValueTypeStrengthens secondRawStrengthens
          secondValueTypeRenames secondRawRenames =>
          have expectedSecondValueStrengthens :
              (secondType.subst0 firstType firstRaw).partialStrengthen?
                  strengthening.back =
                some (targetSecondType.subst0 targetFirstType
                  targetFirstRaw) :=
            Ty.partialStrengthen?_subst0_of_success secondType
              targetSecondType firstType targetFirstType firstRaw
              targetFirstRaw strengthening.forward strengthening.back
              strengthening.injectsBack strengthening.back_forward
              secondTypeStrengthens firstTypeStrengthens
              firstRawStrengthens
          rw [expectedSecondValueStrengthens] at secondValueTypeStrengthens
          cases secondValueTypeStrengthens
          exact {
            targetType := Ty.sigmaTy targetFirstType targetSecondType
            targetRaw := RawTerm.pair targetFirstRaw targetSecondRaw
            targetTerm := Term.pair targetFirstTerm targetSecondTerm
            typeStrengthens := by
              change
                Option.mapTwo
                  (firstType.partialStrengthen? strengthening.back)
                  (secondType.partialStrengthen? strengthening.back.lift)
                  Ty.sigmaTy =
                  some (Ty.sigmaTy targetFirstType targetSecondType)
              rw [firstTypeStrengthens, secondTypeStrengthens]
              rfl
            rawStrengthens := by
              change
                Option.mapTwo
                  (firstRaw.partialStrengthen? strengthening.back)
                  (secondRaw.partialStrengthen? strengthening.back)
                  RawTerm.pair =
                  some (RawTerm.pair targetFirstRaw targetSecondRaw)
              rw [firstRawStrengthens, secondRawStrengthens]
              rfl
            typeRenames := by
              simp only [Ty.rename]
              rw [firstTypeRenames]
              exact congrArg (Ty.sigmaTy (targetFirstType.rename
                  strengthening.forward))
                (Ty.partialStrengthen?_imp_rename secondType
                  strengthening.forward.lift strengthening.back.lift
                  (PartialRawRenaming.lift_renamingInjectsBack
                    strengthening.injectsBack)
                  targetSecondType secondTypeStrengthens)
            rawRenames := by
              cases firstRawRenames
              cases secondRawRenames
              rfl
          }

/-- Sigma first projection strengthens by strengthening its pair payload. -/
def partialStrengthenTypedFst {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {targetFirstType : Ty level targetScope}
    {targetSecondType : Ty level (targetScope + 1)}
    {pairRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {pairTerm : Term sourceCtx (Ty.sigmaTy firstType secondType) pairRaw}
    (firstSuccess :
      firstType.partialStrengthen? strengthening.back =
        some targetFirstType)
    (secondSuccess :
      secondType.partialStrengthen? strengthening.back.lift =
        some targetSecondType)
    (pairResult : StrengtheningResult strengthening pairTerm) :
    StrengtheningResult strengthening (Term.fst pairTerm) := by
  cases pairResult with
  | mk targetType targetRaw targetTerm typeStrengthens rawStrengthens
      typeRenames rawRenames =>
      change
        Option.mapTwo
          (firstType.partialStrengthen? strengthening.back)
          (secondType.partialStrengthen? strengthening.back.lift)
          Ty.sigmaTy = some targetType at typeStrengthens
      rw [firstSuccess, secondSuccess] at typeStrengthens
      cases typeStrengthens
      exact {
        targetType := targetFirstType
        targetRaw := RawTerm.fst targetRaw
        targetTerm := Term.fst targetTerm
        typeStrengthens := firstSuccess
        rawStrengthens := by
          change
            (match pairRaw.partialStrengthen? strengthening.back with
            | some strengthenedPair => some (RawTerm.fst strengthenedPair)
            | none => none) =
              some (RawTerm.fst targetRaw)
          rw [rawStrengthens]
        typeRenames := by
          injection typeRenames
        rawRenames := congrArg RawTerm.fst rawRenames
      }

/-- Sigma second projection strengthens by strengthening its pair payload
and rebuilding the dependent result type with the strengthened first
projection. -/
def partialStrengthenTypedSnd {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {targetFirstType : Ty level targetScope}
    {targetSecondType : Ty level (targetScope + 1)}
    {pairRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {pairTerm : Term sourceCtx (Ty.sigmaTy firstType secondType) pairRaw}
    (firstSuccess :
      firstType.partialStrengthen? strengthening.back =
        some targetFirstType)
    (secondSuccess :
      secondType.partialStrengthen? strengthening.back.lift =
        some targetSecondType)
    (pairResult : StrengtheningResult strengthening pairTerm) :
    StrengtheningResult strengthening (Term.snd pairTerm) := by
  cases pairResult with
  | mk targetType targetRaw targetTerm typeStrengthens rawStrengthens
      typeRenames rawRenames =>
      change
        Option.mapTwo
          (firstType.partialStrengthen? strengthening.back)
          (secondType.partialStrengthen? strengthening.back.lift)
          Ty.sigmaTy = some targetType at typeStrengthens
      rw [firstSuccess, secondSuccess] at typeStrengthens
      cases typeStrengthens
      have fstRawStrengthens :
          (RawTerm.fst pairRaw).partialStrengthen?
              strengthening.back =
            some (RawTerm.fst targetRaw) := by
        change
          (match pairRaw.partialStrengthen? strengthening.back with
          | some strengthenedPair => some (RawTerm.fst strengthenedPair)
          | none => none) =
            some (RawTerm.fst targetRaw)
        rw [rawStrengthens]
      have sndTypeStrengthens :
          (secondType.subst0 firstType
              (RawTerm.fst pairRaw)).partialStrengthen?
            strengthening.back =
            some (targetSecondType.subst0 targetFirstType
              (RawTerm.fst targetRaw)) :=
        Ty.partialStrengthen?_subst0_of_success secondType
          targetSecondType firstType targetFirstType
          (RawTerm.fst pairRaw) (RawTerm.fst targetRaw)
          strengthening.forward strengthening.back
          strengthening.injectsBack strengthening.back_forward
          secondSuccess firstSuccess fstRawStrengthens
      exact {
        targetType := targetSecondType.subst0 targetFirstType
          (RawTerm.fst targetRaw)
        targetRaw := RawTerm.snd targetRaw
        targetTerm := Term.snd targetTerm
        typeStrengthens := sndTypeStrengthens
        rawStrengthens := by
          change
            (match pairRaw.partialStrengthen? strengthening.back with
            | some strengthenedPair => some (RawTerm.snd strengthenedPair)
            | none => none) =
              some (RawTerm.snd targetRaw)
          rw [rawStrengthens]
        typeRenames :=
          Ty.partialStrengthen?_imp_rename
            (secondType.subst0 firstType (RawTerm.fst pairRaw))
            strengthening.forward strengthening.back
            strengthening.injectsBack
            (targetSecondType.subst0 targetFirstType
              (RawTerm.fst targetRaw))
            sndTypeStrengthens
        rawRenames := congrArg RawTerm.snd rawRenames
      }

/-- Record introduction strengthens by strengthening its field. -/
def partialStrengthenTypedRecordIntro {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {singleFieldType : Ty level sourceScope}
    {firstRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {firstField : Term sourceCtx singleFieldType firstRaw}
    (fieldResult : StrengtheningResult strengthening firstField) :
    StrengtheningResult strengthening (Term.recordIntro firstField) where
  targetType := Ty.record fieldResult.targetType
  targetRaw := RawTerm.recordIntro fieldResult.targetRaw
  targetTerm := Term.recordIntro fieldResult.targetTerm
  typeStrengthens := by
    change
      (match singleFieldType.partialStrengthen? strengthening.back with
      | some strengthenedField => some (Ty.record strengthenedField)
      | none => none) =
        some (Ty.record fieldResult.targetType)
    rw [fieldResult.typeStrengthens]
  rawStrengthens := by
    change
      (match firstRaw.partialStrengthen? strengthening.back with
      | some strengthenedField => some (RawTerm.recordIntro strengthenedField)
      | none => none) =
        some (RawTerm.recordIntro fieldResult.targetRaw)
    rw [fieldResult.rawStrengthens]
  typeRenames := congrArg Ty.record fieldResult.typeRenames
  rawRenames := congrArg RawTerm.recordIntro fieldResult.rawRenames

/-- Success branch for record-projection strengthening.

Takes the pre-decomposed strengthened field type and the strengthened
record-valued term as explicit witnesses, splitting out the term-mode
body so the strengthening-image soundness layer can prove it without
traversing `Option.casesOn` on the `singleFieldType.partialStrengthen?`
pivot in the wrapper's tactic-mode `cases` chain. -/
def partialStrengthenTypedRecordProjOfSuccess {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {singleFieldType : Ty level sourceScope}
    {recordRaw : RawTerm sourceScope}
    {targetFieldType : Ty level targetScope}
    {targetRecordRaw : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {recordValue : Term sourceCtx (Ty.record singleFieldType) recordRaw}
    (targetRecordTerm :
      Term targetCtx (Ty.record targetFieldType) targetRecordRaw)
    (fieldSuccess :
      singleFieldType.partialStrengthen? strengthening.back =
        some targetFieldType)
    (recordRawStrengthens :
      recordRaw.partialStrengthen? strengthening.back =
        some targetRecordRaw)
    (recordRawRenames :
      recordRaw = targetRecordRaw.rename strengthening.forward) :
    StrengtheningResult strengthening (Term.recordProj recordValue) := {
  targetType := targetFieldType
  targetRaw := RawTerm.recordProj targetRecordRaw
  targetTerm := Term.recordProj targetRecordTerm
  typeStrengthens := fieldSuccess
  rawStrengthens := by
    change
      (match recordRaw.partialStrengthen? strengthening.back with
        | some strengthenedRecord =>
            some (RawTerm.recordProj strengthenedRecord)
        | none => none) =
        some (RawTerm.recordProj targetRecordRaw)
    rw [recordRawStrengthens]
  typeRenames :=
    Ty.partialStrengthen?_imp_rename singleFieldType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetFieldType fieldSuccess
  rawRenames := by
    cases recordRawRenames
    rfl
}

/-- Record projection strengthens by strengthening its record payload.

App-pattern: takes the field-type strengthening witness `fieldSuccess`
as an explicit parameter, lifted from the dispatcher's option-split.
The body destructures the record's `StrengtheningResult`, aligns the
`Ty.record` shape via `rw` + `cases` on the derived equation, then
delegates to `partialStrengthenTypedRecordProjOfSuccess`.  This shape
admits a clean App-pattern soundness proof
(`partialStrengthenTypedRecordProj_sound`) by mirror-destructuring +
final-arm `OfSuccess_sound` delegation. -/
def partialStrengthenTypedRecordProj {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {singleFieldType : Ty level sourceScope}
    {targetFieldType : Ty level targetScope}
    {recordRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {recordValue : Term sourceCtx (Ty.record singleFieldType) recordRaw}
    (fieldSuccess :
      singleFieldType.partialStrengthen? strengthening.back =
        some targetFieldType)
    (recordResult : StrengtheningResult strengthening recordValue) :
    StrengtheningResult strengthening (Term.recordProj recordValue) := by
  cases recordResult with
  | mk targetType targetRaw targetTerm typeStrengthens rawStrengthens
      typeRenames rawRenames =>
      have expectedRecordTypeStrengthens :
          (Ty.record singleFieldType).partialStrengthen? strengthening.back =
            some (Ty.record targetFieldType) := by
        change
          (match singleFieldType.partialStrengthen? strengthening.back with
          | some strengthenedField => some (Ty.record strengthenedField)
          | none => none) =
            some (Ty.record targetFieldType)
        rw [fieldSuccess]
      rw [expectedRecordTypeStrengthens] at typeStrengthens
      cases typeStrengthens
      exact partialStrengthenTypedRecordProjOfSuccess
        targetTerm fieldSuccess rawStrengthens rawRenames

/-- Success branch for codata-unfold strengthening.

Takes pre-decomposed witnesses for the state type, output type, and
both raw component strengthenings.  Splits the term-mode body so the
strengthening-image soundness layer can prove it without traversing
`Eq.casesOn` on the arrow-decomposed transition type strengthening. -/
def partialStrengthenTypedCodataUnfoldOfSuccess {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {stateType outputType : Ty level sourceScope}
    {targetStateType targetOutputType : Ty level targetScope}
    {stateRaw transitionRaw : RawTerm sourceScope}
    {targetStateRaw targetTransitionRaw : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {initialState : Term sourceCtx stateType stateRaw}
    {transition :
      Term sourceCtx (Ty.arrow stateType outputType) transitionRaw}
    (targetStateTerm : Term targetCtx targetStateType targetStateRaw)
    (targetTransitionTerm :
      Term targetCtx (Ty.arrow targetStateType targetOutputType)
        targetTransitionRaw)
    (stateTypeStrengthens :
      stateType.partialStrengthen? strengthening.back = some targetStateType)
    (outputTypeStrengthens :
      outputType.partialStrengthen? strengthening.back =
        some targetOutputType)
    (stateRawStrengthens :
      stateRaw.partialStrengthen? strengthening.back =
        some targetStateRaw)
    (transitionRawStrengthens :
      transitionRaw.partialStrengthen? strengthening.back =
        some targetTransitionRaw)
    (stateRawRenames :
      stateRaw = targetStateRaw.rename strengthening.forward)
    (transitionRawRenames :
      transitionRaw = targetTransitionRaw.rename strengthening.forward) :
    StrengtheningResult strengthening
      (Term.codataUnfold initialState transition) := {
  targetType := Ty.codata targetStateType targetOutputType
  targetRaw := RawTerm.codataUnfold targetStateRaw targetTransitionRaw
  targetTerm := Term.codataUnfold targetStateTerm targetTransitionTerm
  typeStrengthens := by
    change
      Option.mapTwo
        (stateType.partialStrengthen? strengthening.back)
        (outputType.partialStrengthen? strengthening.back)
        Ty.codata =
        some (Ty.codata targetStateType targetOutputType)
    rw [stateTypeStrengthens, outputTypeStrengthens]
    rfl
  rawStrengthens := by
    change
      Option.mapTwo
        (stateRaw.partialStrengthen? strengthening.back)
        (transitionRaw.partialStrengthen? strengthening.back)
        RawTerm.codataUnfold =
        some (RawTerm.codataUnfold targetStateRaw targetTransitionRaw)
    rw [stateRawStrengthens, transitionRawStrengthens]
    rfl
  typeRenames :=
    Ty.partialStrengthen?_imp_rename (Ty.codata stateType outputType)
      strengthening.forward strengthening.back strengthening.injectsBack
      (Ty.codata targetStateType targetOutputType)
      (by
        change
          Option.mapTwo
            (stateType.partialStrengthen? strengthening.back)
            (outputType.partialStrengthen? strengthening.back)
            Ty.codata =
            some (Ty.codata targetStateType targetOutputType)
        rw [stateTypeStrengthens, outputTypeStrengthens]
        rfl)
  rawRenames := by
    cases stateRawRenames
    cases transitionRawRenames
    rfl
}

/-- Codata unfold strengthens by strengthening the initial state, the
transition function, and the output type index used by the codata
carrier. -/
def partialStrengthenTypedCodataUnfold {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {stateType outputType : Ty level sourceScope}
    {targetOutputType : Ty level targetScope}
    {stateRaw transitionRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {initialState : Term sourceCtx stateType stateRaw}
    {transition :
      Term sourceCtx (Ty.arrow stateType outputType) transitionRaw}
    (outputTypeStrengthens :
      outputType.partialStrengthen? strengthening.back =
        some targetOutputType)
    (stateResult : StrengtheningResult strengthening initialState)
    (transitionResult : StrengtheningResult strengthening transition) :
    StrengtheningResult strengthening
      (Term.codataUnfold initialState transition) := by
  cases stateResult with
  | mk targetStateType targetStateRaw targetStateTerm stateTypeStrengthens
      stateRawStrengthens stateTypeRenames stateRawRenames =>
      cases transitionResult with
      | mk targetTransitionType targetTransitionRaw targetTransitionTerm
          transitionTypeStrengthens transitionRawStrengthens
          transitionTypeRenames transitionRawRenames =>
          change
            Option.mapTwo
              (stateType.partialStrengthen? strengthening.back)
              (outputType.partialStrengthen? strengthening.back)
              Ty.arrow = some targetTransitionType at transitionTypeStrengthens
          rw [stateTypeStrengthens, outputTypeStrengthens]
            at transitionTypeStrengthens
          cases transitionTypeStrengthens
          exact partialStrengthenTypedCodataUnfoldOfSuccess
            targetStateTerm targetTransitionTerm stateTypeStrengthens
            outputTypeStrengthens stateRawStrengthens transitionRawStrengthens
            stateRawRenames transitionRawRenames

/-- Success branch for codata-destruction strengthening.

Takes the pre-decomposed state and output type strengthenings plus the
strengthened codata-valued term as explicit witnesses, splitting the
term-mode body so the soundness layer can prove it without traversing
`Option.casesOn` on the state and output pivots. -/
def partialStrengthenTypedCodataDestOfSuccess {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {stateType outputType : Ty level sourceScope}
    {targetStateType targetOutputType : Ty level targetScope}
    {codataRaw : RawTerm sourceScope}
    {targetCodataRaw : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {codataValue : Term sourceCtx (Ty.codata stateType outputType) codataRaw}
    (targetCodataTerm :
      Term targetCtx (Ty.codata targetStateType targetOutputType)
        targetCodataRaw)
    (_stateSuccess :
      stateType.partialStrengthen? strengthening.back = some targetStateType)
    (outputSuccess :
      outputType.partialStrengthen? strengthening.back =
        some targetOutputType)
    (codataRawStrengthens :
      codataRaw.partialStrengthen? strengthening.back =
        some targetCodataRaw)
    (codataRawRenames :
      codataRaw = targetCodataRaw.rename strengthening.forward) :
    StrengtheningResult strengthening (Term.codataDest codataValue) := {
  targetType := targetOutputType
  targetRaw := RawTerm.codataDest targetCodataRaw
  targetTerm := Term.codataDest targetCodataTerm
  typeStrengthens := outputSuccess
  rawStrengthens := by
    change
      (match codataRaw.partialStrengthen? strengthening.back with
        | some strengthenedCodata =>
            some (RawTerm.codataDest strengthenedCodata)
        | none => none) =
        some (RawTerm.codataDest targetCodataRaw)
    rw [codataRawStrengthens]
  typeRenames :=
    Ty.partialStrengthen?_imp_rename outputType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetOutputType outputSuccess
  rawRenames := by
    cases codataRawRenames
    rfl
}

/-- Codata destruction strengthens by strengthening the codata payload
and projecting both the state and output strengthenings out of the
codata type index.

App-pattern: takes `stateSuccess` / `outputSuccess` as explicit
parameters lifted from the dispatcher's two option-splits.  The body
destructures the codata value's `StrengtheningResult`, aligns the
`Ty.codata` shape via `rw` + `cases` on the derived equation, then
delegates to `partialStrengthenTypedCodataDestOfSuccess`.  Mirrors the
2-option-split recipe established for RefineElim (Phase 39). -/
def partialStrengthenTypedCodataDest {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {stateType outputType : Ty level sourceScope}
    {targetStateType targetOutputType : Ty level targetScope}
    {codataRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {codataValue : Term sourceCtx (Ty.codata stateType outputType) codataRaw}
    (stateSuccess :
      stateType.partialStrengthen? strengthening.back = some targetStateType)
    (outputSuccess :
      outputType.partialStrengthen? strengthening.back =
        some targetOutputType)
    (codataResult : StrengtheningResult strengthening codataValue) :
    StrengtheningResult strengthening (Term.codataDest codataValue) := by
  cases codataResult with
  | mk targetCodataType targetCodataRaw targetCodataTerm
      codataTypeStrengthens codataRawStrengthens codataTypeRenames
      codataRawRenames =>
      have expectedCodataTypeStrengthens :
          (Ty.codata stateType outputType).partialStrengthen?
              strengthening.back =
            some (Ty.codata targetStateType targetOutputType) := by
        change
          Option.mapTwo
            (stateType.partialStrengthen? strengthening.back)
            (outputType.partialStrengthen? strengthening.back)
            Ty.codata =
              some (Ty.codata targetStateType targetOutputType)
        rw [stateSuccess, outputSuccess]
        rfl
      rw [expectedCodataTypeStrengthens] at codataTypeStrengthens
      cases codataTypeStrengthens
      exact partialStrengthenTypedCodataDestOfSuccess
        targetCodataTerm stateSuccess outputSuccess
        codataRawStrengthens codataRawRenames

/-- Session send strengthens by strengthening the protocol raw, channel,
and payload while preserving the session carrier shape. -/
def partialStrengthenTypedSessionSend {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {protocolStep : RawTerm sourceScope}
    {targetProtocolStep : RawTerm targetScope}
    {payloadType : Ty level sourceScope}
    {channelRaw payloadRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {channel : Term sourceCtx (Ty.session protocolStep) channelRaw}
    {payload : Term sourceCtx payloadType payloadRaw}
    (protocolStrengthens :
      protocolStep.partialStrengthen? strengthening.back =
        some targetProtocolStep)
    (channelResult : StrengtheningResult strengthening channel)
    (payloadResult : StrengtheningResult strengthening payload) :
    StrengtheningResult strengthening
      (Term.sessionSend protocolStep channel payload) := by
  cases channelResult with
  | mk targetChannelType targetChannelRaw targetChannelTerm
      channelTypeStrengthens channelRawStrengthens channelTypeRenames
      channelRawRenames =>
      change
        (match protocolStep.partialStrengthen? strengthening.back with
        | some strengthenedProtocol => some (Ty.session strengthenedProtocol)
        | none => none) = some targetChannelType at channelTypeStrengthens
      rw [protocolStrengthens] at channelTypeStrengthens
      cases channelTypeStrengthens
      cases payloadResult with
      | mk targetPayloadType targetPayloadRaw targetPayloadTerm
          payloadTypeStrengthens payloadRawStrengthens payloadTypeRenames
          payloadRawRenames =>
          exact {
            targetType := Ty.session targetProtocolStep
            targetRaw := RawTerm.sessionSend targetChannelRaw targetPayloadRaw
            targetTerm := Term.sessionSend targetProtocolStep
              targetChannelTerm targetPayloadTerm
            typeStrengthens := by
              change
                (match protocolStep.partialStrengthen? strengthening.back with
                | some strengthenedProtocol =>
                    some (Ty.session strengthenedProtocol)
                | none => none) = some (Ty.session targetProtocolStep)
              rw [protocolStrengthens]
            rawStrengthens := by
              change
                Option.mapTwo
                  (channelRaw.partialStrengthen? strengthening.back)
                  (payloadRaw.partialStrengthen? strengthening.back)
                  RawTerm.sessionSend =
                    some (RawTerm.sessionSend targetChannelRaw
                      targetPayloadRaw)
              rw [channelRawStrengthens, payloadRawStrengthens]
              rfl
            typeRenames :=
              Ty.partialStrengthen?_imp_rename (Ty.session protocolStep)
                strengthening.forward strengthening.back
                strengthening.injectsBack (Ty.session targetProtocolStep)
                (by
                  change
                    (match protocolStep.partialStrengthen?
                        strengthening.back with
                    | some strengthenedProtocol =>
                        some (Ty.session strengthenedProtocol)
                    | none => none) = some (Ty.session targetProtocolStep)
                  rw [protocolStrengthens])
            rawRenames := by
              cases channelRawRenames
              cases payloadRawRenames
              rfl
          }

/-- Session receive strengthens by strengthening the channel and
protocol raw while preserving the session carrier shape. -/
def partialStrengthenTypedSessionRecv {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {protocolStep : RawTerm sourceScope}
    {targetProtocolStep : RawTerm targetScope}
    {channelRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {channel : Term sourceCtx (Ty.session protocolStep) channelRaw}
    (protocolStrengthens :
      protocolStep.partialStrengthen? strengthening.back =
        some targetProtocolStep)
    (channelResult : StrengtheningResult strengthening channel) :
    StrengtheningResult strengthening (Term.sessionRecv channel) := by
  cases channelResult with
  | mk targetChannelType targetChannelRaw targetChannelTerm
      channelTypeStrengthens channelRawStrengthens channelTypeRenames
      channelRawRenames =>
      change
        (match protocolStep.partialStrengthen? strengthening.back with
        | some strengthenedProtocol => some (Ty.session strengthenedProtocol)
        | none => none) = some targetChannelType at channelTypeStrengthens
      rw [protocolStrengthens] at channelTypeStrengthens
      cases channelTypeStrengthens
      exact {
        targetType := Ty.session targetProtocolStep
        targetRaw := RawTerm.sessionRecv targetChannelRaw
        targetTerm := Term.sessionRecv targetChannelTerm
        typeStrengthens := by
          change
            (match protocolStep.partialStrengthen? strengthening.back with
            | some strengthenedProtocol =>
                some (Ty.session strengthenedProtocol)
            | none => none) = some (Ty.session targetProtocolStep)
          rw [protocolStrengthens]
        rawStrengthens := by
          change
            (match channelRaw.partialStrengthen? strengthening.back with
            | some strengthenedChannel =>
                some (RawTerm.sessionRecv strengthenedChannel)
            | none => none) = some (RawTerm.sessionRecv targetChannelRaw)
          rw [channelRawStrengthens]
        typeRenames :=
          Ty.partialStrengthen?_imp_rename (Ty.session protocolStep)
            strengthening.forward strengthening.back
            strengthening.injectsBack (Ty.session targetProtocolStep)
            (by
              change
                (match protocolStep.partialStrengthen? strengthening.back with
                | some strengthenedProtocol =>
                    some (Ty.session strengthenedProtocol)
                | none => none) = some (Ty.session targetProtocolStep)
              rw [protocolStrengthens])
        rawRenames := congrArg RawTerm.sessionRecv channelRawRenames
      }

end Term

end LeanFX2
