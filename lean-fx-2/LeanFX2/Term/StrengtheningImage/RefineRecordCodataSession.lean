import LeanFX2.Term.StrengtheningImage.Core

/-! # Term/StrengtheningImage/RefineRecordCodataSession

Soundness lemmas for refinement, record, codata, session, and cumulativity producers.
-/

namespace LeanFX2

namespace Term

/-- Soundness for refinement-introduction strengthening.  The proof
component lives at `Ty.unit`, which strengthens definitionally; the
predicate carrier and base value contribute the load-bearing renames. -/
theorem partialStrengthenTypedRefineIntro_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {baseType : Ty level sourceScope}
    {predicate : RawTerm (sourceScope + 1)}
    {targetPredicate : RawTerm (targetScope + 1)}
    {valueRaw proofRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {baseValue : Term sourceCtx baseType valueRaw}
    {predicateProof : Term sourceCtx Ty.unit proofRaw}
    (predicateStrengthens :
      predicate.partialStrengthen? strengthening.back.lift =
        some targetPredicate)
    {baseResult : StrengtheningResult strengthening baseValue}
    {proofResult : StrengtheningResult strengthening predicateProof}
    (baseSound : StrengtheningSoundness baseResult)
    (proofSound : StrengtheningSoundness proofResult) :
    StrengtheningSoundness
      (partialStrengthenTypedRefineIntro predicateStrengthens baseResult
        proofResult) := by
  cases proofResult with
  | mk targetProofType targetProofRaw targetProofTerm proofTypeStrengthens
      proofRawStrengthens proofTypeRenames proofRawRenames =>
      cases proofTypeStrengthens
      refine ⟨?_⟩
      dsimp [partialStrengthenTypedRefineIntro,
          StrengtheningResult.renamedTarget] at proofSound ⊢
      have predicateRenames :
          predicate = targetPredicate.rename strengthening.forward.lift :=
        RawTerm.partialStrengthen?_imp_rename predicate
          strengthening.forward.lift strengthening.back.lift
          (PartialRawRenaming.lift_renamingInjectsBack
            strengthening.injectsBack)
          targetPredicate predicateStrengthens
      exact Term.refineIntro_HEq_congr baseResult.typeRenames predicateRenames
        baseResult.rawRenames proofRawRenames
        baseSound.termRenames proofSound.termRenames

/-- Soundness for the success branch of refinement-elimination
strengthening.  Mirrors `partialStrengthenTypedListElimOfSuccess_sound`:
the term-mode OfSuccess body's record construction is what `dsimp`
unfolds, while the tactic-mode wrapper traversing `Option.casesOn` on
the base/predicate pivots is left unsounded by design. -/
theorem partialStrengthenTypedRefineElimOfSuccess_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {baseType : Ty level sourceScope}
    {predicate : RawTerm (sourceScope + 1)}
    {refinedRaw : RawTerm sourceScope}
    {targetBaseType : Ty level targetScope}
    {targetPredicate : RawTerm (targetScope + 1)}
    {targetRefinedRaw : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {refinedValue :
      Term sourceCtx (Ty.refine baseType predicate) refinedRaw}
    {targetRefinedTerm :
      Term targetCtx (Ty.refine targetBaseType targetPredicate)
        targetRefinedRaw}
    {baseSuccess :
      baseType.partialStrengthen? strengthening.back = some targetBaseType}
    {predicateSuccess :
      predicate.partialStrengthen? strengthening.back.lift =
        some targetPredicate}
    {refinedRawStrengthens :
      refinedRaw.partialStrengthen? strengthening.back =
        some targetRefinedRaw}
    {refinedRawRenames :
      refinedRaw = targetRefinedRaw.rename strengthening.forward}
    (refinedSound :
      HEq refinedValue
        (Term.rename strengthening.toTermRenaming targetRefinedTerm)) :
    StrengtheningSoundness
      (partialStrengthenTypedRefineElimOfSuccess
        (refinedValue := refinedValue)
        targetRefinedTerm baseSuccess predicateSuccess refinedRawStrengthens
        refinedRawRenames) := by
  refine ⟨?_⟩
  unfold StrengtheningResult.renamedTarget
  dsimp [partialStrengthenTypedRefineElimOfSuccess]
  have baseRenames :
      baseType = targetBaseType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename baseType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetBaseType baseSuccess
  have predicateRenames :
      predicate = targetPredicate.rename strengthening.forward.lift :=
    RawTerm.partialStrengthen?_imp_rename predicate
      strengthening.forward.lift strengthening.back.lift
      (PartialRawRenaming.lift_renamingInjectsBack
        strengthening.injectsBack)
      targetPredicate predicateSuccess
  exact Term.refineElim_HEq_congr baseRenames predicateRenames
    refinedRawRenames refinedSound

/-- Soundness for the typed refinement-elimination wrapper.

Mirrors `partialStrengthenTypedRefineElim`'s App-pattern shape: the
wrapper takes `baseSuccess` and `predicateSuccess` as explicit
parameters (lifted from the dispatcher's two nested option-splits on
base type and predicate respectively).  The proof destructures the
refined value's `StrengtheningResult`, aligns the `Ty.refine` shape via
`rw` + `cases` on the derived equation, then delegates to
`partialStrengthenTypedRefineElimOfSuccess_sound`.  Bypasses Lean
4.29.1 tactic-mode opacity on the original ListElim-pattern wrapper
with two internal option-splits. -/
theorem partialStrengthenTypedRefineElim_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {baseType : Ty level sourceScope}
    {predicate : RawTerm (sourceScope + 1)}
    {targetBaseType : Ty level targetScope}
    {targetPredicate : RawTerm (targetScope + 1)}
    {refinedRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {refinedValue :
      Term sourceCtx (Ty.refine baseType predicate) refinedRaw}
    (baseSuccess :
      baseType.partialStrengthen? strengthening.back = some targetBaseType)
    (predicateSuccess :
      predicate.partialStrengthen? strengthening.back.lift =
        some targetPredicate)
    {refinedResult : StrengtheningResult strengthening refinedValue}
    (refinedSound : StrengtheningSoundness refinedResult) :
    StrengtheningSoundness
      (partialStrengthenTypedRefineElim baseSuccess predicateSuccess
        refinedResult) := by
  cases refinedResult with
  | mk targetType targetRaw targetTerm typeStrengthens rawStrengthens
      typeRenames rawRenames =>
      have expectedRefineTypeStrengthens :
          (Ty.refine baseType predicate).partialStrengthen?
              strengthening.back =
            some (Ty.refine targetBaseType targetPredicate) := by
        change
          Option.mapTwo
            (baseType.partialStrengthen? strengthening.back)
            (predicate.partialStrengthen? strengthening.back.lift)
            Ty.refine =
              some (Ty.refine targetBaseType targetPredicate)
        rw [baseSuccess, predicateSuccess]
        rfl
      rw [expectedRefineTypeStrengthens] at typeStrengthens
      cases typeStrengthens
      exact partialStrengthenTypedRefineElimOfSuccess_sound
        (baseSuccess := baseSuccess)
        (predicateSuccess := predicateSuccess)
        (refinedRawStrengthens := rawStrengthens)
        (refinedRawRenames := rawRenames)
        refinedSound.termRenames

/-- Soundness for record-introduction strengthening.  The producer
threads `fieldResult`'s field projections through without destructuring,
so the soundness proof can apply the HEq congruence lemma directly using
the field projections of the result. -/
theorem partialStrengthenTypedRecordIntro_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {singleFieldType : Ty level sourceScope}
    {firstRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {firstField : Term sourceCtx singleFieldType firstRaw}
    {fieldResult : StrengtheningResult strengthening firstField}
    (fieldSound : StrengtheningSoundness fieldResult) :
    StrengtheningSoundness
      (partialStrengthenTypedRecordIntro fieldResult) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedRecordIntro,
      StrengtheningResult.renamedTarget] at fieldSound ⊢
  exact Term.recordIntro_HEq_congr fieldResult.typeRenames
    fieldResult.rawRenames fieldSound.termRenames

/-- Soundness for the success branch of record-projection strengthening.
Mirrors `partialStrengthenTypedRefineElimOfSuccess_sound`: the term-mode
OfSuccess body is what `dsimp` unfolds, while the tactic-mode wrapper
traversing `Option.casesOn` on the field-type pivot is left unsounded
by design. -/
theorem partialStrengthenTypedRecordProjOfSuccess_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {singleFieldType : Ty level sourceScope}
    {recordRaw : RawTerm sourceScope}
    {targetFieldType : Ty level targetScope}
    {targetRecordRaw : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {recordValue : Term sourceCtx (Ty.record singleFieldType) recordRaw}
    {targetRecordTerm :
      Term targetCtx (Ty.record targetFieldType) targetRecordRaw}
    {fieldSuccess :
      singleFieldType.partialStrengthen? strengthening.back =
        some targetFieldType}
    {recordRawStrengthens :
      recordRaw.partialStrengthen? strengthening.back =
        some targetRecordRaw}
    {recordRawRenames :
      recordRaw = targetRecordRaw.rename strengthening.forward}
    (recordSound :
      HEq recordValue
        (Term.rename strengthening.toTermRenaming targetRecordTerm)) :
    StrengtheningSoundness
      (partialStrengthenTypedRecordProjOfSuccess
        (recordValue := recordValue)
        targetRecordTerm fieldSuccess recordRawStrengthens
        recordRawRenames) := by
  refine ⟨?_⟩
  unfold StrengtheningResult.renamedTarget
  dsimp [partialStrengthenTypedRecordProjOfSuccess]
  have fieldRenames :
      singleFieldType = targetFieldType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename singleFieldType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetFieldType fieldSuccess
  exact Term.recordProj_HEq_congr fieldRenames recordRawRenames recordSound

/-- Soundness for the typed record-projection wrapper.

Mirrors `partialStrengthenTypedRecordProj`'s structure after the
App-pattern refactor: the wrapper takes the field-type strengthening
witness `fieldSuccess` as an explicit parameter (lifted from the
dispatcher's option-split), destructures the record's
`StrengtheningResult`, aligns the `Ty.record` shape via `rw` + `cases`
on the derived equation, and delegates to
`partialStrengthenTypedRecordProjOfSuccess`.  Soundness threads
`recordSound.termRenames` through the same case cascade and invokes
the leaf `_OfSuccess_sound`. -/
theorem partialStrengthenTypedRecordProj_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
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
    {recordResult : StrengtheningResult strengthening recordValue}
    (recordSound : StrengtheningSoundness recordResult) :
    StrengtheningSoundness
      (partialStrengthenTypedRecordProj fieldSuccess recordResult) := by
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
      exact partialStrengthenTypedRecordProjOfSuccess_sound
        (fieldSuccess := fieldSuccess)
        (recordRawStrengthens := rawStrengthens)
        (recordRawRenames := rawRenames)
        recordSound.termRenames

/-- Soundness for the success branch of codata-unfold strengthening.
Mirrors `partialStrengthenTypedAppOfSuccess_sound`: takes pre-decomposed
state/output strengthenings and rename equations, applies the codata-
unfold HEq congruence lemma after deriving the state/output type
renames from the strengthening's injectivity. -/
theorem partialStrengthenTypedCodataUnfoldOfSuccess_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
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
    {targetStateTerm : Term targetCtx targetStateType targetStateRaw}
    {targetTransitionTerm :
      Term targetCtx (Ty.arrow targetStateType targetOutputType)
        targetTransitionRaw}
    {stateTypeStrengthens :
      stateType.partialStrengthen? strengthening.back = some targetStateType}
    {outputTypeStrengthens :
      outputType.partialStrengthen? strengthening.back =
        some targetOutputType}
    {stateRawStrengthens :
      stateRaw.partialStrengthen? strengthening.back =
        some targetStateRaw}
    {transitionRawStrengthens :
      transitionRaw.partialStrengthen? strengthening.back =
        some targetTransitionRaw}
    {stateRawRenames :
      stateRaw = targetStateRaw.rename strengthening.forward}
    {transitionRawRenames :
      transitionRaw = targetTransitionRaw.rename strengthening.forward}
    (stateSound :
      HEq initialState
        (Term.rename strengthening.toTermRenaming targetStateTerm))
    (transitionSound :
      HEq transition
        (Term.rename strengthening.toTermRenaming targetTransitionTerm)) :
    StrengtheningSoundness
      (partialStrengthenTypedCodataUnfoldOfSuccess
        (initialState := initialState) (transition := transition)
        targetStateTerm targetTransitionTerm stateTypeStrengthens
        outputTypeStrengthens stateRawStrengthens transitionRawStrengthens
        stateRawRenames transitionRawRenames) := by
  refine ⟨?_⟩
  unfold StrengtheningResult.renamedTarget
  dsimp [partialStrengthenTypedCodataUnfoldOfSuccess]
  have stateRenames :
      stateType = targetStateType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename stateType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetStateType stateTypeStrengthens
  have outputRenames :
      outputType = targetOutputType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename outputType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetOutputType outputTypeStrengthens
  exact Term.codataUnfold_HEq_congr stateRenames outputRenames
    stateRawRenames transitionRawRenames stateSound transitionSound

/-- Soundness for the typed codata-unfold wrapper.

Mirrors `partialStrengthenTypedCodataUnfold`'s structure: destructures
both child `StrengtheningResult` records, aligns the transition's
`Ty.arrow` type via `rw` + `cases` on the transition-type
strengthening, then invokes
`partialStrengthenTypedCodataUnfoldOfSuccess_sound` at the leaf with
the explicit `outputTypeStrengthens` witness threaded through.  Pure
App-pattern: no internal `cases X : foo` option-split, only record
field rewrites. -/
theorem partialStrengthenTypedCodataUnfold_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
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
    {stateResult : StrengtheningResult strengthening initialState}
    {transitionResult : StrengtheningResult strengthening transition}
    (stateSound : StrengtheningSoundness stateResult)
    (transitionSound : StrengtheningSoundness transitionResult) :
    StrengtheningSoundness
      (partialStrengthenTypedCodataUnfold outputTypeStrengthens
        stateResult transitionResult) := by
  cases stateResult with
  | mk targetStateType targetStateRaw targetStateTerm stateTypeStrengthens
      stateRawStrengthens stateTypeRenames stateRawRenames =>
      cases transitionResult with
      | mk targetTransitionType targetTransitionRaw targetTransitionTerm
          transitionTypeStrengthens transitionRawStrengthens
          transitionTypeRenames transitionRawRenames =>
          have expectedTransitionTypeStrengthens :
              (Ty.arrow stateType outputType).partialStrengthen?
                  strengthening.back =
                some (Ty.arrow targetStateType targetOutputType) := by
            change
              Option.mapTwo
                (stateType.partialStrengthen? strengthening.back)
                (outputType.partialStrengthen? strengthening.back)
                Ty.arrow =
                  some (Ty.arrow targetStateType targetOutputType)
            rw [stateTypeStrengthens, outputTypeStrengthens]
            rfl
          rw [expectedTransitionTypeStrengthens]
            at transitionTypeStrengthens
          cases transitionTypeStrengthens
          exact partialStrengthenTypedCodataUnfoldOfSuccess_sound
            (stateTypeStrengthens := stateTypeStrengthens)
            (outputTypeStrengthens := outputTypeStrengthens)
            (stateRawStrengthens := stateRawStrengthens)
            (transitionRawStrengthens := transitionRawStrengthens)
            (stateRawRenames := stateRawRenames)
            (transitionRawRenames := transitionRawRenames)
            stateSound.termRenames transitionSound.termRenames

/-- Soundness for the success branch of codata-destruction strengthening.
Mirrors `partialStrengthenTypedRefineElimOfSuccess_sound`: the OfSuccess
body's record construction is what `dsimp` unfolds.  The state-type
strengthening witness is unused by the produced output type but stays
in the signature for symmetry with the wrapper's case cascade. -/
theorem partialStrengthenTypedCodataDestOfSuccess_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {stateType outputType : Ty level sourceScope}
    {targetStateType targetOutputType : Ty level targetScope}
    {codataRaw : RawTerm sourceScope}
    {targetCodataRaw : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {codataValue :
      Term sourceCtx (Ty.codata stateType outputType) codataRaw}
    {targetCodataTerm :
      Term targetCtx (Ty.codata targetStateType targetOutputType)
        targetCodataRaw}
    {stateSuccess :
      stateType.partialStrengthen? strengthening.back = some targetStateType}
    {outputSuccess :
      outputType.partialStrengthen? strengthening.back =
        some targetOutputType}
    {codataRawStrengthens :
      codataRaw.partialStrengthen? strengthening.back =
        some targetCodataRaw}
    {codataRawRenames :
      codataRaw = targetCodataRaw.rename strengthening.forward}
    (codataSound :
      HEq codataValue
        (Term.rename strengthening.toTermRenaming targetCodataTerm)) :
    StrengtheningSoundness
      (partialStrengthenTypedCodataDestOfSuccess
        (codataValue := codataValue)
        targetCodataTerm stateSuccess outputSuccess codataRawStrengthens
        codataRawRenames) := by
  refine ⟨?_⟩
  unfold StrengtheningResult.renamedTarget
  dsimp [partialStrengthenTypedCodataDestOfSuccess]
  have stateRenames :
      stateType = targetStateType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename stateType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetStateType stateSuccess
  have outputRenames :
      outputType = targetOutputType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename outputType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetOutputType outputSuccess
  exact Term.codataDest_HEq_congr stateRenames outputRenames
    codataRawRenames codataSound

/-- Soundness for the typed codata-destruction wrapper.

Mirrors `partialStrengthenTypedCodataDest`'s App-pattern shape: the
wrapper takes `stateSuccess` and `outputSuccess` as explicit
parameters (lifted from the dispatcher's two nested option-splits on
state and output type respectively).  The proof destructures the
codata value's `StrengtheningResult`, aligns the `Ty.codata` shape via
`rw` + `cases` on the derived equation, then delegates to
`partialStrengthenTypedCodataDestOfSuccess_sound`.  Same recipe as
Phase 39 RefineElim. -/
theorem partialStrengthenTypedCodataDest_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
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
    {codataResult : StrengtheningResult strengthening codataValue}
    (codataSound : StrengtheningSoundness codataResult) :
    StrengtheningSoundness
      (partialStrengthenTypedCodataDest stateSuccess outputSuccess
        codataResult) := by
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
      exact partialStrengthenTypedCodataDestOfSuccess_sound
        (stateSuccess := stateSuccess)
        (outputSuccess := outputSuccess)
        (codataRawStrengthens := codataRawStrengthens)
        (codataRawRenames := codataRawRenames)
        codataSound.termRenames

/-- Soundness for session-send strengthening.  The producer is direct
(no Option.casesOn discriminator wall — protocol pivot is pre-witnessed
by the `protocolStrengthens` hypothesis), so soundness mirrors the
producer's case structure with the same `change / rw / cases` chain
to unify the channel's session type with the target's protocol step. -/
theorem partialStrengthenTypedSessionSend_sound {mode : Mode} {level : Nat}
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
    {channelResult : StrengtheningResult strengthening channel}
    {payloadResult : StrengtheningResult strengthening payload}
    (channelSound : StrengtheningSoundness channelResult)
    (payloadSound : StrengtheningSoundness payloadResult) :
    StrengtheningSoundness
      (partialStrengthenTypedSessionSend protocolStrengthens channelResult
        payloadResult) := by
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
          refine ⟨?_⟩
          dsimp [partialStrengthenTypedSessionSend,
              StrengtheningResult.renamedTarget] at channelSound payloadSound ⊢
          have protocolRenames :
              protocolStep = targetProtocolStep.rename strengthening.forward :=
            RawTerm.partialStrengthen?_imp_rename protocolStep
              strengthening.forward strengthening.back strengthening.injectsBack
              targetProtocolStep protocolStrengthens
          exact Term.sessionSend_HEq_congr protocolRenames
            payloadTypeRenames channelRawRenames payloadRawRenames
            channelSound.termRenames payloadSound.termRenames

/-- Soundness for session-receive strengthening.  Mirrors the session-send
soundness pattern with one fewer payload component: the producer cases the
channel result and unifies the session type via `change / rw / cases` on
the channel's typeStrengthens witness. -/
theorem partialStrengthenTypedSessionRecv_sound {mode : Mode} {level : Nat}
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
    {channelResult : StrengtheningResult strengthening channel}
    (channelSound : StrengtheningSoundness channelResult) :
    StrengtheningSoundness
      (partialStrengthenTypedSessionRecv protocolStrengthens
        channelResult) := by
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
      refine ⟨?_⟩
      dsimp [partialStrengthenTypedSessionRecv,
          StrengtheningResult.renamedTarget] at channelSound ⊢
      have protocolRenames :
          protocolStep = targetProtocolStep.rename strengthening.forward :=
        RawTerm.partialStrengthen?_imp_rename protocolStep
          strengthening.forward strengthening.back strengthening.injectsBack
          targetProtocolStep protocolStrengthens
      exact Term.sessionRecv_HEq_congr protocolRenames channelRawRenames
        channelSound.termRenames

/-- Soundness for cumulativity-promotion strengthening.  The producer is
direct: the type-code's source type is `Ty.universe lowerLevel levelLeLow`
(closed in scope), so its partial-strengthen reduces definitionally to
`some (Ty.universe lowerLevel levelLeLow)` and `cases` unifies cleanly.
Only the code's raw rename equation is load-bearing. -/
theorem partialStrengthenTypedCumulUp_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {codeRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {typeCode :
      Term sourceCtx (Ty.universe lowerLevel levelLeLow) codeRaw}
    {codeResult : StrengtheningResult strengthening typeCode}
    (codeSound : StrengtheningSoundness codeResult) :
    StrengtheningSoundness
      (partialStrengthenTypedCumulUp lowerLevel higherLevel cumulMonotone
        levelLeLow levelLeHigh codeResult) := by
  cases codeResult with
  | mk targetCodeType targetCodeRaw targetCodeTerm codeTypeStrengthens
      codeRawStrengthens codeTypeRenames codeRawRenames =>
      cases codeTypeStrengthens
      refine ⟨?_⟩
      dsimp [partialStrengthenTypedCumulUp,
          StrengtheningResult.renamedTarget] at codeSound ⊢
      exact Term.cumulUp_HEq_congr codeRawRenames codeSound.termRenames

end Term

end LeanFX2
