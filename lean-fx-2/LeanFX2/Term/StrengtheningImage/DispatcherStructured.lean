import LeanFX2.Term.StrengtheningImage.Core
import LeanFX2.Term.StrengtheningImage.Reflexivity
import LeanFX2.Term.StrengtheningImage.HoTTElimSuccess
import LeanFX2.Term.StrengtheningImage.CubicalTransport
import LeanFX2.Term.StrengtheningImage.CubicalComposition
import LeanFX2.Term.StrengtheningImage.RefineRecordCodataSession
import LeanFX2.Term.StrengtheningImage.MatcherWrappers
import LeanFX2.Term.StrengtheningImage.HoTTAppWrappers


/-! # Term/StrengtheningImage/DispatcherStructured

Dispatcher-arm soundness for structured HoTT, cubical, codata, session, record, refinement, and cumulativity constructors.
-/

namespace LeanFX2

namespace Term

/-- Dispatcher soundness at the `Term.oeqFunext` arm.  Function-
extensionality intro: two type witnesses (domain + codomain) plus
two raw witnesses (leftFunctionRaw + rightFunctionRaw) plus one
flat-context value IH (pointwiseProof). -/
theorem partialStrengthenTyped?_atOeqFunext_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {domainType codomainType : Ty level sourceScope}
    {leftFunctionRaw rightFunctionRaw : RawTerm sourceScope}
    {pointwiseRaw : RawTerm sourceScope}
    {pointwiseProof :
      Term sourceCtx
        (oeqFunextPointwiseType domainType codomainType
          leftFunctionRaw rightFunctionRaw)
        pointwiseRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (pointwiseIH : ∀ pointwiseResult,
        partialStrengthenTyped? pointwiseProof strengthening =
            some pointwiseResult →
          StrengtheningSoundness pointwiseResult)
    (result : StrengtheningResult strengthening
      (Term.oeqFunext (domainType := domainType)
        (codomainType := codomainType)
        (leftFunctionRaw := leftFunctionRaw)
        (rightFunctionRaw := rightFunctionRaw)
        pointwiseProof))
    (success : partialStrengthenTyped?
        (Term.oeqFunext (domainType := domainType)
          (codomainType := codomainType)
          (leftFunctionRaw := leftFunctionRaw)
          (rightFunctionRaw := rightFunctionRaw)
          pointwiseProof) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetDomainType domainSuccess
    split at success
    · cases success
    · rename_i targetCodomainType codomainSuccess
      split at success
      · cases success
      · rename_i targetLeftFunctionRaw leftSuccess
        split at success
        · cases success
        · rename_i targetRightFunctionRaw rightSuccess
          split at success
          · cases success
          · rename_i pointwiseResult pointwiseRecurse
            cases success
            exact partialStrengthenTypedOeqFunext_sound
              domainType codomainType targetDomainType targetCodomainType
              leftFunctionRaw rightFunctionRaw targetLeftFunctionRaw
              targetRightFunctionRaw domainSuccess codomainSuccess
              leftSuccess rightSuccess
              (pointwiseIH pointwiseResult pointwiseRecurse)

/-- Dispatcher soundness at the `Term.idStrictRefl` arm.  Strict-mode
identity reflexivity: one type witness (carrier) + one raw witness,
no value IH, plus the `modeIsStrict` discipline witness. -/
theorem partialStrengthenTyped?_atIdStrictRefl_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {modeIsStrict : mode = Mode.strict}
    {carrier : Ty level sourceScope}
    {rawWitness : RawTerm sourceScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening
      (Term.idStrictRefl (context := sourceCtx)
        (carrier := carrier) modeIsStrict rawWitness))
    (success : partialStrengthenTyped?
        (Term.idStrictRefl (context := sourceCtx)
          (carrier := carrier) modeIsStrict rawWitness)
          strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetCarrier carrierSuccess
    split at success
    · cases success
    · rename_i targetWitness witnessSuccess
      cases success
      exact partialStrengthenTypedIdStrictRefl_sound modeIsStrict
        carrierSuccess witnessSuccess

/-- Dispatcher soundness at the `Term.idStrictRec` arm.  Strict-mode
J-eliminator: one type witness (carrier) + two raw witnesses
(leftEndpoint + rightEndpoint) + two flat-context value IHs
(baseCase + witness), plus `modeIsStrict`. -/
theorem partialStrengthenTyped?_atIdStrictRec_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {modeIsStrict : mode = Mode.strict}
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx (Ty.idStrict carrier leftEndpoint rightEndpoint)
        witnessRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (baseIH : ∀ baseResult,
        partialStrengthenTyped? baseCase strengthening =
            some baseResult →
          StrengtheningSoundness baseResult)
    (witnessIH : ∀ witnessResult,
        partialStrengthenTyped? witness strengthening =
            some witnessResult →
          StrengtheningSoundness witnessResult)
    (result : StrengtheningResult strengthening
      (Term.idStrictRec (motiveType := motiveType) modeIsStrict
        baseCase witness))
    (success : partialStrengthenTyped?
        (Term.idStrictRec (motiveType := motiveType) modeIsStrict
          baseCase witness) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetCarrier carrierSuccess
    split at success
    · cases success
    · rename_i targetLeftEndpoint leftSuccess
      split at success
      · cases success
      · rename_i targetRightEndpoint rightSuccess
        split at success
        · cases success
        · rename_i baseResult baseRecurse
          split at success
          · cases success
          · rename_i witnessResult witnessRecurse
            cases success
            exact partialStrengthenTypedIdStrictRec_sound modeIsStrict
              carrierSuccess leftSuccess rightSuccess
              (baseIH baseResult baseRecurse)
              (witnessIH witnessResult witnessRecurse)

/-- Dispatcher soundness at the `Term.pathApp` arm.  Cubical path
application: three type witnesses (carrierType + leftEndpoint +
rightEndpoint as Ty.path components) + two flat-context value IHs
(pathTerm + intervalTerm), plus `modeIsUnivalent`. -/
theorem partialStrengthenTyped?_atPathApp_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {modeIsUnivalent : mode = Mode.univalent}
    {carrierType : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {pathRaw intervalRaw : RawTerm sourceScope}
    {pathTerm :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint)
        pathRaw}
    {intervalTerm : Term sourceCtx Ty.interval intervalRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (pathIH : ∀ pathResult,
        partialStrengthenTyped? pathTerm strengthening =
            some pathResult →
          StrengtheningSoundness pathResult)
    (intervalIH : ∀ intervalResult,
        partialStrengthenTyped? intervalTerm strengthening =
            some intervalResult →
          StrengtheningSoundness intervalResult)
    (result : StrengtheningResult strengthening
      (Term.pathApp modeIsUnivalent pathTerm intervalTerm))
    (success : partialStrengthenTyped?
        (Term.pathApp modeIsUnivalent pathTerm intervalTerm)
          strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetCarrierType carrierSuccess
    split at success
    · cases success
    · rename_i targetLeftEndpoint leftSuccess
      split at success
      · cases success
      · rename_i targetRightEndpoint rightSuccess
        split at success
        · cases success
        · rename_i pathResult pathRecurse
          split at success
          · cases success
          · rename_i intervalResult intervalRecurse
            cases success
            exact partialStrengthenTypedPathApp_sound modeIsUnivalent
              carrierSuccess leftSuccess rightSuccess
              (pathIH pathResult pathRecurse)
              (intervalIH intervalResult intervalRecurse)

/-- Dispatcher soundness at the `Term.glueElim` arm.  Cubical glue
elimination: one type witness (baseType) + one raw witness
(boundaryWitness) + one flat-context value IH (gluedValue), plus
`modeIsUnivalent`. -/
theorem partialStrengthenTyped?_atGlueElim_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {modeIsUnivalent : mode = Mode.univalent}
    {baseType : Ty level sourceScope}
    {boundaryWitness gluedRaw : RawTerm sourceScope}
    {gluedValue :
      Term sourceCtx (Ty.glue baseType boundaryWitness) gluedRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (gluedIH : ∀ gluedResult,
        partialStrengthenTyped? gluedValue strengthening =
            some gluedResult →
          StrengtheningSoundness gluedResult)
    (result : StrengtheningResult strengthening
      (Term.glueElim modeIsUnivalent gluedValue))
    (success : partialStrengthenTyped?
        (Term.glueElim modeIsUnivalent gluedValue) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetBaseType baseSuccess
    split at success
    · cases success
    · rename_i targetBoundaryWitness boundarySuccess
      split at success
      · cases success
      · rename_i gluedResult gluedRecurse
        cases success
        exact partialStrengthenTypedGlueElim_sound modeIsUnivalent
          baseSuccess boundarySuccess (gluedIH gluedResult gluedRecurse)

/-- Dispatcher soundness at the `Term.codataUnfold` arm.  Codata
introduction: one raw witness on `outputType` (state type rides
through the transition arrow's type strengthening) + two
flat-context value IHs (`initialState` + `transition`). -/
theorem partialStrengthenTyped?_atCodataUnfold_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {stateType outputType : Ty level sourceScope}
    {stateRaw transitionRaw : RawTerm sourceScope}
    {initialState : Term sourceCtx stateType stateRaw}
    {transition :
      Term sourceCtx (Ty.arrow stateType outputType) transitionRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (stateIH : ∀ stateResult,
        partialStrengthenTyped? initialState strengthening =
            some stateResult →
          StrengtheningSoundness stateResult)
    (transitionIH : ∀ transitionResult,
        partialStrengthenTyped? transition strengthening =
            some transitionResult →
          StrengtheningSoundness transitionResult)
    (result : StrengtheningResult strengthening
      (Term.codataUnfold initialState transition))
    (success : partialStrengthenTyped?
        (Term.codataUnfold initialState transition) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetOutputType outputSuccess
    split at success
    · cases success
    · rename_i stateResult stateRecurse
      split at success
      · cases success
      · rename_i transitionResult transitionRecurse
        cases success
        exact partialStrengthenTypedCodataUnfold_sound outputSuccess
          (stateSound := stateIH stateResult stateRecurse)
          (transitionSound := transitionIH transitionResult transitionRecurse)

/-- Dispatcher soundness at the `Term.codataDest` arm.  Codata
destruction: two type witnesses (`stateType` + `outputType`, both at
`strengthening.back`) + one flat-context value IH on `codataValue`. -/
theorem partialStrengthenTyped?_atCodataDest_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {stateType outputType : Ty level sourceScope}
    {codataRaw : RawTerm sourceScope}
    {codataValue :
      Term sourceCtx (Ty.codata stateType outputType) codataRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (codataIH : ∀ codataResult,
        partialStrengthenTyped? codataValue strengthening =
            some codataResult →
          StrengtheningSoundness codataResult)
    (result : StrengtheningResult strengthening
      (Term.codataDest codataValue))
    (success : partialStrengthenTyped?
        (Term.codataDest codataValue) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetStateType stateSuccess
    split at success
    · cases success
    · rename_i targetOutputType outputSuccess
      split at success
      · cases success
      · rename_i codataResult codataRecurse
        cases success
        exact partialStrengthenTypedCodataDest_sound stateSuccess
          outputSuccess
          (codataSound := codataIH codataResult codataRecurse)

/-- Dispatcher soundness at the `Term.sessionSend` arm.  Session-send:
one raw witness on the protocol step (lifted to
`strengthening.back` since the protocol step lives at flat scope) +
two flat-context value IHs (`channel` + `payload`). -/
theorem partialStrengthenTyped?_atSessionSend_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {protocolStep : RawTerm sourceScope}
    {payloadType : Ty level sourceScope}
    {channelRaw payloadRaw : RawTerm sourceScope}
    {channel : Term sourceCtx (Ty.session protocolStep) channelRaw}
    {payload : Term sourceCtx payloadType payloadRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (channelIH : ∀ channelResult,
        partialStrengthenTyped? channel strengthening =
            some channelResult →
          StrengtheningSoundness channelResult)
    (payloadIH : ∀ payloadResult,
        partialStrengthenTyped? payload strengthening =
            some payloadResult →
          StrengtheningSoundness payloadResult)
    (result : StrengtheningResult strengthening
      (Term.sessionSend protocolStep channel payload))
    (success : partialStrengthenTyped?
        (Term.sessionSend protocolStep channel payload) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetProtocolStep protocolSuccess
    split at success
    · cases success
    · rename_i channelResult channelRecurse
      split at success
      · cases success
      · rename_i payloadResult payloadRecurse
        cases success
        exact partialStrengthenTypedSessionSend_sound protocolSuccess
          (channelSound := channelIH channelResult channelRecurse)
          (payloadSound := payloadIH payloadResult payloadRecurse)

/-- Dispatcher soundness at the `Term.sessionRecv` arm.  Session-recv:
one raw witness on the protocol step + one flat-context value IH on
`channel`. -/
theorem partialStrengthenTyped?_atSessionRecv_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {protocolStep : RawTerm sourceScope}
    {channelRaw : RawTerm sourceScope}
    {channel : Term sourceCtx (Ty.session protocolStep) channelRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (channelIH : ∀ channelResult,
        partialStrengthenTyped? channel strengthening =
            some channelResult →
          StrengtheningSoundness channelResult)
    (result : StrengtheningResult strengthening
      (Term.sessionRecv channel))
    (success : partialStrengthenTyped?
        (Term.sessionRecv channel) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetProtocolStep protocolSuccess
    split at success
    · cases success
    · rename_i channelResult channelRecurse
      cases success
      exact partialStrengthenTypedSessionRecv_sound protocolSuccess
        (channelSound := channelIH channelResult channelRecurse)

/-- Dispatcher soundness at the `Term.equivReflId` arm.  Closed-leaf
equivalence-reflexivity-at-id: one type witness on `carrier`, NO
value IH.  The wrapper takes `carrier` and `targetCarrier` as
positional explicit arguments; the dispatcher leaf grabs the latter
from `split`'s rename. -/
theorem partialStrengthenTyped?_atEquivReflId_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrier : Ty level sourceScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening
      (Term.equivReflId (context := sourceCtx) (carrier := carrier)))
    (success : partialStrengthenTyped?
        (Term.equivReflId (context := sourceCtx) (carrier := carrier))
          strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetCarrier carrierSuccess
    cases success
    exact partialStrengthenTypedEquivReflId_sound carrier targetCarrier
      carrierSuccess

/-- Dispatcher soundness at the `Term.recordIntro` arm.  Single-field
record introduction: no raw or type witnesses (`Ty.record` is built
from the strengthened field type via `congrArg`), one flat-context
value IH (`firstField`). -/
theorem partialStrengthenTyped?_atRecordIntro_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {singleFieldType : Ty level sourceScope}
    {firstRaw : RawTerm sourceScope}
    {firstField : Term sourceCtx singleFieldType firstRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (fieldIH : ∀ fieldResult,
        partialStrengthenTyped? firstField strengthening =
            some fieldResult →
          StrengtheningSoundness fieldResult)
    (result : StrengtheningResult strengthening
      (Term.recordIntro (firstField := firstField)))
    (success : partialStrengthenTyped?
        (Term.recordIntro (firstField := firstField)) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i fieldResult fieldRecurse
    cases success
    exact partialStrengthenTypedRecordIntro_sound
      (fieldSound := fieldIH fieldResult fieldRecurse)

/-- Dispatcher soundness at the `Term.recordProj` arm.  Record
projection: one type witness (`singleFieldType` at
`strengthening.back`) + one flat-context value IH (`recordValue`). -/
theorem partialStrengthenTyped?_atRecordProj_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {singleFieldType : Ty level sourceScope}
    {recordRaw : RawTerm sourceScope}
    {recordValue : Term sourceCtx (Ty.record singleFieldType) recordRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (recordIH : ∀ recordResult,
        partialStrengthenTyped? recordValue strengthening =
            some recordResult →
          StrengtheningSoundness recordResult)
    (result : StrengtheningResult strengthening
      (Term.recordProj (recordValue := recordValue)))
    (success : partialStrengthenTyped?
        (Term.recordProj (recordValue := recordValue)) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetFieldType fieldSuccess
    split at success
    · cases success
    · rename_i recordResult recordRecurse
      cases success
      exact partialStrengthenTypedRecordProj_sound fieldSuccess
        (recordSound := recordIH recordResult recordRecurse)

/-- Dispatcher soundness at the `Term.refineIntro` arm.  Refinement
introduction: one raw witness on the predicate (lifted to
`strengthening.back.lift` since the predicate binds the refined
variable) + two flat-context value IHs (`baseValue` carrying the
underlying datum + `predicateProof` discharging the refinement). -/
theorem partialStrengthenTyped?_atRefineIntro_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {baseType : Ty level sourceScope}
    {predicate : RawTerm (sourceScope + 1)}
    {valueRaw proofRaw : RawTerm sourceScope}
    {baseValue : Term sourceCtx baseType valueRaw}
    {predicateProof : Term sourceCtx Ty.unit proofRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (baseIH : ∀ baseResult,
        partialStrengthenTyped? baseValue strengthening =
            some baseResult →
          StrengtheningSoundness baseResult)
    (proofIH : ∀ proofResult,
        partialStrengthenTyped? predicateProof strengthening =
            some proofResult →
          StrengtheningSoundness proofResult)
    (result : StrengtheningResult strengthening
      (Term.refineIntro predicate baseValue predicateProof))
    (success : partialStrengthenTyped?
        (Term.refineIntro predicate baseValue predicateProof)
          strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetPredicate predicateSuccess
    split at success
    · cases success
    · rename_i baseResult baseRecurse
      split at success
      · cases success
      · rename_i proofResult proofRecurse
        cases success
        exact partialStrengthenTypedRefineIntro_sound predicateSuccess
          (baseSound := baseIH baseResult baseRecurse)
          (proofSound := proofIH proofResult proofRecurse)

/-- Dispatcher soundness at the `Term.refineElim` arm.  Refinement
elimination: one type witness (`baseType` at `strengthening.back`) +
one raw witness on the predicate (lifted) + one flat-context value
IH (`refinedValue`). -/
theorem partialStrengthenTyped?_atRefineElim_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {baseType : Ty level sourceScope}
    {predicate : RawTerm (sourceScope + 1)}
    {refinedRaw : RawTerm sourceScope}
    {refinedValue :
      Term sourceCtx (Ty.refine baseType predicate) refinedRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (refinedIH : ∀ refinedResult,
        partialStrengthenTyped? refinedValue strengthening =
            some refinedResult →
          StrengtheningSoundness refinedResult)
    (result : StrengtheningResult strengthening
      (Term.refineElim refinedValue))
    (success : partialStrengthenTyped?
        (Term.refineElim refinedValue) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetBaseType baseSuccess
    split at success
    · cases success
    · rename_i targetPredicate predicateSuccess
      split at success
      · cases success
      · rename_i refinedResult refinedRecurse
        cases success
        exact partialStrengthenTypedRefineElim_sound baseSuccess
          predicateSuccess
          (refinedSound := refinedIH refinedResult refinedRecurse)

/-- Dispatcher soundness at the `Term.cumulUp` arm.  Universe-level
cumulation: no raw or type witnesses (all level data
`lowerLevel`/`higherLevel`/`cumulMonotone`/`levelLeLow`/`levelLeHigh`
forwards through as positional data into the wrapper), one
flat-context value IH (`typeCode`). -/
theorem partialStrengthenTyped?_atCumulUp_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {codeRaw : RawTerm sourceScope}
    {typeCode :
      Term sourceCtx (Ty.universe lowerLevel levelLeLow) codeRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (codeIH : ∀ codeResult,
        partialStrengthenTyped? typeCode strengthening =
            some codeResult →
          StrengtheningSoundness codeResult)
    (result : StrengtheningResult strengthening
      (Term.cumulUp lowerLevel higherLevel cumulMonotone levelLeLow
        levelLeHigh typeCode))
    (success : partialStrengthenTyped?
        (Term.cumulUp lowerLevel higherLevel cumulMonotone levelLeLow
          levelLeHigh typeCode) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i codeResult codeRecurse
    cases success
    exact partialStrengthenTypedCumulUp_sound lowerLevel higherLevel
      cumulMonotone levelLeLow levelLeHigh
      (codeSound := codeIH codeResult codeRecurse)

/-- Dispatcher soundness at the `Term.eitherMatch` arm.  ι-eliminator
with three type witnesses (leftType + rightType + motiveType, all at
`strengthening.back`) plus three flat-context value IHs
(scrutinee + leftBranch + rightBranch). -/
theorem partialStrengthenTyped?_atEitherMatch_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {leftType rightType motiveType : Ty level sourceScope}
    {scrutineeRaw leftRaw rightRaw : RawTerm sourceScope}
    {scrutinee :
      Term sourceCtx (Ty.eitherType leftType rightType) scrutineeRaw}
    {leftBranch : Term sourceCtx (Ty.arrow leftType motiveType) leftRaw}
    {rightBranch :
      Term sourceCtx (Ty.arrow rightType motiveType) rightRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (scrutineeIH : ∀ scrutineeResult,
        partialStrengthenTyped? scrutinee strengthening =
            some scrutineeResult →
          StrengtheningSoundness scrutineeResult)
    (leftIH : ∀ leftResult,
        partialStrengthenTyped? leftBranch strengthening =
            some leftResult →
          StrengtheningSoundness leftResult)
    (rightIH : ∀ rightResult,
        partialStrengthenTyped? rightBranch strengthening =
            some rightResult →
          StrengtheningSoundness rightResult)
    (result : StrengtheningResult strengthening
      (Term.eitherMatch (motiveType := motiveType) scrutinee leftBranch
        rightBranch))
    (success : partialStrengthenTyped?
        (Term.eitherMatch (motiveType := motiveType) scrutinee leftBranch
          rightBranch) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetLeftType leftSuccess
    split at success
    · cases success
    · rename_i targetRightType rightSuccess
      split at success
      · cases success
      · rename_i targetMotiveType motiveSuccess
        split at success
        · cases success
        · rename_i scrutineeResult scrutineeRecurse
          split at success
          · cases success
          · rename_i leftResult leftRecurse
            split at success
            · cases success
            · rename_i rightResult rightRecurse
              cases success
              exact partialStrengthenTypedEitherMatch_sound
                leftSuccess rightSuccess motiveSuccess
                (scrutineeIH scrutineeResult scrutineeRecurse)
                (leftIH leftResult leftRecurse)
                (rightIH rightResult rightRecurse)

end Term

end LeanFX2
