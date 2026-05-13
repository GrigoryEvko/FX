import LeanFX2.Tools.StrictHarness.Common
import LeanFX2.Tools.StrictHarness.Census.ModeDiscipline
import LeanFX2.Tools.StrictHarness.Census.SemanticSignature

/-! # LeanFX2.Tools.StrictHarness.Census.RichSchemaLinkage

Rich schema and linkage debt gates for type and term constructors:

* `Ty` constructors with raw identity/path endpoints lacking typed evidence
* `Ty` constructors with unstructured (raw/Nat) schema payloads
* `Term.transp` with unlinked source/target universe endpoints
* `Term.glue*` lacking BoundaryCofib/equiv schema
* `Term.effectPerform` lacking EffectRow membership
* `Term.session{Send,Recv}` lacking SessionProtocol schema
* `Term.hcomp` lacking Kan boundary evidence

## Root status

Layer T strict-harness audit gate. -/

namespace LeanFX2.Tools

open Lean Elab Command

/-! ## Rich schema and linkage debt gates -/

/-- Whether a binder name contains a specific substring. -/
partial def hasBinderContainingSegment
    (wantedSegment : String) (constructorType : Expr) :
    Bool :=
  match constructorType with
  | .forallE binderName _ bodyType _ =>
      (Name.lastSegmentString binderName).contains wantedSegment ||
        hasBinderContainingSegment wantedSegment bodyType
  | _ => false

/-- `Ty` ctors whose identity/path endpoints are still raw terms instead of
typed endpoint evidence. -/
def isTyRawEndpointConstructorName (constructorName : Name) : Bool :=
  let suffix := Name.lastSegmentString constructorName
  suffix == "id" ||
    suffix == "path" ||
    suffix == "oeq" ||
    suffix == "idStrict"

/-- Whether the constructor already appears to carry typed endpoint evidence. -/
def hasTypedEndpointEvidence (constructorType : Expr) : Bool :=
  hasBinderContainingSegment "EndpointTerm" constructorType ||
    hasBinderContainingSegment "endpointTerm" constructorType ||
    hasBinderContainingSegment "EndpointWitness" constructorType ||
    hasBinderContainingSegment "endpointWitness" constructorType

/-- Report raw endpoint debt for one `Ty` constructor. -/
def tyRawEndpointDebtRecord?
    (environment : Environment) (constructorName : Name) :
    Option SignatureDebtRecord :=
  if !isTyRawEndpointConstructorName constructorName then
    none
  else
    match environment.find? constructorName with
    | some (.ctorInfo constructorInfo) =>
        let hasRawEndpoints :=
          hasBinderWithLastSegment "leftEndpoint" constructorInfo.type &&
            hasBinderWithLastSegment "rightEndpoint" constructorInfo.type &&
            doesExprMentionConst `LeanFX2.RawTerm constructorInfo.type
        if hasRawEndpoints && !hasTypedEndpointEvidence constructorInfo.type then
          some {
            constructorName := constructorName
            detail := "type constructor has raw endpoints without typed endpoint evidence"
          }
        else
          none
    | _ => none

/-- Collect raw endpoint debt records for a type inductive. -/
def tyRawEndpointDebtRecordsForInductive
    (environment : Environment) (inductiveName : Name) :
    Array SignatureDebtRecord :=
  let constructorNames := getInductiveConstructorNames environment inductiveName
  constructorNames.foldl
    (init := (#[] : Array SignatureDebtRecord))
    (fun records constructorName =>
      match tyRawEndpointDebtRecord? environment constructorName with
      | some record => records.push record
      | none => records)

/-- Build-failing budget gate for raw endpoint type constructors. -/
elab "#assert_ty_raw_endpoint_budget " inductiveSyntax:ident
    rawEndpointBudgetSyntax:num : command => do
  let environment ← getEnv
  let inductiveName := inductiveSyntax.getId
  let rawEndpointBudget := rawEndpointBudgetSyntax.getNat
  let records := tyRawEndpointDebtRecordsForInductive environment inductiveName
  if records.size <= rawEndpointBudget then
    logInfo
      (s!"Ty raw endpoint budget ok: {inductiveName} " ++
      s!"({records.size}/{rawEndpointBudget} raw endpoint ctors)")
  else
    let perCtorLines := records.toList.map fun record =>
      s!"  - {record.constructorName}: {record.detail}"
    let header :=
      s!"Ty raw endpoint budget FAILED for {inductiveName}: " ++
      s!"{records.size} raw endpoint ctors exceed budget {rawEndpointBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perCtorLines)

/-- Whether a Ty constructor has the richer schema object expected by its
surface meaning. -/
def hasExpectedTySchemaPayload
    (constructorName : Name) (constructorType : Expr) :
    Bool :=
  let suffix := Name.lastSegmentString constructorName
  if suffix == "modal" then
    doesExprMentionConst `LeanFX2.Modality constructorType
  else if suffix == "glue" then
    doesExprMentionConst `LeanFX2.BoundaryCofib constructorType &&
      doesExprMentionConst `LeanFX2.Ty.equiv constructorType
  else if suffix == "refine" then
    hasBinderContainingSegment "predicateTerm" constructorType ||
      hasBinderContainingSegment "predicateWitness" constructorType
  else if suffix == "session" then
    doesExprMentionConst `LeanFX2.SessionProtocol constructorType
  else if suffix == "effect" then
    doesExprMentionConst `LeanFX2.Effects.EffectRow constructorType
  else
    true

/-- Ty constructors whose semantics currently travel through raw/Nat tags. -/
def isTyUnstructuredSchemaConstructorName (constructorName : Name) : Bool :=
  let suffix := Name.lastSegmentString constructorName
  suffix == "modal" ||
    suffix == "glue" ||
    suffix == "refine" ||
    suffix == "session" ||
    suffix == "effect"

/-- Report unstructured schema payload debt for one `Ty` constructor. -/
def tyUnstructuredSchemaDebtRecord?
    (environment : Environment) (constructorName : Name) :
    Option SignatureDebtRecord :=
  if !isTyUnstructuredSchemaConstructorName constructorName then
    none
  else
    match environment.find? constructorName with
    | some (.ctorInfo constructorInfo) =>
        if hasExpectedTySchemaPayload constructorName constructorInfo.type then
          none
        else
          some {
            constructorName := constructorName
            detail := "type constructor uses raw/Nat schema payload instead of rich schema object"
          }
    | _ => none

/-- Collect unstructured schema payload debt records for a type inductive. -/
def tyUnstructuredSchemaDebtRecordsForInductive
    (environment : Environment) (inductiveName : Name) :
    Array SignatureDebtRecord :=
  let constructorNames := getInductiveConstructorNames environment inductiveName
  constructorNames.foldl
    (init := (#[] : Array SignatureDebtRecord))
    (fun records constructorName =>
      match tyUnstructuredSchemaDebtRecord? environment constructorName with
      | some record => records.push record
      | none => records)

/-- Build-failing budget gate for unstructured Ty schema payloads. -/
elab "#assert_ty_unstructured_schema_budget " inductiveSyntax:ident
    schemaBudgetSyntax:num : command => do
  let environment ← getEnv
  let inductiveName := inductiveSyntax.getId
  let schemaBudget := schemaBudgetSyntax.getNat
  let records := tyUnstructuredSchemaDebtRecordsForInductive environment inductiveName
  if records.size <= schemaBudget then
    logInfo
      (s!"Ty unstructured schema budget ok: {inductiveName} " ++
      s!"({records.size}/{schemaBudget} raw/Nat schema ctors)")
  else
    let perCtorLines := records.toList.map fun record =>
      s!"  - {record.constructorName}: {record.detail}"
    let header :=
      s!"Ty unstructured schema budget FAILED for {inductiveName}: " ++
      s!"{records.size} schema debts exceed budget {schemaBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perCtorLines)

/-- Report cubical transport endpoint-linkage debt for `Term.transp`. -/
def transportLinkageDebtRecord?
    (environment : Environment) (constructorName : Name) :
    Option SignatureDebtRecord :=
  if Name.lastSegmentString constructorName != "transp" then
    none
  else
    match environment.find? constructorName with
    | some (.ctorInfo constructorInfo) =>
        let hasSeparateRawCodes :=
          hasBinderWithLastSegment "sourceTypeRaw" constructorInfo.type &&
            hasBinderWithLastSegment "targetTypeRaw" constructorInfo.type
        let hasLinkageEvidence :=
          hasBinderContainingSegment "sourceTypeLink" constructorInfo.type ||
            hasBinderContainingSegment "targetTypeLink" constructorInfo.type ||
            hasBinderContainingSegment "decodedSource" constructorInfo.type ||
            hasBinderContainingSegment "decodedTarget" constructorInfo.type
        if hasSeparateRawCodes && !hasLinkageEvidence then
          some {
            constructorName := constructorName
            detail := "transport has raw universe endpoints without source/target linkage evidence"
          }
        else
          none
    | _ => none

/-- Collect transport endpoint-linkage debt records for an inductive. -/
def transportLinkageDebtRecordsForInductive
    (environment : Environment) (inductiveName : Name) :
    Array SignatureDebtRecord :=
  let constructorNames := getInductiveConstructorNames environment inductiveName
  constructorNames.foldl
    (init := (#[] : Array SignatureDebtRecord))
    (fun records constructorName =>
      match transportLinkageDebtRecord? environment constructorName with
      | some record => records.push record
      | none => records)

/-- Build-failing budget gate for cubical transport endpoint linkage debt. -/
elab "#assert_transport_linkage_budget " inductiveSyntax:ident
    transportLinkageBudgetSyntax:num : command => do
  let environment ← getEnv
  let inductiveName := inductiveSyntax.getId
  let transportLinkageBudget := transportLinkageBudgetSyntax.getNat
  let records := transportLinkageDebtRecordsForInductive environment inductiveName
  if records.size <= transportLinkageBudget then
    logInfo
      (s!"transport linkage budget ok: {inductiveName} " ++
      s!"({records.size}/{transportLinkageBudget} unlinked transport ctors)")
  else
    let perCtorLines := records.toList.map fun record =>
      s!"  - {record.constructorName}: {record.detail}"
    let header :=
      s!"transport linkage budget FAILED for {inductiveName}: " ++
      s!"{records.size} transport linkage debts exceed budget " ++
      s!"{transportLinkageBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perCtorLines)

/-- Glue-related Term constructors that should mention boundary cofibrations and
equivalence data when they stop being schematic. -/
def isGlueSchemaConstructorName (constructorName : Name) : Bool :=
  let suffix := Name.lastSegmentString constructorName
  suffix == "glueIntro" || suffix == "glueElim"

/-- Report Glue boundary/equivalence schema debt for one Term constructor. -/
def glueSchemaDebtRecord?
    (environment : Environment) (constructorName : Name) :
    Option SignatureDebtRecord :=
  if !isGlueSchemaConstructorName constructorName then
    none
  else
    match environment.find? constructorName with
    | some (.ctorInfo constructorInfo) =>
        let hasBoundarySchema :=
          doesExprMentionConst `LeanFX2.BoundaryCofib constructorInfo.type
        let hasEquivSchema :=
          doesExprMentionConst `LeanFX2.Ty.equiv constructorInfo.type ||
            doesExprMentionConst `LeanFX2.IsEquiv constructorInfo.type
        if hasBoundarySchema && hasEquivSchema then
          none
        else
          some {
            constructorName := constructorName
            detail := "Glue constructor lacks BoundaryCofib/equivalence schema evidence"
          }
    | _ => none

/-- Collect Glue boundary/equivalence schema debt records for an inductive. -/
def glueSchemaDebtRecordsForInductive
    (environment : Environment) (inductiveName : Name) :
    Array SignatureDebtRecord :=
  let constructorNames := getInductiveConstructorNames environment inductiveName
  constructorNames.foldl
    (init := (#[] : Array SignatureDebtRecord))
    (fun records constructorName =>
      match glueSchemaDebtRecord? environment constructorName with
      | some record => records.push record
      | none => records)

/-- Build-failing budget gate for schematic Glue constructors. -/
elab "#assert_glue_schema_budget " inductiveSyntax:ident
    glueSchemaBudgetSyntax:num : command => do
  let environment ← getEnv
  let inductiveName := inductiveSyntax.getId
  let glueSchemaBudget := glueSchemaBudgetSyntax.getNat
  let records := glueSchemaDebtRecordsForInductive environment inductiveName
  if records.size <= glueSchemaBudget then
    logInfo
      (s!"Glue schema budget ok: {inductiveName} " ++
      s!"({records.size}/{glueSchemaBudget} schematic Glue ctors)")
  else
    let perCtorLines := records.toList.map fun record =>
      s!"  - {record.constructorName}: {record.detail}"
    let header :=
      s!"Glue schema budget FAILED for {inductiveName}: " ++
      s!"{records.size} Glue schema debts exceed budget {glueSchemaBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perCtorLines)

/-- Term constructors that should mention `EffectRow` instead of raw/unit tags. -/
def isEffectSchemaConstructorName (constructorName : Name) : Bool :=
  Name.lastSegmentString constructorName == "effectPerform"

/-- Report effect-row schema debt for one Term constructor. -/
def effectSchemaDebtRecord?
    (environment : Environment) (constructorName : Name) :
    Option SignatureDebtRecord :=
  if !isEffectSchemaConstructorName constructorName then
    none
  else
    match environment.find? constructorName with
    | some (.ctorInfo constructorInfo) =>
        if doesExprMentionConst `LeanFX2.Effects.EffectRow constructorInfo.type then
          none
        else
          some {
            constructorName := constructorName
            detail := "effect constructor lacks EffectRow membership evidence"
          }
    | _ => none

/-- Collect effect-row schema debt records for an inductive. -/
def effectSchemaDebtRecordsForInductive
    (environment : Environment) (inductiveName : Name) :
    Array SignatureDebtRecord :=
  let constructorNames := getInductiveConstructorNames environment inductiveName
  constructorNames.foldl
    (init := (#[] : Array SignatureDebtRecord))
    (fun records constructorName =>
      match effectSchemaDebtRecord? environment constructorName with
      | some record => records.push record
      | none => records)

/-- Build-failing budget gate for effect-row schema debt. -/
elab "#assert_effect_schema_budget " inductiveSyntax:ident
    effectSchemaBudgetSyntax:num : command => do
  let environment ← getEnv
  let inductiveName := inductiveSyntax.getId
  let effectSchemaBudget := effectSchemaBudgetSyntax.getNat
  let records := effectSchemaDebtRecordsForInductive environment inductiveName
  if records.size <= effectSchemaBudget then
    logInfo
      (s!"effect schema budget ok: {inductiveName} " ++
      s!"({records.size}/{effectSchemaBudget} effect ctors lack row evidence)")
  else
    let perCtorLines := records.toList.map fun record =>
      s!"  - {record.constructorName}: {record.detail}"
    let header :=
      s!"effect schema budget FAILED for {inductiveName}: " ++
      s!"{records.size} effect schema debts exceed budget {effectSchemaBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perCtorLines)

/-- Term constructors that should mention `SessionProtocol` at the core
signature once sessions stop being raw protocol tags. -/
def isSessionSchemaConstructorName (constructorName : Name) : Bool :=
  let suffix := Name.lastSegmentString constructorName
  suffix == "sessionSend" || suffix == "sessionRecv"

/-- Report session schema debt for one Term constructor. -/
def sessionSchemaDebtRecord?
    (environment : Environment) (constructorName : Name) :
    Option SignatureDebtRecord :=
  if !isSessionSchemaConstructorName constructorName then
    none
  else
    match environment.find? constructorName with
    | some (.ctorInfo constructorInfo) =>
        if doesExprMentionConst `LeanFX2.SessionProtocol constructorInfo.type then
          none
        else
          some {
            constructorName := constructorName
            detail := "session constructor lacks SessionProtocol schema evidence"
          }
    | _ => none

/-- Collect session schema debt records for an inductive. -/
def sessionSchemaDebtRecordsForInductive
    (environment : Environment) (inductiveName : Name) :
    Array SignatureDebtRecord :=
  let constructorNames := getInductiveConstructorNames environment inductiveName
  constructorNames.foldl
    (init := (#[] : Array SignatureDebtRecord))
    (fun records constructorName =>
      match sessionSchemaDebtRecord? environment constructorName with
      | some record => records.push record
      | none => records)

/-- Build-failing budget gate for session protocol schema debt. -/
elab "#assert_session_schema_budget " inductiveSyntax:ident
    sessionSchemaBudgetSyntax:num : command => do
  let environment ← getEnv
  let inductiveName := inductiveSyntax.getId
  let sessionSchemaBudget := sessionSchemaBudgetSyntax.getNat
  let records := sessionSchemaDebtRecordsForInductive environment inductiveName
  if records.size <= sessionSchemaBudget then
    logInfo
      (s!"session schema budget ok: {inductiveName} " ++
      s!"({records.size}/{sessionSchemaBudget} session ctors lack protocol schema)")
  else
    let perCtorLines := records.toList.map fun record =>
      s!"  - {record.constructorName}: {record.detail}"
    let header :=
      s!"session schema budget FAILED for {inductiveName}: " ++
      s!"{records.size} session schema debts exceed budget {sessionSchemaBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perCtorLines)

/-- Report homogeneous-composition Kan-boundary debt for `Term.hcomp`. -/
def hcompKanDebtRecord?
    (environment : Environment) (constructorName : Name) :
    Option SignatureDebtRecord :=
  if Name.lastSegmentString constructorName != "hcomp" then
    none
  else
    match environment.find? constructorName with
    | some (.ctorInfo constructorInfo) =>
        let hasKanBoundaryEvidence :=
          doesExprMentionConst `LeanFX2.BoundaryCofib constructorInfo.type ||
            hasBinderContainingSegment "boundary" constructorInfo.type ||
            hasBinderContainingSegment "kan" constructorInfo.type ||
            hasBinderContainingSegment "Kan" constructorInfo.type
        if hasKanBoundaryEvidence then
          none
        else
          some {
            constructorName := constructorName
            detail := "hcomp lacks Kan boundary/filler evidence"
          }
    | _ => none

/-- Collect hcomp Kan-boundary debt records for an inductive. -/
def hcompKanDebtRecordsForInductive
    (environment : Environment) (inductiveName : Name) :
    Array SignatureDebtRecord :=
  let constructorNames := getInductiveConstructorNames environment inductiveName
  constructorNames.foldl
    (init := (#[] : Array SignatureDebtRecord))
    (fun records constructorName =>
      match hcompKanDebtRecord? environment constructorName with
      | some record => records.push record
      | none => records)

/-- Build-failing budget gate for `hcomp` without Kan boundary evidence. -/
elab "#assert_hcomp_kan_budget " inductiveSyntax:ident
    hcompKanBudgetSyntax:num : command => do
  let environment ← getEnv
  let inductiveName := inductiveSyntax.getId
  let hcompKanBudget := hcompKanBudgetSyntax.getNat
  let records := hcompKanDebtRecordsForInductive environment inductiveName
  if records.size <= hcompKanBudget then
    logInfo
      (s!"hcomp Kan budget ok: {inductiveName} " ++
      s!"({records.size}/{hcompKanBudget} hcomp ctors lack Kan evidence)")
  else
    let perCtorLines := records.toList.map fun record =>
      s!"  - {record.constructorName}: {record.detail}"
    let header :=
      s!"hcomp Kan budget FAILED for {inductiveName}: " ++
      s!"{records.size} hcomp Kan debts exceed budget {hcompKanBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perCtorLines)

end LeanFX2.Tools
