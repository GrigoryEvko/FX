import LeanFX2.Tools.StrictHarness.Common

/-! # LeanFX2.Tools.StrictHarness.Census.SchematicPayload

Constructor-census budget gate for explicit schematic payload
parameters.  A constructor "carries schematic payload" when it accepts
an explicit `RawTerm` or `Nat` parameter — typically a sign that
untyped syntax or an unstructured tag escaped a richer schema.

## Root status

Layer T strict-harness audit gate. -/

namespace LeanFX2.Tools

open Lean Elab Command

/-! ## Schematic-payload budget check -/

/-- Counts of explicit schematic payload types in constructor signatures. -/
structure SchematicPayloadCounts where
  rawTermPayloadCount : Nat := 0
  natPayloadCount : Nat := 0
  deriving Inhabited, Repr

namespace SchematicPayloadCounts

/-- Pointwise addition for schematic-payload counts. -/
def add
    (leftCounts rightCounts : SchematicPayloadCounts) :
    SchematicPayloadCounts :=
  {
    rawTermPayloadCount :=
      leftCounts.rawTermPayloadCount + rightCounts.rawTermPayloadCount
    natPayloadCount :=
      leftCounts.natPayloadCount + rightCounts.natPayloadCount
  }

/-- Whether any schematic payload was counted. -/
def hasAnyPayload (payloadCounts : SchematicPayloadCounts) : Bool :=
  payloadCounts.rawTermPayloadCount != 0 ||
    payloadCounts.natPayloadCount != 0

/-- Render counts for build-log diagnostics. -/
def format (payloadCounts : SchematicPayloadCounts) : String :=
  s!"RawTerm={payloadCounts.rawTermPayloadCount}, Nat={payloadCounts.natPayloadCount}"

end SchematicPayloadCounts

/-- Schematic payload kind recognized by the constructor census. -/
inductive SchematicPayloadKind : Type
  /-- Explicit `RawTerm` payload; this usually means a typed constructor is
  carrying untyped syntax as trusted data. -/
  | rawTerm : SchematicPayloadKind
  /-- Explicit `Nat` payload; this often means an unstructured tag or arity
  escaped a richer schema. -/
  | nat : SchematicPayloadKind
  deriving Inhabited, Repr

/-- Classify a constructor parameter type as a schematic payload type. -/
def schematicPayloadKind? (parameterType : Expr) :
    Option SchematicPayloadKind :=
  match parameterType.getAppFn with
  | .const typeName _ =>
      if typeName == `LeanFX2.RawTerm then
        some SchematicPayloadKind.rawTerm
      else if typeName == `Nat then
        some SchematicPayloadKind.nat
      else
        none
  | _ => none

/-- Turn one recognized schematic payload into a singleton count. -/
def countForSchematicPayloadKind
    (payloadKind : SchematicPayloadKind) :
    SchematicPayloadCounts :=
  match payloadKind with
  | .rawTerm => { rawTermPayloadCount := 1 }
  | .nat => { natPayloadCount := 1 }

/-- Count explicit schematic payloads in a constructor type.

Implicit parameters are skipped so family indices such as `{scope : Nat}` do
not pollute the budget.  The audit is intentionally focused on explicit data
the constructor accepts from callers. -/
partial def countExplicitSchematicPayloads (constructorType : Expr) :
    SchematicPayloadCounts :=
  match constructorType with
  | .forallE _ parameterType bodyType binderInfo =>
      let bodyCounts := countExplicitSchematicPayloads bodyType
      let parameterCounts :=
        match binderInfo with
        | .default =>
            match schematicPayloadKind? parameterType with
            | some payloadKind => countForSchematicPayloadKind payloadKind
            | none => {}
        | _ => {}
      parameterCounts.add bodyCounts
  | _ => {}

/-- One constructor that contributes to the schematic-payload budget. -/
structure SchematicPayloadRecord where
  /-- Constructor name being reported. -/
  constructorName : Name
  /-- Counts contributed by this constructor. -/
  payloadCounts : SchematicPayloadCounts
  deriving Inhabited, Repr

/-- Count schematic payloads for one constructor if it exists. -/
def schematicPayloadRecord?
    (environment : Environment) (constructorName : Name) :
    Option SchematicPayloadRecord :=
  match environment.find? constructorName with
  | some (.ctorInfo constructorInfo) =>
      let payloadCounts :=
        countExplicitSchematicPayloads constructorInfo.type
      if payloadCounts.hasAnyPayload then
        some {
          constructorName := constructorName
          payloadCounts := payloadCounts
        }
      else
        none
  | _ => none

/-- Collect schematic-payload records for every constructor of an inductive. -/
def schematicPayloadRecordsForInductive
    (environment : Environment) (inductiveName : Name) :
    Array SchematicPayloadRecord :=
  let constructorNames := getInductiveConstructorNames environment inductiveName
  constructorNames.foldl
    (init := (#[] : Array SchematicPayloadRecord))
    (fun records constructorName =>
      match schematicPayloadRecord? environment constructorName with
      | some record => records.push record
      | none => records)

/-- Total schematic-payload counts across a record list. -/
def totalSchematicPayloadCounts
    (records : Array SchematicPayloadRecord) :
    SchematicPayloadCounts :=
  records.foldl
    (init := ({} : SchematicPayloadCounts))
    (fun payloadCounts record =>
      payloadCounts.add record.payloadCounts)

/-- Build-failing budget gate for explicit schematic payloads in an inductive's
constructors.  Budgets are ceilings: existing debt may be recorded, but new
explicit `RawTerm` or `Nat` payloads fail the build until the budget is
deliberately revised. -/
elab "#assert_schematic_payload_budget " inductiveSyntax:ident
    rawTermBudgetSyntax:num natBudgetSyntax:num : command => do
  let environment ← getEnv
  let inductiveName := inductiveSyntax.getId
  let rawTermPayloadBudget := rawTermBudgetSyntax.getNat
  let natPayloadBudget := natBudgetSyntax.getNat
  let records := schematicPayloadRecordsForInductive environment inductiveName
  let totalCounts := totalSchematicPayloadCounts records
  let isWithinBudget :=
    totalCounts.rawTermPayloadCount <= rawTermPayloadBudget &&
      totalCounts.natPayloadCount <= natPayloadBudget
  if isWithinBudget then
    let successMessage :=
      s!"schematic payload budget ok: {inductiveName} " ++
      s!"({totalCounts.format}; budget RawTerm={rawTermPayloadBudget}, " ++
      s!"Nat={natPayloadBudget}; payload ctors={records.size})"
    logInfo successMessage
  else
    let perCtorLines := records.toList.map fun record =>
      s!"  - {record.constructorName}: {record.payloadCounts.format}"
    let header :=
      s!"schematic payload budget FAILED for {inductiveName}: " ++
      s!"actual {totalCounts.format}; " ++
      s!"budget RawTerm={rawTermPayloadBudget}, Nat={natPayloadBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perCtorLines)

end LeanFX2.Tools
