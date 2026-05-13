import LeanFX2.Tools.StrictHarness.Common
import LeanFX2.Tools.StrictHarness.Census.ModeDiscipline

/-! # LeanFX2.Tools.StrictHarness.Census.BridgeCoverage

Constructor-census budget gate for missing
`FX1Bridge.encodeTermSound_*` certificates.  One typed `Term`
constructor maps to one expected bridge soundness theorem whose shape
must mention `LeanFX2.Term`, `LeanFX2.FX1.HasType`, and the
corresponding raw constructor name.

## Root status

Layer T strict-harness audit gate. -/

namespace LeanFX2.Tools

open Lean Elab Command

/-! ## Bridge constructor coverage budget -/

/-- Exact bridge theorem name expected for a `Term` constructor suffix. -/
def exactBridgeSoundnessNameForConstructor (constructorName : Name) : Name :=
  Name.str
    `LeanFX2.FX1Bridge
    ("encodeTermSound_" ++ Name.lastSegmentString constructorName)

/-- Raw constructor names that can witness an exact bridge for a `Term`
constructor.

Most typed constructors pin the same-suffix raw constructor.  Dependent and
non-dependent lambda/application share raw syntax, so `lamPi` and `appPi`
intentionally map to the same raw constructors as `lam` and `app`. -/
def expectedRawConstructorNamesForTermConstructor
    (constructorName : Name) :
    Array Name :=
  let constructorSuffix := Name.lastSegmentString constructorName
  let rawSuffix :=
    if constructorSuffix == "lamPi" then
      "lam"
    else if constructorSuffix == "appPi" then
      "app"
    else
      constructorSuffix
  #[Name.str `LeanFX2.RawTerm rawSuffix]

/-- One `Term` constructor without a certificate-shaped exact
`FX1Bridge.encodeTermSound_*` theorem.  Fragment-specific bridge lemmas are
useful, but this exact-name matrix is the ratchet for whole-constructor bridge
coverage. -/
structure BridgeCoverageDebtRecord where
  /-- Constructor name being reported. -/
  constructorName : Name
  /-- Exact bridge theorem name expected by the coverage matrix. -/
  expectedBridgeName : Name
  /-- Why the exact bridge theorem did not count. -/
  detail : String
  deriving Inhabited, Repr

/-- Whether an exact bridge coverage declaration has the minimum soundness
shape: it must consume/mention a rich `Term`, produce/mention an FX1
`HasType` derivation, and mention the raw constructor pinned by the covered
typed constructor.  This is still a shape check, not a proof of semantic
faithfulness; the separate round-trip gate checks certificate companions. -/
def isExactBridgeSoundnessShapeValid
    (constructorName : Name) (constantInfo : ConstantInfo) :
    Bool :=
  let expectedRawConstructors :=
    expectedRawConstructorNamesForTermConstructor constructorName
  doesExprMentionConst `LeanFX2.Term constantInfo.type &&
    doesExprMentionConst `LeanFX2.FX1.HasType constantInfo.type &&
    expectedRawConstructors.any
      (fun rawConstructorName =>
        doesExprMentionConst rawConstructorName constantInfo.type)

/-- Report bridge coverage debt for one constructor. -/
def bridgeCoverageDebtRecord?
    (environment : Environment) (constructorName : Name) :
    Option BridgeCoverageDebtRecord :=
  let expectedBridgeName := exactBridgeSoundnessNameForConstructor constructorName
  match environment.find? expectedBridgeName with
  | some constantInfo =>
      if isExactBridgeSoundnessShapeValid constructorName constantInfo then
        none
      else
        some {
          constructorName := constructorName
          expectedBridgeName := expectedBridgeName
          detail :=
            "declaration exists but is not Term/raw-ctor -> FX1.HasType shaped"
        }
  | none =>
      some {
        constructorName := constructorName
        expectedBridgeName := expectedBridgeName
        detail := "missing declaration"
      }

/-- Collect exact bridge coverage debt records for an inductive. -/
def bridgeCoverageDebtRecordsForInductive
    (environment : Environment) (inductiveName : Name) :
    Array BridgeCoverageDebtRecord :=
  let constructorNames := getInductiveConstructorNames environment inductiveName
  constructorNames.foldl
    (init := (#[] : Array BridgeCoverageDebtRecord))
    (fun records constructorName =>
      match bridgeCoverageDebtRecord? environment constructorName with
      | some record => records.push record
      | none => records)

/-- Build-failing budget gate for exact `encodeTermSound_*` constructor coverage.
This intentionally does not count narrower demo fragments as full constructor
coverage. -/
elab "#assert_bridge_exact_coverage_budget " inductiveSyntax:ident
    bridgeDebtBudgetSyntax:num : command => do
  let environment ← getEnv
  let inductiveName := inductiveSyntax.getId
  let bridgeDebtBudget := bridgeDebtBudgetSyntax.getNat
  let records := bridgeCoverageDebtRecordsForInductive environment inductiveName
  let constructorCount := getInductiveConstructorNames environment inductiveName |>.size
  let coveredCount := constructorCount - records.size
  if records.size <= bridgeDebtBudget then
    logInfo
      (s!"bridge exact coverage budget ok: {inductiveName} " ++
      s!"({coveredCount}/{constructorCount} exact bridge soundness theorems; " ++
      s!"debt {records.size}/{bridgeDebtBudget})")
  else
    let perCtorLines := records.toList.map fun record =>
      s!"  - {record.constructorName}: expected {record.expectedBridgeName}; " ++
      record.detail
    let header :=
      s!"bridge exact coverage budget FAILED for {inductiveName}: " ++
      s!"{records.size} unbridged ctors exceed budget {bridgeDebtBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perCtorLines)

end LeanFX2.Tools
