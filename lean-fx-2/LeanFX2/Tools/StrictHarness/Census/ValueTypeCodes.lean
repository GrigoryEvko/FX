import LeanFX2.Tools.StrictHarness.Common
import LeanFX2.Tools.StrictHarness.Census.ModeDiscipline
import LeanFX2.Tools.StrictHarness.Census.SemanticSignature
import LeanFX2.Tools.StrictHarness.Census.ExactSnapshots

/-! # LeanFX2.Tools.StrictHarness.Census.ValueTypeCodes

Constructor-census budget + snapshot gates for `Term.*Code` type-code
constructors whose computational payload contains no recursive `Term`
child.  Such constructors are value-shaped rather than recursively
typed and miss the all-raw-payload gate because their proof binders
(e.g. `levelLe`) hide their schematic nature.

## Root status

Layer T strict-harness audit gate. -/

namespace LeanFX2.Tools

open Lean Elab Command

/-! ## Value-shaped type-code constructor gate

The all-raw-payload gate deliberately ignores proof binders, which made it
miss the `*Code` constructors: they carry proof premises such as
`levelLe : outerLevel.toNat + 1 <= level`, but their computational payload is
still schematic rather than recursively typed.  This gate tracks type-code
constructors whose explicit parameters contain no recursive `Term` child.
-/

/-- Whether a constructor name is one of the `Term.*Code` type-code ctors. -/
def isTypeCodeConstructorName (constructorName : Name) : Bool :=
  (Name.lastSegmentString constructorName).endsWith "Code"

/-- Whether a constructor signature has any explicit recursive `Term` child. -/
partial def hasExplicitTermChildBinder (constructorType : Expr) : Bool :=
  match constructorType with
  | .forallE _ parameterType bodyType binderInfo =>
      let currentBinderIsTermChild :=
        match binderInfo with
        | .default => doesExprMentionConst `LeanFX2.Term parameterType
        | _ => false
      currentBinderIsTermChild || hasExplicitTermChildBinder bodyType
  | _ => false

/-- Report a value-shaped type-code constructor if it has no recursive Term
child tying the code payload back to typed syntax. -/
def valueTypeCodeDebtRecord?
    (environment : Environment) (constructorName : Name) :
    Option SignatureDebtRecord :=
  if !isTypeCodeConstructorName constructorName then
    none
  else
    match environment.find? constructorName with
    | some (.ctorInfo constructorInfo) =>
        if hasExplicitTermChildBinder constructorInfo.type then
          none
        else
          some {
            constructorName := constructorName
            detail := "type-code constructor has no recursive Term child"
          }
    | _ => none

/-- Collect value-shaped type-code debt records across a Term inductive. -/
def valueTypeCodeDebtRecordsForInductive
    (environment : Environment) (inductiveName : Name) :
    Array SignatureDebtRecord :=
  let constructorNames := getInductiveConstructorNames environment inductiveName
  constructorNames.foldl
    (init := (#[] : Array SignatureDebtRecord))
    (fun records constructorName =>
      match valueTypeCodeDebtRecord? environment constructorName with
      | some record => records.push record
      | none => records)

/-- Expected current value-shaped type-code constructors. -/
def expectedTermValueTypeCodeDebtNames : Array Name := #[
  `LeanFX2.Term.universeCode,
  `LeanFX2.Term.arrowCode,
  `LeanFX2.Term.piTyCode,
  `LeanFX2.Term.sigmaTyCode,
  `LeanFX2.Term.productCode,
  `LeanFX2.Term.sumCode,
  `LeanFX2.Term.listCode,
  `LeanFX2.Term.optionCode,
  `LeanFX2.Term.eitherCode,
  `LeanFX2.Term.idCode,
  `LeanFX2.Term.equivCode
]

/-- Build-failing budget gate for `Term.*Code` ctors whose code payloads are
value-shaped instead of recursive typed subterms. -/
elab "#assert_value_type_code_budget " inductiveSyntax:ident
    typeCodeBudgetSyntax:num : command => do
  let environment ← getEnv
  let inductiveName := inductiveSyntax.getId
  let typeCodeBudget := typeCodeBudgetSyntax.getNat
  let records := valueTypeCodeDebtRecordsForInductive environment inductiveName
  recordAuditCount `value_type_code_ctor records.size
  if records.size <= typeCodeBudget then
    logInfo
      (s!"value-shaped type-code budget ok: {inductiveName} " ++
      s!"({records.size}/{typeCodeBudget} *Code ctors have no Term child)")
  else
    let perCtorLines := records.toList.map fun record =>
      s!"  - {record.constructorName}: {record.detail}"
    let header :=
      s!"value-shaped type-code budget FAILED for {inductiveName}: " ++
      s!"{records.size} *Code ctors exceed budget {typeCodeBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perCtorLines)

/-- Exact snapshot for the current value-shaped type-code constructor debt. -/
elab "#assert_value_type_code_snapshot " inductiveSyntax:ident :
    command => do
  let environment ← getEnv
  let inductiveName := inductiveSyntax.getId
  assertExactDebtSnapshot "Term value-shaped type-code debt"
    `value_type_code_ctor_snapshot
    (valueTypeCodeDebtRecordsForInductive environment inductiveName |>
      signatureDebtConstructorNames)
    expectedTermValueTypeCodeDebtNames

end LeanFX2.Tools
