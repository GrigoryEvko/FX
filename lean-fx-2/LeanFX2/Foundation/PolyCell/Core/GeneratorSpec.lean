import LeanFX2.Foundation.PolyCell.Core.CellSort
import LeanFX2.Foundation.PolyCell.Core.PolyTerm
/-!
# GeneratorSpec — First Sort/Child Metadata for PolyCells

This file begins the metadata layer that will let the raw-to-certified checker
reject malformed raw cells.  It is intentionally only a table of computable
shape data: no raw `PolyTerm` is accepted here, and no typing theorem is
claimed.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- One expected child position of a generator.

`scopeShift` is separate from arity.  A generator can have two children while
only one of them lives under an extended scope. -/
structure ChildSpec where
  /-- Required sort of this child. -/
  cellSort : CellSort
  /-- Required dimension of this child. -/
  cellDimension : CellDim
  /-- Scope increment applied to this child relative to the parent scope. -/
  scopeShift : Nat
  deriving DecidableEq

namespace ChildSpec

/-- A child at the same scope and dimension zero. -/
def sameScopeDimZero (cellSort : CellSort) : ChildSpec where
  cellSort := cellSort
  cellDimension := 0
  scopeShift := 0

/-- A child under one newly bound variable and dimension zero. -/
def boundDimZero (cellSort : CellSort) : ChildSpec where
  cellSort := cellSort
  cellDimension := 0
  scopeShift := 1

/-- Same-scope context child. -/
def contextSameScope : ChildSpec :=
  sameScopeDimZero .context

/-- Same-scope type child. -/
def typeSameScope : ChildSpec :=
  sameScopeDimZero .type

/-- Same-scope term child. -/
def termSameScope : ChildSpec :=
  sameScopeDimZero .term

/-- Same-scope mode child. -/
def modeSameScope : ChildSpec :=
  sameScopeDimZero .mode

/-- Bound-scope type child. -/
def typeUnderBinder : ChildSpec :=
  boundDimZero .type

/-- Bound-scope term child. -/
def termUnderBinder : ChildSpec :=
  boundDimZero .term

end ChildSpec

/-- Sort and child metadata for one dim-0 generator. -/
structure GeneratorSpec where
  /-- Raw cell id used by `PolyTerm.atom`. -/
  cellId : CellId
  /-- Sort declared for this generator. -/
  cellSort : CellSort
  /-- Dimension declared for this generator.  Current seed generators are
  dim zero, but the field is explicit so later metadata does not need a
  different record. -/
  cellDimension : CellDim
  /-- Ordered child positions expected by this generator. -/
  childSpecs : List ChildSpec
  deriving DecidableEq

namespace GeneratorSpec

/-- Computed arity of a generator from its child-spec list. -/
def arity (generatorSpec : GeneratorSpec) : Nat :=
  generatorSpec.childSpecs.length

end GeneratorSpec

/-- Sort and endpoint metadata for one dim-(n+1) generating rule. -/
structure RuleSpec where
  /-- Raw rule id used by `PolyTerm.cell`. -/
  ruleId : CellId
  /-- Sort of the source and target endpoints. -/
  cellSort : CellSort
  /-- Dimension of the source and target endpoints. -/
  endpointDimension : CellDim
  deriving DecidableEq

/-- Legacy-compatible id for the current `var` term constructor. -/
def variableGeneratorSpec : GeneratorSpec where
  cellId := 0
  cellSort := .term
  cellDimension := 0
  childSpecs := []

/-- Target metadata for a lambda term: domain type plus body under one binder. -/
def lambdaGeneratorSpec : GeneratorSpec where
  cellId := 2
  cellSort := .term
  cellDimension := 0
  childSpecs := [
    ChildSpec.typeSameScope,
    ChildSpec.termUnderBinder
  ]

/-- First finite lambda payload whose decoded children are unit type at the
parent scope and `var 0` under the binder. -/
def lambdaUnitTypeBodyVarZeroPayload : Nat := 9200

/-- Target metadata for application: function and argument at the same scope. -/
def applicationGeneratorSpec : GeneratorSpec where
  cellId := 3
  cellSort := .term
  cellDimension := 0
  childSpecs := [
    ChildSpec.termSameScope,
    ChildSpec.termSameScope
  ]

/-- First finite application payload whose decoded children are `var 0` and
`var 1` at the parent scope. -/
def applicationVarZeroVarOnePayload : Nat := 9100

/-- Target metadata for the nullary unit type. -/
def unitTypeGeneratorSpec : GeneratorSpec where
  cellId := PolyTerm.firstTypeCellId
  cellSort := .type
  cellDimension := 0
  childSpecs := []

/-- Target metadata for dependent function types. -/
def piTypeGeneratorSpec : GeneratorSpec where
  cellId := PolyTerm.firstTypeCellId + 4
  cellSort := .type
  cellDimension := 0
  childSpecs := [
    ChildSpec.typeSameScope,
    ChildSpec.typeUnderBinder
  ]

/-- First finite pi-type payload whose decoded children are unit type at the
parent scope and unit type under the binder. -/
def piTypeUnitCodomainUnitPayload : Nat := 9300

/-- First context generator id, immediately after current term/type ids. -/
def firstContextGeneratorCellId : CellId :=
  PolyTerm.typeCellIdLimit

/-- Target metadata for the empty context. -/
def contextEmptyGeneratorSpec : GeneratorSpec where
  cellId := firstContextGeneratorCellId
  cellSort := .context
  cellDimension := 0
  childSpecs := []

/-- Target metadata for context extension by one typed/mode-annotated slot. -/
def contextConsGeneratorSpec : GeneratorSpec where
  cellId := firstContextGeneratorCellId + 1
  cellSort := .context
  cellDimension := 0
  childSpecs := [
    ChildSpec.contextSameScope,
    ChildSpec.typeSameScope,
    ChildSpec.modeSameScope
  ]

/-- First finite context-extension payload whose decoded children are empty
context, unit type, and linear mode at the parent scope. -/
def contextConsEmptyUnitLinearPayload : Nat := 9400

/-- First mode generator id, immediately after current context ids. -/
def firstModeGeneratorCellId : CellId :=
  firstContextGeneratorCellId + 2

/-- Target metadata for the nullary linear mode. -/
def linearModeGeneratorSpec : GeneratorSpec where
  cellId := firstModeGeneratorCellId
  cellSort := .mode
  cellDimension := 0
  childSpecs := []

/-- Current seed rule shell for dim-1 term rewrites. -/
def termStepRuleSpec : RuleSpec where
  ruleId := 0
  cellSort := .term
  endpointDimension := 0

/-- Definitional ratchets for the seed metadata table.
These facts do not certify raw cells; they only make table drift visible to
the audit harness. -/
theorem variableGeneratorSpec_childSpecs :
    variableGeneratorSpec.childSpecs = [] := rfl

theorem lambdaGeneratorSpec_childSpecs :
    lambdaGeneratorSpec.childSpecs =
      [ChildSpec.typeSameScope, ChildSpec.termUnderBinder] := rfl

theorem applicationGeneratorSpec_childSpecs :
    applicationGeneratorSpec.childSpecs =
      [ChildSpec.termSameScope, ChildSpec.termSameScope] := rfl

theorem unitTypeGeneratorSpec_childSpecs :
    unitTypeGeneratorSpec.childSpecs = [] := rfl

theorem piTypeGeneratorSpec_childSpecs :
    piTypeGeneratorSpec.childSpecs =
      [ChildSpec.typeSameScope, ChildSpec.typeUnderBinder] := rfl

theorem contextEmptyGeneratorSpec_childSpecs :
    contextEmptyGeneratorSpec.childSpecs = [] := rfl

theorem contextConsGeneratorSpec_childSpecs :
    contextConsGeneratorSpec.childSpecs =
      [ChildSpec.contextSameScope, ChildSpec.typeSameScope,
        ChildSpec.modeSameScope] := rfl

theorem linearModeGeneratorSpec_childSpecs :
    linearModeGeneratorSpec.childSpecs = [] := rfl

theorem variableGeneratorSpec_arity :
    variableGeneratorSpec.arity = 0 := rfl

theorem lambdaGeneratorSpec_arity :
    lambdaGeneratorSpec.arity = 2 := rfl

theorem applicationGeneratorSpec_arity :
    applicationGeneratorSpec.arity = 2 := rfl

theorem unitTypeGeneratorSpec_arity :
    unitTypeGeneratorSpec.arity = 0 := rfl

theorem piTypeGeneratorSpec_arity :
    piTypeGeneratorSpec.arity = 2 := rfl

theorem contextEmptyGeneratorSpec_arity :
    contextEmptyGeneratorSpec.arity = 0 := rfl

theorem contextConsGeneratorSpec_arity :
    contextConsGeneratorSpec.arity = 3 := rfl

theorem linearModeGeneratorSpec_arity :
    linearModeGeneratorSpec.arity = 0 := rfl

theorem variableGeneratorSpec_cellId :
    variableGeneratorSpec.cellId = 0 := rfl

theorem lambdaGeneratorSpec_cellId :
    lambdaGeneratorSpec.cellId = 2 := rfl

theorem applicationGeneratorSpec_cellId :
    applicationGeneratorSpec.cellId = 3 := rfl

theorem piTypeGeneratorSpec_cellId :
    piTypeGeneratorSpec.cellId = 82 := rfl

theorem unitTypeGeneratorSpec_cellId :
    unitTypeGeneratorSpec.cellId = 78 := rfl

theorem contextEmptyGeneratorSpec_cellId :
    contextEmptyGeneratorSpec.cellId = 103 := rfl

theorem unitTypeGeneratorSpec_cellId_eq_declared :
    unitTypeGeneratorSpec.cellId = PolyTerm.firstTypeCellId := rfl

theorem contextConsGeneratorSpec_cellId :
    contextConsGeneratorSpec.cellId = 104 := rfl

theorem firstModeGeneratorCellId_eq_declared :
    firstModeGeneratorCellId = PolyTerm.typeCellIdLimit + 2 := rfl

theorem linearModeGeneratorSpec_cellId :
    linearModeGeneratorSpec.cellId = 105 := rfl

theorem piTypeGeneratorSpec_cellId_eq_declared :
    piTypeGeneratorSpec.cellId = PolyTerm.firstTypeCellId + 4 := rfl

theorem contextEmptyGeneratorSpec_cellId_eq_declared :
    contextEmptyGeneratorSpec.cellId = PolyTerm.typeCellIdLimit := rfl

theorem contextConsGeneratorSpec_cellId_eq_declared :
    contextConsGeneratorSpec.cellId = PolyTerm.typeCellIdLimit + 1 := rfl

theorem linearModeGeneratorSpec_cellId_eq_declared :
    linearModeGeneratorSpec.cellId = firstModeGeneratorCellId := rfl

theorem termStepRuleSpec_ruleId :
    termStepRuleSpec.ruleId = 0 := rfl

theorem termStepRuleSpec_cellSort :
    termStepRuleSpec.cellSort = .term := rfl

theorem termStepRuleSpec_endpointDimension :
    termStepRuleSpec.endpointDimension = 0 := rfl

end LeanFX2.Foundation.PolyCell.Core
