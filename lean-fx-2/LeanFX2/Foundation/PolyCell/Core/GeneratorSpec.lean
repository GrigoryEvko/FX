import LeanFX2.Foundation.PolyCell.Core.CellSort
import LeanFX2.Foundation.PolyCell.Core.PolyTerm
/-!
# GeneratorSpec — First Sort/Child Metadata for Certified PolyCells

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
  deriving DecidableEq, Repr

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
  /-- Sort certified for this generator. -/
  cellSort : CellSort
  /-- Dimension certified for this generator.  Current seed generators are
  dim zero, but the field is explicit so later metadata does not need a
  different record. -/
  cellDimension : CellDim
  /-- Ordered child positions expected by this generator. -/
  childSpecs : List ChildSpec
  deriving DecidableEq, Repr

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
  sourceDimension : CellDim
  deriving DecidableEq, Repr

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

/-- Target metadata for application: function and argument at the same scope. -/
def applicationGeneratorSpec : GeneratorSpec where
  cellId := 3
  cellSort := .term
  cellDimension := 0
  childSpecs := [
    ChildSpec.termSameScope,
    ChildSpec.termSameScope
  ]

/-- Target metadata for dependent function types. -/
def piTypeGeneratorSpec : GeneratorSpec where
  cellId := PolyTerm.firstTypeCellId + 4
  cellSort := .type
  cellDimension := 0
  childSpecs := [
    ChildSpec.typeSameScope,
    ChildSpec.typeUnderBinder
  ]

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

/-- Current seed rule shell for dim-1 term rewrites. -/
def termStepRuleSpec : RuleSpec where
  ruleId := 0
  cellSort := .term
  sourceDimension := 0

theorem variableGeneratorSpec_childSpecs :
    variableGeneratorSpec.childSpecs = [] := rfl

theorem lambdaGeneratorSpec_childSpecs :
    lambdaGeneratorSpec.childSpecs =
      [ChildSpec.typeSameScope, ChildSpec.termUnderBinder] := rfl

theorem applicationGeneratorSpec_childSpecs :
    applicationGeneratorSpec.childSpecs =
      [ChildSpec.termSameScope, ChildSpec.termSameScope] := rfl

theorem piTypeGeneratorSpec_childSpecs :
    piTypeGeneratorSpec.childSpecs =
      [ChildSpec.typeSameScope, ChildSpec.typeUnderBinder] := rfl

theorem contextEmptyGeneratorSpec_childSpecs :
    contextEmptyGeneratorSpec.childSpecs = [] := rfl

theorem contextConsGeneratorSpec_childSpecs :
    contextConsGeneratorSpec.childSpecs =
      [ChildSpec.contextSameScope, ChildSpec.typeSameScope,
        ChildSpec.modeSameScope] := rfl

theorem lambdaGeneratorSpec_arity :
    lambdaGeneratorSpec.arity = 2 := rfl

theorem piTypeGeneratorSpec_arity :
    piTypeGeneratorSpec.arity = 2 := rfl

theorem contextConsGeneratorSpec_arity :
    contextConsGeneratorSpec.arity = 3 := rfl

theorem piTypeGeneratorSpec_cellId :
    piTypeGeneratorSpec.cellId = 82 := rfl

theorem contextEmptyGeneratorSpec_cellId :
    contextEmptyGeneratorSpec.cellId = 103 := rfl

theorem contextConsGeneratorSpec_cellId :
    contextConsGeneratorSpec.cellId = 104 := rfl

theorem termStepRuleSpec_sourceDimension :
    termStepRuleSpec.sourceDimension = 0 := rfl

end LeanFX2.Foundation.PolyCell.Core
