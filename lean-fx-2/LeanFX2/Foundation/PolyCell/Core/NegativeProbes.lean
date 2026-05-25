import LeanFX2.Foundation.PolyCell.Core.CheckResult
import LeanFX2.Foundation.PolyCell.Core.GeneratorSpec
/-!
# NegativeProbes — Malformed Raw Inputs for the Future Checker

This file records raw cells that the future raw-to-certified checker must
reject.  It does not implement the checker and does not prove rejection yet:
the probe catalog is a concrete, audited set of hostile inputs that later
`Check.lean` must connect to executable rejection theorems.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- A raw-inference negative probe.

The `dimension` field keeps the raw input's dimension explicit while still
allowing one list to contain dim-0 atoms and dim-1 composites. -/
structure RawInferNegativeProbe (profile : PolyProfile) where
  /-- Dimension of the malformed raw input. -/
  dimension : CellDim
  /-- Malformed raw input. -/
  rawCell : PolyTerm profile dimension
  /-- Rejection that the future inference checker must return. -/
  expectedRejection : CellCheckRejection

/-- A negative probe for expected-shape checking.

`wrongSort` belongs to expected-shape checking rather than bare inference:
the raw cell may infer a real sort, but not the caller's requested sort. -/
structure RawExpectedShapeNegativeProbe (profile : PolyProfile) where
  /-- Dimension of the malformed raw input. -/
  dimension : CellDim
  /-- Sort requested by the caller. -/
  expectedSort : CellSort
  /-- Scope requested by the caller. -/
  expectedScope : Nat
  /-- Raw input that should fail the expected-shape check. -/
  rawCell : PolyTerm profile dimension
  /-- Rejection that the future expected-shape checker must return. -/
  expectedRejection : CellCheckRejection

namespace NegativeProbes

/-- Payload sentinel for a known generator whose payload should not decode. -/
def badPayloadSentinel : Nat := 9001

/-- Payload sentinel for a known generator that decodes to the wrong arity. -/
def wrongAritySentinel : Nat := 9002

/-- Payload sentinel for a known generator with a child of the wrong shape. -/
def wrongChildShapeSentinel : Nat := 9003

/-- A small accepted-looking term atom used only to build malformed cells. -/
def seedTermAtom (profile : PolyProfile) : PolyTerm profile 0 :=
  .atom variableGeneratorSpec.cellId 0

/-- A second term atom with different raw payload. -/
def alternateTermAtom (profile : PolyProfile) : PolyTerm profile 0 :=
  .atom variableGeneratorSpec.cellId 1

/-- A third term atom with different raw payload. -/
def thirdTermAtom (profile : PolyProfile) : PolyTerm profile 0 :=
  .atom variableGeneratorSpec.cellId 2

/-- A fourth term atom with different raw payload. -/
def fourthTermAtom (profile : PolyProfile) : PolyTerm profile 0 :=
  .atom variableGeneratorSpec.cellId 3

/-- Unknown dim-0 generator id. -/
def unknownGeneratorRawCell (profile : PolyProfile) : PolyTerm profile 0 :=
  .atom (contextConsGeneratorSpec.cellId + 1000) 0

/-- Known lambda generator with a payload reserved for bad-payload testing. -/
def badPayloadRawCell (profile : PolyProfile) : PolyTerm profile 0 :=
  .atom lambdaGeneratorSpec.cellId badPayloadSentinel

/-- Known lambda generator with a payload reserved for wrong-arity testing. -/
def wrongArityRawCell (profile : PolyProfile) : PolyTerm profile 0 :=
  .atom lambdaGeneratorSpec.cellId wrongAritySentinel

/-- Known lambda generator with a payload reserved for child-shape testing. -/
def wrongChildShapeRawCell (profile : PolyProfile) : PolyTerm profile 0 :=
  .atom lambdaGeneratorSpec.cellId wrongChildShapeSentinel

/-- Known rule over an endpoint whose generator id is not supported. -/
def badBoundaryEndpointRawCell (profile : PolyProfile) : PolyTerm profile 1 :=
  .cell termStepRuleSpec.ruleId
    (unknownGeneratorRawCell profile)
    (seedTermAtom profile)

/-- First step used in the bad-vertical-boundary probe. -/
def firstMismatchedStepRawCell (profile : PolyProfile) : PolyTerm profile 1 :=
  .cell termStepRuleSpec.ruleId
    (seedTermAtom profile)
    (alternateTermAtom profile)

/-- Second step used in the bad-vertical-boundary probe. -/
def secondMismatchedStepRawCell (profile : PolyProfile) : PolyTerm profile 1 :=
  .cell termStepRuleSpec.ruleId
    (thirdTermAtom profile)
    (fourthTermAtom profile)

/-- Vertical composition whose middle endpoint does not match. -/
def badVerticalBoundaryRawCell (profile : PolyProfile) : PolyTerm profile 1 :=
  .compV (firstMismatchedStepRawCell profile)
    (secondMismatchedStepRawCell profile)

/-- Raw horizontal composition must remain unsupported until Gray data exists. -/
def unsupportedCompHRawCell (profile : PolyProfile) : PolyTerm profile 1 :=
  .compH (firstMismatchedStepRawCell profile)
    (secondMismatchedStepRawCell profile)

/-- A context atom checked as a term should fail with `wrongSort`. -/
def wrongSortRawCell (profile : PolyProfile) : PolyTerm profile 0 :=
  .atom contextEmptyGeneratorSpec.cellId 0

/-- Probe for `unknownGenerator`. -/
def unknownGeneratorProbe (profile : PolyProfile) :
    RawInferNegativeProbe profile where
  dimension := 0
  rawCell := unknownGeneratorRawCell profile
  expectedRejection := .unknownGenerator

/-- Probe for `badPayload`. -/
def badPayloadProbe (profile : PolyProfile) :
    RawInferNegativeProbe profile where
  dimension := 0
  rawCell := badPayloadRawCell profile
  expectedRejection := .badPayload

/-- Probe for `wrongArity`. -/
def wrongArityProbe (profile : PolyProfile) :
    RawInferNegativeProbe profile where
  dimension := 0
  rawCell := wrongArityRawCell profile
  expectedRejection := .wrongArity

/-- Probe for `wrongChildShape`. -/
def wrongChildShapeProbe (profile : PolyProfile) :
    RawInferNegativeProbe profile where
  dimension := 0
  rawCell := wrongChildShapeRawCell profile
  expectedRejection := .wrongChildShape

/-- Probe for `badBoundaryEndpoint`. -/
def badBoundaryEndpointProbe (profile : PolyProfile) :
    RawInferNegativeProbe profile where
  dimension := 1
  rawCell := badBoundaryEndpointRawCell profile
  expectedRejection := .badBoundaryEndpoint

/-- Probe for `badVerticalBoundary`. -/
def badVerticalBoundaryProbe (profile : PolyProfile) :
    RawInferNegativeProbe profile where
  dimension := 1
  rawCell := badVerticalBoundaryRawCell profile
  expectedRejection := .badVerticalBoundary

/-- Probe for `unsupportedCompH`. -/
def unsupportedCompHProbe (profile : PolyProfile) :
    RawInferNegativeProbe profile where
  dimension := 1
  rawCell := unsupportedCompHRawCell profile
  expectedRejection := .unsupportedCompH

/-- Probe for expected-shape `wrongSort`. -/
def wrongSortProbe (profile : PolyProfile) :
    RawExpectedShapeNegativeProbe profile where
  dimension := 0
  expectedSort := .term
  expectedScope := 0
  rawCell := wrongSortRawCell profile
  expectedRejection := .wrongSort

/-- Inference probes, one for each inference-level rejection reason. -/
def inferNegativeProbes (profile : PolyProfile) :
    List (RawInferNegativeProbe profile) :=
  [unknownGeneratorProbe profile,
    badPayloadProbe profile,
    wrongArityProbe profile,
    wrongChildShapeProbe profile,
    badBoundaryEndpointProbe profile,
    badVerticalBoundaryProbe profile,
    unsupportedCompHProbe profile]

/-- Expected-shape probes, currently only `wrongSort`. -/
def expectedShapeNegativeProbes (profile : PolyProfile) :
    List (RawExpectedShapeNegativeProbe profile) :=
  [wrongSortProbe profile]

/-- Inference probe count. -/
theorem inferNegativeProbes_length (profile : PolyProfile) :
    (inferNegativeProbes profile).length = 7 := rfl

/-- Expected-shape probe count. -/
theorem expectedShapeNegativeProbes_length (profile : PolyProfile) :
    (expectedShapeNegativeProbes profile).length = 1 := rfl

end NegativeProbes

end LeanFX2.Foundation.PolyCell.Core
