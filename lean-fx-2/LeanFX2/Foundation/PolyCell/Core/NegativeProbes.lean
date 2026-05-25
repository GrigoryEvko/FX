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
  /-- Scope used when screening the malformed raw input. -/
  scope : Nat
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

/-- Shared scope for inference-level probes.

The scope admits the seed variables with payloads 0, 1, 2, and 3, so the
vertical-boundary probe reaches the boundary check instead of failing early
on out-of-scope variables. -/
def defaultInferScope : Nat := 4

/-- Payload sentinel for a known generator whose payload should not decode. -/
def badPayloadSentinel : Nat := 9001

/-- Payload sentinel for a known generator that decodes to the wrong arity. -/
def wrongAritySentinel : Nat := 9002

/-- Payload sentinel for a known generator with a child of the wrong shape. -/
def wrongChildShapeSentinel : Nat := 9003

/-- First finite application payload accepted by the executable screen.

It decodes to `var 0` applied to `var 1`.  This is a checker fixture, not a
claim that the application is fully typed by the legacy kernel. -/
def applicationVarZeroVarOnePayload : Nat :=
  LeanFX2.Foundation.PolyCell.Core.applicationVarZeroVarOnePayload

/-- Application payload whose decoded function child is a type cell. -/
def applicationTypeAsFunctionPayload : Nat := 9101

/-- Application payload whose decoded argument child is a type cell. -/
def applicationTypeAsArgumentPayload : Nat := 9102

/-- Application payload whose decoded argument is outside the parent scope. -/
def applicationOutOfScopeArgumentPayload : Nat := 9103

/-- Application payload whose decoded function child is a mode cell. -/
def applicationModeAsFunctionPayload : Nat := 9104

/-- Application payload whose decoded function child is a context cell. -/
def applicationContextAsFunctionPayload : Nat := 9105

/-- Application payload whose decoded argument child is a mode cell. -/
def applicationModeAsArgumentPayload : Nat := 9106

/-- Application payload whose decoded argument child is a context cell. -/
def applicationContextAsArgumentPayload : Nat := 9107

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

/-- A small accepted-looking context atom used to test cross-sort rejection. -/
def seedContextAtom (profile : PolyProfile) : PolyTerm profile 0 :=
  .atom contextEmptyGeneratorSpec.cellId 0

/-- A small accepted-looking type atom used to test cross-sort rejection. -/
def seedTypeAtom (profile : PolyProfile) : PolyTerm profile 0 :=
  .atom unitTypeGeneratorSpec.cellId 0

/-- A small accepted-looking mode atom used to test cross-sort rejection. -/
def seedModeAtom (profile : PolyProfile) : PolyTerm profile 0 :=
  .atom linearModeGeneratorSpec.cellId 0

/-- Dim-0 generator id not present in the current supported seed table. -/
def unknownGeneratorRawCell (profile : PolyProfile) : PolyTerm profile 0 :=
  .atom (lambdaGeneratorSpec.cellId - 1) 0

/-- Known variable generator with a de Bruijn index outside the probe scope. -/
def outOfScopeVariableRawCell (profile : PolyProfile) : PolyTerm profile 0 :=
  .atom variableGeneratorSpec.cellId defaultInferScope

/-- Known lambda generator with a payload reserved for bad-payload testing. -/
def badPayloadRawCell (profile : PolyProfile) : PolyTerm profile 0 :=
  .atom lambdaGeneratorSpec.cellId badPayloadSentinel

/-- Known unit-type generator with a non-nullary payload. -/
def badUnitTypePayloadRawCell (profile : PolyProfile) : PolyTerm profile 0 :=
  .atom unitTypeGeneratorSpec.cellId badPayloadSentinel

/-- Known linear-mode generator with a non-nullary payload. -/
def badLinearModePayloadRawCell (profile : PolyProfile) : PolyTerm profile 0 :=
  .atom linearModeGeneratorSpec.cellId badPayloadSentinel

/-- Known lambda generator with a payload reserved for wrong-arity testing. -/
def wrongArityRawCell (profile : PolyProfile) : PolyTerm profile 0 :=
  .atom lambdaGeneratorSpec.cellId wrongAritySentinel

/-- Known lambda generator with a payload reserved for child-shape testing. -/
def wrongChildShapeRawCell (profile : PolyProfile) : PolyTerm profile 0 :=
  .atom lambdaGeneratorSpec.cellId wrongChildShapeSentinel

/-- Accepted application payload fixture over two variable atoms. -/
def applicationVarZeroVarOneRawCell (profile : PolyProfile) :
    PolyTerm profile 0 :=
  .atom applicationGeneratorSpec.cellId applicationVarZeroVarOnePayload

/-- Application payload whose decoded function child has type sort. -/
def applicationTypeAsFunctionRawCell (profile : PolyProfile) :
    PolyTerm profile 0 :=
  .atom applicationGeneratorSpec.cellId applicationTypeAsFunctionPayload

/-- Application payload whose decoded argument child has type sort. -/
def applicationTypeAsArgumentRawCell (profile : PolyProfile) :
    PolyTerm profile 0 :=
  .atom applicationGeneratorSpec.cellId applicationTypeAsArgumentPayload

/-- Application payload whose decoded argument is outside the screening scope. -/
def applicationOutOfScopeArgumentRawCell (profile : PolyProfile) :
    PolyTerm profile 0 :=
  .atom applicationGeneratorSpec.cellId applicationOutOfScopeArgumentPayload

/-- Application payload whose decoded function child has mode sort. -/
def applicationModeAsFunctionRawCell (profile : PolyProfile) :
    PolyTerm profile 0 :=
  .atom applicationGeneratorSpec.cellId applicationModeAsFunctionPayload

/-- Application payload whose decoded function child has context sort. -/
def applicationContextAsFunctionRawCell (profile : PolyProfile) :
    PolyTerm profile 0 :=
  .atom applicationGeneratorSpec.cellId applicationContextAsFunctionPayload

/-- Application payload whose decoded argument child has mode sort. -/
def applicationModeAsArgumentRawCell (profile : PolyProfile) :
    PolyTerm profile 0 :=
  .atom applicationGeneratorSpec.cellId applicationModeAsArgumentPayload

/-- Application payload whose decoded argument child has context sort. -/
def applicationContextAsArgumentRawCell (profile : PolyProfile) :
    PolyTerm profile 0 :=
  .atom applicationGeneratorSpec.cellId applicationContextAsArgumentPayload

/-- Known rule over an endpoint whose generator id is not supported. -/
def badBoundaryEndpointRawCell (profile : PolyProfile) : PolyTerm profile 1 :=
  .cell termStepRuleSpec.ruleId
    (unknownGeneratorRawCell profile)
    (seedTermAtom profile)

/-- Known term-step rule applied to context endpoints instead of term endpoints. -/
def badBoundarySortRawCell (profile : PolyProfile) : PolyTerm profile 1 :=
  .cell termStepRuleSpec.ruleId
    (seedContextAtom profile)
    (seedContextAtom profile)

/-- Known term-step rule applied to type endpoints instead of term endpoints. -/
def badBoundaryTypeSortRawCell (profile : PolyProfile) : PolyTerm profile 1 :=
  .cell termStepRuleSpec.ruleId
    (seedTypeAtom profile)
    (seedTypeAtom profile)

/-- Known term-step rule applied to mode endpoints instead of term endpoints. -/
def badBoundaryModeSortRawCell (profile : PolyProfile) : PolyTerm profile 1 :=
  .cell termStepRuleSpec.ruleId
    (seedModeAtom profile)
    (seedModeAtom profile)

/-- Known term-step rule used at an unsupported endpoint dimension. -/
def wrongRuleEndpointDimensionRawCell (profile : PolyProfile) :
    PolyTerm profile 2 :=
  .cell termStepRuleSpec.ruleId
    (PolyTerm.identity (seedTermAtom profile))
    (PolyTerm.identity (alternateTermAtom profile))

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
  seedContextAtom profile

/-- A context atom checked as a type should fail with `wrongSort`. -/
def contextAsTypeRawCell (profile : PolyProfile) : PolyTerm profile 0 :=
  seedContextAtom profile

/-- A unit type atom checked as a term should fail with `wrongSort`. -/
def unitTypeAsTermRawCell (profile : PolyProfile) : PolyTerm profile 0 :=
  seedTypeAtom profile

/-- A unit type atom checked as a context should fail with `wrongSort`. -/
def unitTypeAsContextRawCell (profile : PolyProfile) : PolyTerm profile 0 :=
  seedTypeAtom profile

/-- A term atom checked as a type should fail with `wrongSort`. -/
def termAsTypeRawCell (profile : PolyProfile) : PolyTerm profile 0 :=
  seedTermAtom profile

/-- A term atom checked as a context should fail with `wrongSort`. -/
def termAsContextRawCell (profile : PolyProfile) : PolyTerm profile 0 :=
  seedTermAtom profile

/-- A mode atom checked as a term should fail with `wrongSort`. -/
def linearModeAsTermRawCell (profile : PolyProfile) : PolyTerm profile 0 :=
  seedModeAtom profile

/-- A mode atom checked as a type should fail with `wrongSort`. -/
def linearModeAsTypeRawCell (profile : PolyProfile) : PolyTerm profile 0 :=
  seedModeAtom profile

/-- A type identity cell checked as a term step should fail with `wrongSort`. -/
def typeIdentityAsTermStepRawCell (profile : PolyProfile) :
    PolyTerm profile 1 :=
  .identity (seedTypeAtom profile)

/-- Probe for `unknownGenerator`. -/
def unknownGeneratorProbe (profile : PolyProfile) :
    RawInferNegativeProbe profile where
  scope := defaultInferScope
  dimension := 0
  rawCell := unknownGeneratorRawCell profile
  expectedRejection := .unknownGenerator

/-- Probe for out-of-scope variable payload rejection. -/
def outOfScopeVariableProbe (profile : PolyProfile) :
    RawInferNegativeProbe profile where
  scope := defaultInferScope
  dimension := 0
  rawCell := outOfScopeVariableRawCell profile
  expectedRejection := .badPayload

/-- Probe for `badPayload`. -/
def badPayloadProbe (profile : PolyProfile) :
    RawInferNegativeProbe profile where
  scope := defaultInferScope
  dimension := 0
  rawCell := badPayloadRawCell profile
  expectedRejection := .badPayload

/-- Probe for rejecting non-nullary payloads on the unit-type generator. -/
def badUnitTypePayloadProbe (profile : PolyProfile) :
    RawInferNegativeProbe profile where
  scope := defaultInferScope
  dimension := 0
  rawCell := badUnitTypePayloadRawCell profile
  expectedRejection := .badPayload

/-- Probe for rejecting non-nullary payloads on the linear-mode generator. -/
def badLinearModePayloadProbe (profile : PolyProfile) :
    RawInferNegativeProbe profile where
  scope := defaultInferScope
  dimension := 0
  rawCell := badLinearModePayloadRawCell profile
  expectedRejection := .badPayload

/-- Probe for `wrongArity`. -/
def wrongArityProbe (profile : PolyProfile) :
    RawInferNegativeProbe profile where
  scope := defaultInferScope
  dimension := 0
  rawCell := wrongArityRawCell profile
  expectedRejection := .wrongArity

/-- Probe for `wrongChildShape`. -/
def wrongChildShapeProbe (profile : PolyProfile) :
    RawInferNegativeProbe profile where
  scope := defaultInferScope
  dimension := 0
  rawCell := wrongChildShapeRawCell profile
  expectedRejection := .wrongChildShape

/-- Probe for an application payload with a non-term function child. -/
def applicationTypeAsFunctionProbe (profile : PolyProfile) :
    RawInferNegativeProbe profile where
  scope := defaultInferScope
  dimension := 0
  rawCell := applicationTypeAsFunctionRawCell profile
  expectedRejection := .wrongChildShape

/-- Probe for an application payload with a non-term argument child. -/
def applicationTypeAsArgumentProbe (profile : PolyProfile) :
    RawInferNegativeProbe profile where
  scope := defaultInferScope
  dimension := 0
  rawCell := applicationTypeAsArgumentRawCell profile
  expectedRejection := .wrongChildShape

/-- Probe for an application payload with an out-of-scope argument child. -/
def applicationOutOfScopeArgumentProbe (profile : PolyProfile) :
    RawInferNegativeProbe profile where
  scope := defaultInferScope
  dimension := 0
  rawCell := applicationOutOfScopeArgumentRawCell profile
  expectedRejection := .wrongChildShape

/-- Probe for an application payload with a mode function child. -/
def applicationModeAsFunctionProbe (profile : PolyProfile) :
    RawInferNegativeProbe profile where
  scope := defaultInferScope
  dimension := 0
  rawCell := applicationModeAsFunctionRawCell profile
  expectedRejection := .wrongChildShape

/-- Probe for an application payload with a context function child. -/
def applicationContextAsFunctionProbe (profile : PolyProfile) :
    RawInferNegativeProbe profile where
  scope := defaultInferScope
  dimension := 0
  rawCell := applicationContextAsFunctionRawCell profile
  expectedRejection := .wrongChildShape

/-- Probe for an application payload with a mode argument child. -/
def applicationModeAsArgumentProbe (profile : PolyProfile) :
    RawInferNegativeProbe profile where
  scope := defaultInferScope
  dimension := 0
  rawCell := applicationModeAsArgumentRawCell profile
  expectedRejection := .wrongChildShape

/-- Probe for an application payload with a context argument child. -/
def applicationContextAsArgumentProbe (profile : PolyProfile) :
    RawInferNegativeProbe profile where
  scope := defaultInferScope
  dimension := 0
  rawCell := applicationContextAsArgumentRawCell profile
  expectedRejection := .wrongChildShape

/-- Probe for `badBoundaryEndpoint`. -/
def badBoundaryEndpointProbe (profile : PolyProfile) :
    RawInferNegativeProbe profile where
  scope := defaultInferScope
  dimension := 1
  rawCell := badBoundaryEndpointRawCell profile
  expectedRejection := .badBoundaryEndpoint

/-- Probe for an endpoint whose sort does not match the known rule. -/
def badBoundarySortProbe (profile : PolyProfile) :
    RawInferNegativeProbe profile where
  scope := defaultInferScope
  dimension := 1
  rawCell := badBoundarySortRawCell profile
  expectedRejection := .badBoundaryEndpoint

/-- Probe for a type endpoint whose sort does not match the known term rule. -/
def badBoundaryTypeSortProbe (profile : PolyProfile) :
    RawInferNegativeProbe profile where
  scope := defaultInferScope
  dimension := 1
  rawCell := badBoundaryTypeSortRawCell profile
  expectedRejection := .badBoundaryEndpoint

/-- Probe for a mode endpoint whose sort does not match the known term rule. -/
def badBoundaryModeSortProbe (profile : PolyProfile) :
    RawInferNegativeProbe profile where
  scope := defaultInferScope
  dimension := 1
  rawCell := badBoundaryModeSortRawCell profile
  expectedRejection := .badBoundaryEndpoint

/-- Probe for a known rule id used at the wrong endpoint dimension. -/
def wrongRuleEndpointDimensionProbe (profile : PolyProfile) :
    RawInferNegativeProbe profile where
  scope := defaultInferScope
  dimension := 2
  rawCell := wrongRuleEndpointDimensionRawCell profile
  expectedRejection := .unknownGenerator

/-- Probe for `badVerticalBoundary`. -/
def badVerticalBoundaryProbe (profile : PolyProfile) :
    RawInferNegativeProbe profile where
  scope := defaultInferScope
  dimension := 1
  rawCell := badVerticalBoundaryRawCell profile
  expectedRejection := .badVerticalBoundary

/-- Probe for `unsupportedCompH`. -/
def unsupportedCompHProbe (profile : PolyProfile) :
    RawInferNegativeProbe profile where
  scope := defaultInferScope
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

/-- Probe for rejecting a context atom when a type cell is expected. -/
def contextAsTypeProbe (profile : PolyProfile) :
    RawExpectedShapeNegativeProbe profile where
  dimension := 0
  expectedSort := .type
  expectedScope := defaultInferScope
  rawCell := contextAsTypeRawCell profile
  expectedRejection := .wrongSort

/-- Probe for rejecting a type atom when a term cell is expected. -/
def unitTypeAsTermProbe (profile : PolyProfile) :
    RawExpectedShapeNegativeProbe profile where
  dimension := 0
  expectedSort := .term
  expectedScope := defaultInferScope
  rawCell := unitTypeAsTermRawCell profile
  expectedRejection := .wrongSort

/-- Probe for rejecting a type atom when a context cell is expected. -/
def unitTypeAsContextProbe (profile : PolyProfile) :
    RawExpectedShapeNegativeProbe profile where
  dimension := 0
  expectedSort := .context
  expectedScope := defaultInferScope
  rawCell := unitTypeAsContextRawCell profile
  expectedRejection := .wrongSort

/-- Probe for rejecting a term atom when a type cell is expected. -/
def termAsTypeProbe (profile : PolyProfile) :
    RawExpectedShapeNegativeProbe profile where
  dimension := 0
  expectedSort := .type
  expectedScope := defaultInferScope
  rawCell := termAsTypeRawCell profile
  expectedRejection := .wrongSort

/-- Probe for rejecting a term atom when a context cell is expected. -/
def termAsContextProbe (profile : PolyProfile) :
    RawExpectedShapeNegativeProbe profile where
  dimension := 0
  expectedSort := .context
  expectedScope := defaultInferScope
  rawCell := termAsContextRawCell profile
  expectedRejection := .wrongSort

/-- Probe for rejecting a mode atom when a term cell is expected. -/
def linearModeAsTermProbe (profile : PolyProfile) :
    RawExpectedShapeNegativeProbe profile where
  dimension := 0
  expectedSort := .term
  expectedScope := defaultInferScope
  rawCell := linearModeAsTermRawCell profile
  expectedRejection := .wrongSort

/-- Probe for rejecting a mode atom when a type cell is expected. -/
def linearModeAsTypeProbe (profile : PolyProfile) :
    RawExpectedShapeNegativeProbe profile where
  dimension := 0
  expectedSort := .type
  expectedScope := defaultInferScope
  rawCell := linearModeAsTypeRawCell profile
  expectedRejection := .wrongSort

/-- Probe for rejecting a type identity when a term step is expected. -/
def typeIdentityAsTermStepProbe (profile : PolyProfile) :
    RawExpectedShapeNegativeProbe profile where
  dimension := 1
  expectedSort := .term
  expectedScope := defaultInferScope
  rawCell := typeIdentityAsTermStepRawCell profile
  expectedRejection := .wrongSort

/-- Inference probes, one for each inference-level rejection reason. -/
def inferNegativeProbes (profile : PolyProfile) :
    List (RawInferNegativeProbe profile) :=
  [unknownGeneratorProbe profile,
    outOfScopeVariableProbe profile,
    badPayloadProbe profile,
    badUnitTypePayloadProbe profile,
    badLinearModePayloadProbe profile,
    wrongArityProbe profile,
    wrongChildShapeProbe profile,
    applicationTypeAsFunctionProbe profile,
    applicationTypeAsArgumentProbe profile,
    applicationOutOfScopeArgumentProbe profile,
    applicationModeAsFunctionProbe profile,
    applicationContextAsFunctionProbe profile,
    applicationModeAsArgumentProbe profile,
    applicationContextAsArgumentProbe profile,
    badBoundaryEndpointProbe profile,
    badBoundarySortProbe profile,
    badBoundaryTypeSortProbe profile,
    badBoundaryModeSortProbe profile,
    wrongRuleEndpointDimensionProbe profile,
    badVerticalBoundaryProbe profile,
    unsupportedCompHProbe profile]

/-- Expected-shape probes for dim-0 and positive-dimensional sort mismatches. -/
def expectedShapeNegativeProbes (profile : PolyProfile) :
    List (RawExpectedShapeNegativeProbe profile) :=
  [wrongSortProbe profile,
    contextAsTypeProbe profile,
    unitTypeAsTermProbe profile,
    unitTypeAsContextProbe profile,
    termAsTypeProbe profile,
    termAsContextProbe profile,
    linearModeAsTermProbe profile,
    linearModeAsTypeProbe profile,
    typeIdentityAsTermStepProbe profile]

/-- Inference probe count. -/
theorem inferNegativeProbes_length (profile : PolyProfile) :
    (inferNegativeProbes profile).length = 21 := rfl

/-- Expected-shape probe count. -/
theorem expectedShapeNegativeProbes_length (profile : PolyProfile) :
    (expectedShapeNegativeProbes profile).length = 9 := rfl

end NegativeProbes

end LeanFX2.Foundation.PolyCell.Core
