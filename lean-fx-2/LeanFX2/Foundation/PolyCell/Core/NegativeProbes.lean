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

/-- A negative probe for certified ingress.

Some raw cells screen structurally but still must not enter the certified
layer until a trusted constructor path exists for that exact shape. -/
structure RawCertificationNegativeProbe (profile : PolyProfile) where
  /-- Scope used when certifying the malformed raw input. -/
  scope : Nat
  /-- Dimension of the malformed raw input. -/
  dimension : CellDim
  /-- Malformed or unsupported raw input. -/
  rawCell : PolyTerm profile dimension
  /-- Rejection that certified ingress must return. -/
  expectedRejection : CellCheckRejection

/-- A negative probe for the fuelled structural screen.

Fuel exhaustion is a checker-budget result, not a malformed payload, so these
probes are kept separate from ordinary inference probes that use the default
fuel budget. -/
structure RawFuelNegativeProbe (profile : PolyProfile) where
  /-- Fuel budget supplied to the fuelled screen. -/
  fuel : Nat
  /-- Scope used when screening the raw input. -/
  scope : Nat
  /-- Dimension of the raw input. -/
  dimension : CellDim
  /-- Raw input whose budgeted screen should exhaust fuel. -/
  rawCell : PolyTerm profile dimension
  /-- Rejection that the fuelled screen must return. -/
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

/-- Fuel-zero probe over an otherwise small term atom.

This pins the checker-budget diagnostic independently from payload decoding. -/
def fuelExhaustedProbe (profile : PolyProfile) :
    RawFuelNegativeProbe profile where
  fuel := 0
  scope := defaultInferScope
  dimension := 0
  rawCell := seedTermAtom profile
  expectedRejection := .fuelExhausted

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

/-- Known pi-type generator with a payload reserved for bad-payload testing. -/
def badPiTypePayloadRawCell (profile : PolyProfile) : PolyTerm profile 0 :=
  .atom piTypeGeneratorSpec.cellId badPayloadSentinel

/-- Known context-extension generator with a bad payload. -/
def badContextConsPayloadRawCell (profile : PolyProfile) :
    PolyTerm profile 0 :=
  .atom contextConsGeneratorSpec.cellId badPayloadSentinel

/-- Known lambda generator with a payload reserved for wrong-arity testing. -/
def wrongArityRawCell (profile : PolyProfile) : PolyTerm profile 0 :=
  .atom lambdaGeneratorSpec.cellId wrongAritySentinel

/-- Known lambda generator with a payload reserved for child-shape testing. -/
def wrongChildShapeRawCell (profile : PolyProfile) : PolyTerm profile 0 :=
  .atom lambdaGeneratorSpec.cellId wrongChildShapeSentinel

/-- Known pi-type generator with a wrong-arity payload. -/
def wrongPiTypeArityRawCell (profile : PolyProfile) : PolyTerm profile 0 :=
  .atom piTypeGeneratorSpec.cellId wrongAritySentinel

/-- Known pi-type generator with a wrong-child-shape payload. -/
def wrongPiTypeChildShapeRawCell (profile : PolyProfile) :
    PolyTerm profile 0 :=
  .atom piTypeGeneratorSpec.cellId wrongChildShapeSentinel

/-- Known context-extension generator with a wrong-arity payload. -/
def wrongContextConsArityRawCell (profile : PolyProfile) :
    PolyTerm profile 0 :=
  .atom contextConsGeneratorSpec.cellId wrongAritySentinel

/-- Known context-extension generator with a wrong-child-shape payload. -/
def wrongContextConsChildShapeRawCell (profile : PolyProfile) :
    PolyTerm profile 0 :=
  .atom contextConsGeneratorSpec.cellId wrongChildShapeSentinel

/-- Accepted application payload fixture over two variable atoms. -/
def applicationVarZeroVarOneRawCell (profile : PolyProfile) :
    PolyTerm profile 0 :=
  .atom applicationGeneratorSpec.cellId applicationVarZeroVarOnePayload

/-- Application generator with a payload that must not decode. -/
def applicationBadPayloadRawCell (profile : PolyProfile) :
    PolyTerm profile 0 :=
  .atom applicationGeneratorSpec.cellId badPayloadSentinel

/-- Application generator with a wrong-arity payload sentinel. -/
def applicationWrongArityRawCell (profile : PolyProfile) :
    PolyTerm profile 0 :=
  .atom applicationGeneratorSpec.cellId wrongAritySentinel

/-- Application generator with a wrong-child-shape payload sentinel. -/
def applicationWrongChildShapeRawCell (profile : PolyProfile) :
    PolyTerm profile 0 :=
  .atom applicationGeneratorSpec.cellId wrongChildShapeSentinel

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

/-- The first dim-1 term-step fixture admitted by certified ingress. -/
def termStepVarZeroVarOneRawCell (profile : PolyProfile) :
    PolyTerm profile 1 :=
  .cell termStepRuleSpec.ruleId
    (seedTermAtom profile)
    (alternateTermAtom profile)

/-- A screened term-step shape not admitted by certified ingress. -/
def unsupportedTermStepVarZeroVarTwoRawCell (profile : PolyProfile) :
    PolyTerm profile 1 :=
  .cell termStepRuleSpec.ruleId
    (seedTermAtom profile)
    (thirdTermAtom profile)

/-- A screened term-step variant not admitted by certified ingress. -/
def unsupportedTermStepVarOneVarZeroRawCell (profile : PolyProfile) :
    PolyTerm profile 1 :=
  .cell termStepRuleSpec.ruleId
    (alternateTermAtom profile)
    (seedTermAtom profile)

/-- A screened reflexive term-step variant not admitted by certified ingress. -/
def unsupportedTermStepVarZeroVarZeroRawCell (profile : PolyProfile) :
    PolyTerm profile 1 :=
  .cell termStepRuleSpec.ruleId
    (seedTermAtom profile)
    (seedTermAtom profile)

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

/-- Vertical composition with matching middle boundary but unsupported
certified ingress. -/
def matchedVerticalBoundaryRawCell (profile : PolyProfile) :
    PolyTerm profile 1 :=
  .compV
    (termStepVarZeroVarOneRawCell profile)
    (.cell termStepRuleSpec.ruleId
      (alternateTermAtom profile)
      (thirdTermAtom profile))

/-- Raw identity over the seed term remains unsupported by certified ingress;
use the derived certified operation instead. -/
def termIdentityRawCell (profile : PolyProfile) : PolyTerm profile 1 :=
  .identity (seedTermAtom profile)

/-- Raw identity over the seed type remains unsupported by certified ingress;
use the derived certified operation instead. -/
def typeIdentityRawCell (profile : PolyProfile) : PolyTerm profile 1 :=
  .identity (seedTypeAtom profile)

/-- Raw identity over the seed context remains unsupported by certified
ingress; use the derived certified operation instead. -/
def contextIdentityRawCell (profile : PolyProfile) : PolyTerm profile 1 :=
  .identity (seedContextAtom profile)

/-- Raw identity over the seed mode remains unsupported by certified ingress;
use the derived certified operation instead. -/
def modeIdentityRawCell (profile : PolyProfile) : PolyTerm profile 1 :=
  .identity (seedModeAtom profile)

/-- Raw vertical composition of two term identities remains unsupported by
certified ingress; use the derived certified operation instead. -/
def termIdentityVerticalRawCell (profile : PolyProfile) :
    PolyTerm profile 1 :=
  .compV
    (PolyTerm.identity (seedTermAtom profile))
    (PolyTerm.identity (seedTermAtom profile))

/-- Raw vertical composition of two type identities remains unsupported by
certified ingress; use the derived certified operation instead. -/
def typeIdentityVerticalRawCell (profile : PolyProfile) :
    PolyTerm profile 1 :=
  .compV
    (PolyTerm.identity (seedTypeAtom profile))
    (PolyTerm.identity (seedTypeAtom profile))

/-- Raw vertical composition of two context identities remains unsupported by
certified ingress; use the derived certified operation instead. -/
def contextIdentityVerticalRawCell (profile : PolyProfile) :
    PolyTerm profile 1 :=
  .compV
    (PolyTerm.identity (seedContextAtom profile))
    (PolyTerm.identity (seedContextAtom profile))

/-- Raw vertical composition of two mode identities remains unsupported by
certified ingress; use the derived certified operation instead. -/
def modeIdentityVerticalRawCell (profile : PolyProfile) :
    PolyTerm profile 1 :=
  .compV
    (PolyTerm.identity (seedModeAtom profile))
    (PolyTerm.identity (seedModeAtom profile))

/-- Raw horizontal composition must remain unsupported until Gray data exists. -/
def unsupportedCompHRawCell (profile : PolyProfile) : PolyTerm profile 1 :=
  .compH (firstMismatchedStepRawCell profile)
    (secondMismatchedStepRawCell profile)

/-- Horizontal composition of screened steps still lacks Gray semantics. -/
def unsupportedCompHWellScreenedRawCell (profile : PolyProfile) :
    PolyTerm profile 1 :=
  .compH (termStepVarZeroVarOneRawCell profile)
    (termStepVarZeroVarOneRawCell profile)

/-- Identity over a malformed base must reject through the base. -/
def badIdentityBaseRawCell (profile : PolyProfile) : PolyTerm profile 1 :=
  .identity (badPayloadRawCell profile)

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

/-- Probe for rejecting bad payloads on the pi-type generator. -/
def badPiTypePayloadProbe (profile : PolyProfile) :
    RawInferNegativeProbe profile where
  scope := defaultInferScope
  dimension := 0
  rawCell := badPiTypePayloadRawCell profile
  expectedRejection := .badPayload

/-- Probe for rejecting bad payloads on the context-extension generator. -/
def badContextConsPayloadProbe (profile : PolyProfile) :
    RawInferNegativeProbe profile where
  scope := defaultInferScope
  dimension := 0
  rawCell := badContextConsPayloadRawCell profile
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

/-- Probe for `wrongArity` on the pi-type generator. -/
def wrongPiTypeArityProbe (profile : PolyProfile) :
    RawInferNegativeProbe profile where
  scope := defaultInferScope
  dimension := 0
  rawCell := wrongPiTypeArityRawCell profile
  expectedRejection := .wrongArity

/-- Probe for `wrongChildShape` on the pi-type generator. -/
def wrongPiTypeChildShapeProbe (profile : PolyProfile) :
    RawInferNegativeProbe profile where
  scope := defaultInferScope
  dimension := 0
  rawCell := wrongPiTypeChildShapeRawCell profile
  expectedRejection := .wrongChildShape

/-- Probe for `wrongArity` on the context-extension generator. -/
def wrongContextConsArityProbe (profile : PolyProfile) :
    RawInferNegativeProbe profile where
  scope := defaultInferScope
  dimension := 0
  rawCell := wrongContextConsArityRawCell profile
  expectedRejection := .wrongArity

/-- Probe for `wrongChildShape` on the context-extension generator. -/
def wrongContextConsChildShapeProbe (profile : PolyProfile) :
    RawInferNegativeProbe profile where
  scope := defaultInferScope
  dimension := 0
  rawCell := wrongContextConsChildShapeRawCell profile
  expectedRejection := .wrongChildShape

/-- Probe for an application payload that must not decode. -/
def applicationBadPayloadProbe (profile : PolyProfile) :
    RawInferNegativeProbe profile where
  scope := defaultInferScope
  dimension := 0
  rawCell := applicationBadPayloadRawCell profile
  expectedRejection := .badPayload

/-- Probe for the application branch's wrong-arity sentinel. -/
def applicationWrongArityProbe (profile : PolyProfile) :
    RawInferNegativeProbe profile where
  scope := defaultInferScope
  dimension := 0
  rawCell := applicationWrongArityRawCell profile
  expectedRejection := .wrongArity

/-- Probe for the application branch's wrong-child-shape sentinel. -/
def applicationWrongChildShapeProbe (profile : PolyProfile) :
    RawInferNegativeProbe profile where
  scope := defaultInferScope
  dimension := 0
  rawCell := applicationWrongChildShapeRawCell profile
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

/-- Probe for unsupported horizontal composition over screened steps. -/
def unsupportedCompHWellScreenedProbe (profile : PolyProfile) :
    RawInferNegativeProbe profile where
  scope := defaultInferScope
  dimension := 1
  rawCell := unsupportedCompHWellScreenedRawCell profile
  expectedRejection := .unsupportedCompH

/-- Probe for identity over a malformed raw base. -/
def badIdentityBaseProbe (profile : PolyProfile) :
    RawInferNegativeProbe profile where
  scope := defaultInferScope
  dimension := 1
  rawCell := badIdentityBaseRawCell profile
  expectedRejection := .badPayload

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

/-- Probe for rejecting the accepted application when a type cell is expected. -/
def applicationVarZeroVarOneAsTypeProbe (profile : PolyProfile) :
    RawExpectedShapeNegativeProbe profile where
  dimension := 0
  expectedSort := .type
  expectedScope := defaultInferScope
  rawCell := applicationVarZeroVarOneRawCell profile
  expectedRejection := .wrongSort

/-- Probe for rejecting the accepted application when a context cell is
expected. -/
def applicationVarZeroVarOneAsContextProbe (profile : PolyProfile) :
    RawExpectedShapeNegativeProbe profile where
  dimension := 0
  expectedSort := .context
  expectedScope := defaultInferScope
  rawCell := applicationVarZeroVarOneRawCell profile
  expectedRejection := .wrongSort

/-- Probe for rejecting the accepted application when a mode cell is expected. -/
def applicationVarZeroVarOneAsModeProbe (profile : PolyProfile) :
    RawExpectedShapeNegativeProbe profile where
  dimension := 0
  expectedSort := .mode
  expectedScope := defaultInferScope
  rawCell := applicationVarZeroVarOneRawCell profile
  expectedRejection := .wrongSort

/-- Probe that expected-shape checking preserves malformed application payload
rejection. -/
def applicationBadPayloadExpectedShapeProbe (profile : PolyProfile) :
    RawExpectedShapeNegativeProbe profile where
  dimension := 0
  expectedSort := .term
  expectedScope := defaultInferScope
  rawCell := applicationBadPayloadRawCell profile
  expectedRejection := .badPayload

/-- Probe that expected-shape checking preserves malformed application arity
rejection. -/
def applicationWrongArityExpectedShapeProbe (profile : PolyProfile) :
    RawExpectedShapeNegativeProbe profile where
  dimension := 0
  expectedSort := .term
  expectedScope := defaultInferScope
  rawCell := applicationWrongArityRawCell profile
  expectedRejection := .wrongArity

/-- Probe that expected-shape checking preserves malformed application child
shape rejection. -/
def applicationWrongChildShapeExpectedShapeProbe (profile : PolyProfile) :
    RawExpectedShapeNegativeProbe profile where
  dimension := 0
  expectedSort := .term
  expectedScope := defaultInferScope
  rawCell := applicationWrongChildShapeRawCell profile
  expectedRejection := .wrongChildShape

/-- Probe for preserving bad-boundary rejection through certified ingress. -/
def certificationBadBoundaryEndpointProbe (profile : PolyProfile) :
    RawCertificationNegativeProbe profile where
  scope := defaultInferScope
  dimension := 1
  rawCell := badBoundaryEndpointRawCell profile
  expectedRejection := .badBoundaryEndpoint

/-- Probe for preserving unsupported horizontal composition rejection. -/
def certificationUnsupportedCompHProbe (profile : PolyProfile) :
    RawCertificationNegativeProbe profile where
  scope := defaultInferScope
  dimension := 1
  rawCell := unsupportedCompHRawCell profile
  expectedRejection := .unsupportedCompH

/-- Probe for a screened term step not admitted by the current certified
dim-1 ingress. -/
def certificationUnsupportedTermStepProbe (profile : PolyProfile) :
    RawCertificationNegativeProbe profile where
  scope := defaultInferScope
  dimension := 1
  rawCell := unsupportedTermStepVarZeroVarTwoRawCell profile
  expectedRejection := .unsupportedCertification

/-- Probe for an unsupported reversed term-step variant. -/
def certificationUnsupportedReversedTermStepProbe (profile : PolyProfile) :
    RawCertificationNegativeProbe profile where
  scope := defaultInferScope
  dimension := 1
  rawCell := unsupportedTermStepVarOneVarZeroRawCell profile
  expectedRejection := .unsupportedCertification

/-- Probe for an unsupported reflexive term-step variant. -/
def certificationUnsupportedReflexiveTermStepProbe (profile : PolyProfile) :
    RawCertificationNegativeProbe profile where
  scope := defaultInferScope
  dimension := 1
  rawCell := unsupportedTermStepVarZeroVarZeroRawCell profile
  expectedRejection := .unsupportedCertification

/-- Probe for a screened vertical composite whose certified construction is
not yet implemented. -/
def certificationMatchedVerticalBoundaryProbe (profile : PolyProfile) :
    RawCertificationNegativeProbe profile where
  scope := defaultInferScope
  dimension := 1
  rawCell := matchedVerticalBoundaryRawCell profile
  expectedRejection := .unsupportedCertification

/-- Probe for a screened raw term identity. -/
def certificationTermIdentityProbe (profile : PolyProfile) :
    RawCertificationNegativeProbe profile where
  scope := defaultInferScope
  dimension := 1
  rawCell := termIdentityRawCell profile
  expectedRejection := .unsupportedCertification

/-- Probe for a screened raw type identity. -/
def certificationTypeIdentityProbe (profile : PolyProfile) :
    RawCertificationNegativeProbe profile where
  scope := defaultInferScope
  dimension := 1
  rawCell := typeIdentityRawCell profile
  expectedRejection := .unsupportedCertification

/-- Probe for a screened raw context identity. -/
def certificationContextIdentityProbe (profile : PolyProfile) :
    RawCertificationNegativeProbe profile where
  scope := defaultInferScope
  dimension := 1
  rawCell := contextIdentityRawCell profile
  expectedRejection := .unsupportedCertification

/-- Probe for a screened raw mode identity. -/
def certificationModeIdentityProbe (profile : PolyProfile) :
    RawCertificationNegativeProbe profile where
  scope := defaultInferScope
  dimension := 1
  rawCell := modeIdentityRawCell profile
  expectedRejection := .unsupportedCertification

/-- Probe for a screened raw term-identity vertical composite. -/
def certificationTermIdentityVerticalProbe (profile : PolyProfile) :
    RawCertificationNegativeProbe profile where
  scope := defaultInferScope
  dimension := 1
  rawCell := termIdentityVerticalRawCell profile
  expectedRejection := .unsupportedCertification

/-- Probe for a screened raw type-identity vertical composite. -/
def certificationTypeIdentityVerticalProbe (profile : PolyProfile) :
    RawCertificationNegativeProbe profile where
  scope := defaultInferScope
  dimension := 1
  rawCell := typeIdentityVerticalRawCell profile
  expectedRejection := .unsupportedCertification

/-- Probe for a screened raw context-identity vertical composite. -/
def certificationContextIdentityVerticalProbe (profile : PolyProfile) :
    RawCertificationNegativeProbe profile where
  scope := defaultInferScope
  dimension := 1
  rawCell := contextIdentityVerticalRawCell profile
  expectedRejection := .unsupportedCertification

/-- Probe for a screened raw mode-identity vertical composite. -/
def certificationModeIdentityVerticalProbe (profile : PolyProfile) :
    RawCertificationNegativeProbe profile where
  scope := defaultInferScope
  dimension := 1
  rawCell := modeIdentityVerticalRawCell profile
  expectedRejection := .unsupportedCertification

/-- Inference probes whose expected rejection is `unknownGenerator`. -/
def unknownGeneratorInferNegativeProbes (profile : PolyProfile) :
    List (RawInferNegativeProbe profile) :=
  [unknownGeneratorProbe profile,
    wrongRuleEndpointDimensionProbe profile]

/-- Inference probes whose expected rejection is `badPayload`. -/
def badPayloadInferNegativeProbes (profile : PolyProfile) :
    List (RawInferNegativeProbe profile) :=
  [outOfScopeVariableProbe profile,
    badPayloadProbe profile,
    badUnitTypePayloadProbe profile,
    badLinearModePayloadProbe profile,
    badPiTypePayloadProbe profile,
    badContextConsPayloadProbe profile,
    applicationBadPayloadProbe profile,
    badIdentityBaseProbe profile]

/-- Inference probes whose expected rejection is `wrongArity`. -/
def wrongArityInferNegativeProbes (profile : PolyProfile) :
    List (RawInferNegativeProbe profile) :=
  [wrongArityProbe profile,
    wrongPiTypeArityProbe profile,
    wrongContextConsArityProbe profile,
    applicationWrongArityProbe profile]

/-- Inference probes whose expected rejection is `wrongChildShape`. -/
def wrongChildShapeInferNegativeProbes (profile : PolyProfile) :
    List (RawInferNegativeProbe profile) :=
  [wrongChildShapeProbe profile,
    wrongPiTypeChildShapeProbe profile,
    wrongContextConsChildShapeProbe profile,
    applicationWrongChildShapeProbe profile,
    applicationTypeAsFunctionProbe profile,
    applicationTypeAsArgumentProbe profile,
    applicationOutOfScopeArgumentProbe profile,
    applicationModeAsFunctionProbe profile,
    applicationContextAsFunctionProbe profile,
    applicationModeAsArgumentProbe profile,
    applicationContextAsArgumentProbe profile]

/-- Inference probes whose expected rejection is `badBoundaryEndpoint`. -/
def badBoundaryEndpointInferNegativeProbes (profile : PolyProfile) :
    List (RawInferNegativeProbe profile) :=
  [badBoundaryEndpointProbe profile,
    badBoundarySortProbe profile,
    badBoundaryTypeSortProbe profile,
    badBoundaryModeSortProbe profile]

/-- Inference probes whose expected rejection is `badVerticalBoundary`. -/
def badVerticalBoundaryInferNegativeProbes (profile : PolyProfile) :
    List (RawInferNegativeProbe profile) :=
  [badVerticalBoundaryProbe profile]

/-- Inference probes whose expected rejection is `unsupportedCompH`. -/
def unsupportedCompHInferNegativeProbes (profile : PolyProfile) :
    List (RawInferNegativeProbe profile) :=
  [unsupportedCompHProbe profile,
    unsupportedCompHWellScreenedProbe profile]

/-- Expected-shape probes whose expected rejection is `wrongSort`. -/
def wrongSortExpectedShapeNegativeProbes (profile : PolyProfile) :
    List (RawExpectedShapeNegativeProbe profile) :=
  [wrongSortProbe profile,
    contextAsTypeProbe profile,
    unitTypeAsTermProbe profile,
    unitTypeAsContextProbe profile,
    termAsTypeProbe profile,
    termAsContextProbe profile,
    linearModeAsTermProbe profile,
    linearModeAsTypeProbe profile,
    typeIdentityAsTermStepProbe profile,
    applicationVarZeroVarOneAsTypeProbe profile,
    applicationVarZeroVarOneAsContextProbe profile,
    applicationVarZeroVarOneAsModeProbe profile]

/-- Expected-shape probes whose expected rejection is `badPayload`. -/
def badPayloadExpectedShapeNegativeProbes (profile : PolyProfile) :
    List (RawExpectedShapeNegativeProbe profile) :=
  [applicationBadPayloadExpectedShapeProbe profile]

/-- Expected-shape probes whose expected rejection is `wrongArity`. -/
def wrongArityExpectedShapeNegativeProbes (profile : PolyProfile) :
    List (RawExpectedShapeNegativeProbe profile) :=
  [applicationWrongArityExpectedShapeProbe profile]

/-- Expected-shape probes whose expected rejection is `wrongChildShape`. -/
def wrongChildShapeExpectedShapeNegativeProbes
    (profile : PolyProfile) :
    List (RawExpectedShapeNegativeProbe profile) :=
  [applicationWrongChildShapeExpectedShapeProbe profile]

/-- Certification probes preserving non-certification boundary failure. -/
def badBoundaryEndpointCertificationNegativeProbes
    (profile : PolyProfile) :
    List (RawCertificationNegativeProbe profile) :=
  [certificationBadBoundaryEndpointProbe profile]

/-- Certification probes preserving the absence of Gray semantics. -/
def unsupportedCompHCertificationNegativeProbes
    (profile : PolyProfile) :
    List (RawCertificationNegativeProbe profile) :=
  [certificationUnsupportedCompHProbe profile]

/-- Certification probes whose expected rejection is
`unsupportedCertification`. -/
def unsupportedCertificationNegativeProbes (profile : PolyProfile) :
    List (RawCertificationNegativeProbe profile) :=
  [certificationUnsupportedTermStepProbe profile,
    certificationUnsupportedReversedTermStepProbe profile,
    certificationUnsupportedReflexiveTermStepProbe profile,
    certificationMatchedVerticalBoundaryProbe profile,
    certificationTermIdentityProbe profile,
    certificationTypeIdentityProbe profile,
    certificationContextIdentityProbe profile,
    certificationModeIdentityProbe profile,
    certificationTermIdentityVerticalProbe profile,
    certificationTypeIdentityVerticalProbe profile,
    certificationContextIdentityVerticalProbe profile,
    certificationModeIdentityVerticalProbe profile]

/-- Fuel-budget probes whose expected rejection is `fuelExhausted`. -/
def fuelExhaustedNegativeProbes (profile : PolyProfile) :
    List (RawFuelNegativeProbe profile) :=
  [fuelExhaustedProbe profile]

/-- Inference probes, one for each inference-level rejection reason. -/
def inferNegativeProbes (profile : PolyProfile) :
    List (RawInferNegativeProbe profile) :=
  unknownGeneratorInferNegativeProbes profile ++
    badPayloadInferNegativeProbes profile ++
    wrongArityInferNegativeProbes profile ++
    wrongChildShapeInferNegativeProbes profile ++
    badBoundaryEndpointInferNegativeProbes profile ++
    badVerticalBoundaryInferNegativeProbes profile ++
    unsupportedCompHInferNegativeProbes profile

/-- Expected-shape probes for sort mismatches and screen-error pass-through. -/
def expectedShapeNegativeProbes (profile : PolyProfile) :
    List (RawExpectedShapeNegativeProbe profile) :=
  wrongSortExpectedShapeNegativeProbes profile ++
    badPayloadExpectedShapeNegativeProbes profile ++
    wrongArityExpectedShapeNegativeProbes profile ++
    wrongChildShapeExpectedShapeNegativeProbes profile

/-- Certified-ingress probes for screen-passing but unsupported raw cells. -/
def certificationNegativeProbes (profile : PolyProfile) :
    List (RawCertificationNegativeProbe profile) :=
  badBoundaryEndpointCertificationNegativeProbes profile ++
    unsupportedCompHCertificationNegativeProbes profile ++
    unsupportedCertificationNegativeProbes profile

/-- Inference probe count. -/
theorem inferNegativeProbes_length (profile : PolyProfile) :
    (inferNegativeProbes profile).length = 32 := rfl

/-- Expected-shape probe count. -/
theorem expectedShapeNegativeProbes_length (profile : PolyProfile) :
    (expectedShapeNegativeProbes profile).length = 15 := rfl

/-- Certified-ingress probe count. -/
theorem certificationNegativeProbes_length (profile : PolyProfile) :
    (certificationNegativeProbes profile).length = 14 := rfl

/-- Unknown-generator headline probe count. -/
theorem unknownGeneratorInferNegativeProbes_length
    (profile : PolyProfile) :
    (unknownGeneratorInferNegativeProbes profile).length = 2 := rfl

/-- Bad-payload headline probe count. -/
theorem badPayloadInferNegativeProbes_length (profile : PolyProfile) :
    (badPayloadInferNegativeProbes profile).length = 8 := rfl

/-- Wrong-arity headline probe count. -/
theorem wrongArityInferNegativeProbes_length (profile : PolyProfile) :
    (wrongArityInferNegativeProbes profile).length = 4 := rfl

/-- Wrong-child-shape headline probe count. -/
theorem wrongChildShapeInferNegativeProbes_length
    (profile : PolyProfile) :
    (wrongChildShapeInferNegativeProbes profile).length = 11 := rfl

/-- Bad-boundary-endpoint headline probe count. -/
theorem badBoundaryEndpointInferNegativeProbes_length
    (profile : PolyProfile) :
    (badBoundaryEndpointInferNegativeProbes profile).length = 4 := rfl

/-- Bad-vertical-boundary headline probe count. -/
theorem badVerticalBoundaryInferNegativeProbes_length
    (profile : PolyProfile) :
    (badVerticalBoundaryInferNegativeProbes profile).length = 1 := rfl

/-- Unsupported-horizontal-composition headline probe count. -/
theorem unsupportedCompHInferNegativeProbes_length
    (profile : PolyProfile) :
    (unsupportedCompHInferNegativeProbes profile).length = 2 := rfl

/-- Wrong-sort expected-shape headline probe count. -/
theorem wrongSortExpectedShapeNegativeProbes_length
    (profile : PolyProfile) :
    (wrongSortExpectedShapeNegativeProbes profile).length = 12 := rfl

/-- Bad-payload expected-shape headline probe count. -/
theorem badPayloadExpectedShapeNegativeProbes_length
    (profile : PolyProfile) :
    (badPayloadExpectedShapeNegativeProbes profile).length = 1 := rfl

/-- Wrong-arity expected-shape headline probe count. -/
theorem wrongArityExpectedShapeNegativeProbes_length
    (profile : PolyProfile) :
    (wrongArityExpectedShapeNegativeProbes profile).length = 1 := rfl

/-- Wrong-child-shape expected-shape headline probe count. -/
theorem wrongChildShapeExpectedShapeNegativeProbes_length
    (profile : PolyProfile) :
    (wrongChildShapeExpectedShapeNegativeProbes profile).length = 1 := rfl

/-- Certification bad-boundary-endpoint headline probe count. -/
theorem badBoundaryEndpointCertificationNegativeProbes_length
    (profile : PolyProfile) :
    (badBoundaryEndpointCertificationNegativeProbes profile).length = 1 := rfl

/-- Certification unsupported-horizontal-composition headline probe count. -/
theorem unsupportedCompHCertificationNegativeProbes_length
    (profile : PolyProfile) :
    (unsupportedCompHCertificationNegativeProbes profile).length = 1 := rfl

/-- Unsupported-certification headline probe count. -/
theorem unsupportedCertificationNegativeProbes_length
    (profile : PolyProfile) :
    (unsupportedCertificationNegativeProbes profile).length = 12 := rfl

/-- Fuel-exhaustion headline probe count. -/
theorem fuelExhaustedNegativeProbes_length
    (profile : PolyProfile) :
    (fuelExhaustedNegativeProbes profile).length = 1 := rfl

end NegativeProbes

end LeanFX2.Foundation.PolyCell.Core
