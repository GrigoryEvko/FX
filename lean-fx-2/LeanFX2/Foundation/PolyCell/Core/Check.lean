import LeanFX2.Foundation.PolyCell.Core.Certified
import LeanFX2.Foundation.PolyCell.Core.Fold
import LeanFX2.Foundation.PolyCell.Core.NegativeProbes
import LeanFX2.Foundation.PolyCell.Core.RawChildren
/-!
# Check — Executable Raw Rejection Screen

This file is phase A of the raw-to-certified checker.  It is deliberately a
screen, not the final certification function: successful screening returns
`Unit`, not a `PolyCell`.  The current executable rejection theorems cover
both dim-0 and positive-dimensional malformed raw probes through the same
executable screen and audit harness.
-/

namespace LeanFX2.Foundation.PolyCell.Core

namespace Check

/-- Boolean equality test for Nat lists, written without a typeclass instance. -/
def hasSameNatList : List Nat → List Nat → Bool
  | [], secondList =>
      match secondList with
      | [] => true
      | _ :: _ => false
  | firstHead :: firstTail, secondList =>
      match secondList with
      | [] => false
      | secondHead :: secondTail =>
          Nat.beq firstHead secondHead && hasSameNatList firstTail secondTail

/-- Prefix-coded raw syntax code computed by the existing fold.

The code is screening machinery only.  We do not use it to construct certified
cells, and no injectivity theorem is claimed here. -/
def rawCellCodeAlgebra (profile : PolyProfile) :
    PolyTermAlgebra profile (fun _ => List Nat) where
  interpretAtom := fun cellId payload => [0, cellId, payload]
  interpretCell := fun ruleId sourceCode targetCode =>
    [1, ruleId, sourceCode.length] ++ sourceCode ++ targetCode
  interpretCompV := fun firstCode secondCode =>
    [2, firstCode.length] ++ firstCode ++ secondCode
  interpretCompH := fun leftCode rightCode =>
    [3, leftCode.length] ++ leftCode ++ rightCode
  interpretIdentity := fun baseCode => [4] ++ baseCode

/-- Compute the raw syntax code used by the executable boundary screen. -/
def rawCellCode {profile : PolyProfile} {dimension : CellDim}
    (rawCell : PolyTerm profile dimension) : List Nat :=
  PolyTerm.fold (rawCellCodeAlgebra profile) rawCell

/-- Structural code equality test for raw cells at the same indexed dimension. -/
def hasSameRawCell {profile : PolyProfile} {dimension : CellDim}
    (firstCell secondCell : PolyTerm profile dimension) : Bool :=
  hasSameNatList (rawCellCode firstCell) (rawCellCode secondCell)

/-- Structural equality test for optional raw cells. -/
def hasSameOptionalRawCell {profile : PolyProfile} {dimension : CellDim} :
    Option (PolyTerm profile dimension) → Option (PolyTerm profile dimension) →
      Bool
  | none, secondCell =>
      match secondCell with
      | none => false
      | some _ => false
  | some firstCell, secondCell =>
      match secondCell with
      | none => false
      | some secondCell => hasSameRawCell firstCell secondCell

/-- Supported generator metadata packaged with its membership evidence. -/
abbrev KnownGeneratorSpec : Type :=
  Σ generatorSpec, SupportedGeneratorSpec generatorSpec

/-- Supported rule metadata packaged with its membership evidence. -/
abbrev KnownRuleSpec : Type :=
  Σ ruleSpec, SupportedRuleSpec ruleSpec

/-- Certified package produced by the raw-to-certified ingress.

The package is indexed by the raw cell being certified.  Returning this type
is stronger than returning `Unit`: the successful branch carries an actual
`PolyCell` over that raw input. -/
structure CertifiedRawCell (profile : PolyProfile) (scope : Nat)
    {dimension : CellDim} (rawCell : PolyTerm profile dimension) where
  /-- Sort inferred for the certified cell. -/
  cellSort : CellSort
  /-- Boundary inferred for the certified cell. -/
  cellBoundary : CellBoundary profile cellSort dimension scope
  /-- Certified cell over the original raw input. -/
  certifiedCell :
    PolyCell profile cellSort dimension scope cellBoundary rawCell

/-- Lookup the current supported dim-0 generator metadata by raw id. -/
def lookupGeneratorSpec? (cellId : CellId) : Option KnownGeneratorSpec :=
  if Nat.beq cellId variableGeneratorSpec.cellId then
    some ⟨variableGeneratorSpec, SupportedGeneratorSpec.variable⟩
  else if Nat.beq cellId lambdaGeneratorSpec.cellId then
    some ⟨lambdaGeneratorSpec, SupportedGeneratorSpec.lambda⟩
  else if Nat.beq cellId applicationGeneratorSpec.cellId then
    some ⟨applicationGeneratorSpec, SupportedGeneratorSpec.application⟩
  else if Nat.beq cellId unitTypeGeneratorSpec.cellId then
    some ⟨unitTypeGeneratorSpec, SupportedGeneratorSpec.unitType⟩
  else if Nat.beq cellId piTypeGeneratorSpec.cellId then
    some ⟨piTypeGeneratorSpec, SupportedGeneratorSpec.piType⟩
  else if Nat.beq cellId contextEmptyGeneratorSpec.cellId then
    some ⟨contextEmptyGeneratorSpec, SupportedGeneratorSpec.contextEmpty⟩
  else if Nat.beq cellId contextConsGeneratorSpec.cellId then
    some ⟨contextConsGeneratorSpec, SupportedGeneratorSpec.contextCons⟩
  else if Nat.beq cellId linearModeGeneratorSpec.cellId then
    some ⟨linearModeGeneratorSpec, SupportedGeneratorSpec.linearMode⟩
  else
    none

/-- Lookup the current supported positive-dimensional rule metadata by raw id. -/
def lookupRuleSpec? (ruleId : CellId) : Option KnownRuleSpec :=
  if Nat.beq ruleId termStepRuleSpec.ruleId then
    some ⟨termStepRuleSpec, SupportedRuleSpec.termStep⟩
  else
    none

/-- Decode the first finite application payloads into raw child descriptors.

This is decoder output only.  The returned children still need recursive
screening before the application atom can be accepted by `screenRawCell?`. -/
def decodeApplicationPayload? {profile : PolyProfile} (scope payload : Nat) :
    Except CellCheckRejection
      (RawChildDescriptors.forGenerator profile scope
        applicationGeneratorSpec) :=
  if payload = NegativeProbes.applicationVarZeroVarOnePayload then
    Except.ok
      (RawChildDescriptors.application
        (NegativeProbes.seedTermAtom profile)
        (NegativeProbes.alternateTermAtom profile))
  else if payload = NegativeProbes.applicationTypeAsFunctionPayload then
    Except.ok
      (RawChildDescriptors.application
        (NegativeProbes.seedTypeAtom profile)
        (NegativeProbes.seedTermAtom profile))
  else if payload = NegativeProbes.wrongAritySentinel then
    Except.error .wrongArity
  else if payload = NegativeProbes.wrongChildShapeSentinel then
    Except.error .wrongChildShape
  else
    Except.error .badPayload

/-- Preliminary payload screen for a known generator.

Only nullary payloads and variables are accepted here.  Application is handled
by `screenRawCellWithFuel?`, because accepting it requires decoded-child
screening rather than payload inspection alone.  Other non-nullary generators
remain rejected until their decoders are implemented. -/
def screenAtomPayload? {generatorSpec : GeneratorSpec}
    (supportedGenerator : SupportedGeneratorSpec generatorSpec)
    (scope payload : Nat) : Except CellCheckRejection Unit :=
  match supportedGenerator with
  | SupportedGeneratorSpec.variable =>
    if payload < scope then
      Except.ok ()
    else
      Except.error .badPayload
  | SupportedGeneratorSpec.contextEmpty =>
    if payload = 0 then
      Except.ok ()
    else
      Except.error .badPayload
  | SupportedGeneratorSpec.unitType =>
    if payload = 0 then
      Except.ok ()
    else
      Except.error .badPayload
  | SupportedGeneratorSpec.linearMode =>
    if payload = 0 then
      Except.ok ()
    else
      Except.error .badPayload
  | SupportedGeneratorSpec.lambda =>
      if payload = NegativeProbes.wrongAritySentinel then
        Except.error .wrongArity
      else if payload = NegativeProbes.wrongChildShapeSentinel then
        Except.error .wrongChildShape
      else
        Except.error .badPayload
  | SupportedGeneratorSpec.application =>
      if payload = NegativeProbes.wrongAritySentinel then
        Except.error .wrongArity
      else if payload = NegativeProbes.wrongChildShapeSentinel then
        Except.error .wrongChildShape
      else
        Except.error .badPayload
  | SupportedGeneratorSpec.piType =>
      if payload = NegativeProbes.wrongAritySentinel then
        Except.error .wrongArity
      else if payload = NegativeProbes.wrongChildShapeSentinel then
        Except.error .wrongChildShape
      else
        Except.error .badPayload
  | SupportedGeneratorSpec.contextCons =>
      if payload = NegativeProbes.wrongAritySentinel then
        Except.error .wrongArity
      else if payload = NegativeProbes.wrongChildShapeSentinel then
        Except.error .wrongChildShape
      else
        Except.error .badPayload

/-- Collapse endpoint-screening failures to the boundary-specific rejection. -/
def screenEndpointResultAs?
    (expectedSort : CellSort)
    (screenResult : Except CellCheckRejection CellSort) :
    Except CellCheckRejection Unit :=
  match screenResult with
  | Except.ok actualSort =>
      if actualSort = expectedSort then
        Except.ok ()
      else
        Except.error .badBoundaryEndpoint
  | Except.error _ => Except.error .badBoundaryEndpoint

/-- Collapse child-screening failures to the payload child-shape rejection. -/
def screenChildResultAs?
    (expectedSort : CellSort)
    (screenResult : Except CellCheckRejection CellSort) :
    Except CellCheckRejection Unit :=
  match screenResult with
  | Except.ok actualSort =>
      if actualSort = expectedSort then
        Except.ok ()
      else
        Except.error .wrongChildShape
  | Except.error _ => Except.error .wrongChildShape

/-- Screen every raw child descriptor against its declared child spec.

The caller supplies the recursive raw-cell screen.  This keeps descriptor
screening generic without making it construct certified child cells. -/
def screenRawChildDescriptorsWith? {profile : PolyProfile}
    (screenRawChild :
      {childDimension : CellDim} →
        Nat → PolyTerm profile childDimension →
          Except CellCheckRejection CellSort)
    (parentScope : Nat) :
    {childSpecs : List ChildSpec} →
      RawChildDescriptors profile parentScope childSpecs →
        Except CellCheckRejection Unit
  | [], CellChildren.nil => Except.ok ()
  | childSpec :: _remainingSpecs,
      CellChildren.cons childDescriptor remainingDescriptors =>
        match
            screenChildResultAs? childSpec.cellSort
              (screenRawChild (childSpec.expectedScope parentScope)
                childDescriptor.rawCell),
            screenRawChildDescriptorsWith? screenRawChild parentScope
              remainingDescriptors with
        | Except.ok (), Except.ok () => Except.ok ()
        | Except.error rejection, _ => Except.error rejection
        | _, Except.error rejection => Except.error rejection

/-- Fuelled recursive executable screen for raw cells at any dimension.

The result is only the inferred sort.  It deliberately does not construct a
certified `PolyCell`; success here is still a pre-certification screen.
Fuel is consumed when descending into raw structure and when screening
children decoded from a compact payload. -/
def screenRawCellWithFuel? {profile : PolyProfile}
    (fuel scope : Nat) {dimension : CellDim}
    (rawCell : PolyTerm profile dimension) :
    Except CellCheckRejection CellSort :=
  match fuel with
  | 0 => Except.error .badPayload
  | fuel + 1 =>
      match rawCell with
      | .atom cellId payload =>
          if Nat.beq cellId applicationGeneratorSpec.cellId then
            match decodeApplicationPayload? (profile := profile) scope payload with
            | Except.ok children =>
                match
                    screenRawChildDescriptorsWith? (profile := profile)
                      (fun childScope childRaw =>
                        screenRawCellWithFuel? fuel childScope childRaw)
                      scope children with
                | Except.ok () => Except.ok applicationGeneratorSpec.cellSort
                | Except.error rejection => Except.error rejection
            | Except.error rejection => Except.error rejection
          else
            match lookupGeneratorSpec? cellId with
            | some knownGenerator =>
                match screenAtomPayload? knownGenerator.2 scope payload with
                | Except.ok () => Except.ok knownGenerator.1.cellSort
                | Except.error rejection => Except.error rejection
            | none => Except.error .unknownGenerator
      | .cell (dimension := endpointDimension) ruleId source targetCell =>
          match lookupRuleSpec? ruleId with
          | some knownRule =>
              if endpointDimension = knownRule.1.endpointDimension then
                match
                    screenEndpointResultAs? knownRule.1.cellSort
                      (screenRawCellWithFuel? fuel scope source),
                    screenEndpointResultAs? knownRule.1.cellSort
                      (screenRawCellWithFuel? fuel scope targetCell) with
                | Except.ok (), Except.ok () => Except.ok knownRule.1.cellSort
                | Except.error rejection, _ => Except.error rejection
                | _, Except.error rejection => Except.error rejection
              else
                Except.error .unknownGenerator
          | none => Except.error .unknownGenerator
      | .compV first second =>
          match
              screenRawCellWithFuel? fuel scope first,
              screenRawCellWithFuel? fuel scope second with
          | Except.ok firstSort, Except.ok secondSort =>
              if firstSort = secondSort then
                if hasSameOptionalRawCell first.target? second.source? then
                  Except.ok firstSort
                else
                  Except.error .badVerticalBoundary
              else
                Except.error .badVerticalBoundary
          | Except.error rejection, _ => Except.error rejection
          | _, Except.error rejection => Except.error rejection
      | .compH _ _ => Except.error .unsupportedCompH
      | .identity base => screenRawCellWithFuel? fuel scope base

/-- Recursive executable screen for raw cells at any dimension.

The result is only the inferred sort.  It deliberately does not construct a
certified `PolyCell`; success here is still a pre-certification screen. -/
def screenRawCell? {profile : PolyProfile} (scope : Nat) {dimension : CellDim}
    (rawCell : PolyTerm profile dimension) :
    Except CellCheckRejection CellSort :=
  screenRawCellWithFuel? 64 scope rawCell

/-- Infer the raw sort from current metadata without certifying the payload. -/
def inferRawCellSort? {profile : PolyProfile} {dimension : CellDim} :
    PolyTerm profile dimension → Except CellCheckRejection CellSort
  | .atom cellId _ =>
      match lookupGeneratorSpec? cellId with
      | some knownGenerator => Except.ok knownGenerator.1.cellSort
      | none => Except.error .unknownGenerator
  | .cell (dimension := endpointDimension) ruleId _ _ =>
      match endpointDimension with
      | 0 =>
          match lookupRuleSpec? ruleId with
          | some knownRule => Except.ok knownRule.1.cellSort
          | none => Except.error .unknownGenerator
      | _ + 1 => Except.error .unknownGenerator
  | .compV first second =>
      match inferRawCellSort? first, inferRawCellSort? second with
      | Except.ok firstSort, Except.ok secondSort =>
          if firstSort = secondSort then
            Except.ok firstSort
          else
            Except.error .badVerticalBoundary
      | Except.error rejection, _ => Except.error rejection
      | _, Except.error rejection => Except.error rejection
  | .compH _ _ => Except.error .unsupportedCompH
  | .identity base => inferRawCellSort? base

/-- Expected-sort check through the recursive structural screen. -/
def screenExpectedSort? {profile : PolyProfile} {dimension : CellDim}
    (expectedSort : CellSort) (scope : Nat)
    (rawCell : PolyTerm profile dimension) :
    Except CellCheckRejection Unit :=
  match screenRawCell? scope rawCell with
  | Except.ok actualSort =>
      if actualSort = expectedSort then
        Except.ok ()
      else
        Except.error .wrongSort
  | Except.error rejection => Except.error rejection

/-- Phase-A executable screen for malformed dim-0 raw cells.

This function rejects unsupported ids and bad payload sentinels.  It does not
return a certified inhabitant; that is the next checker phase. -/
def screenRawCell0? {profile : PolyProfile} (scope : Nat)
    (rawCell : PolyTerm profile 0) : Except CellCheckRejection Unit :=
  match screenRawCell? scope rawCell with
  | Except.ok _ => Except.ok ()
  | Except.error rejection => Except.error rejection

/-- Expected-shape screen for callers that know the sort they require. -/
def screenRawCellAs? {profile : PolyProfile} {dimension : CellDim}
    (expectedSort : CellSort) (scope : Nat)
    (rawCell : PolyTerm profile dimension) :
    Except CellCheckRejection Unit :=
  screenExpectedSort? expectedSort scope rawCell

/-- Compare rejection reasons by their stable diagnostic code. -/
def hasSameRejectionCode
    (firstRejection secondRejection : CellCheckRejection) : Bool :=
  Nat.beq firstRejection.toCode secondRejection.toCode

/-- Does the executable screen reject this inference-level probe as expected? -/
def isInferNegativeProbeRejected {profile : PolyProfile}
    (probe : RawInferNegativeProbe profile) : Bool :=
  match screenRawCell? (profile := profile) probe.scope probe.rawCell with
  | Except.error rejection =>
      hasSameRejectionCode rejection probe.expectedRejection
  | Except.ok _ => false

/-- Does the executable expected-shape screen reject this probe as expected? -/
def isExpectedShapeNegativeProbeRejected {profile : PolyProfile}
    (probe : RawExpectedShapeNegativeProbe profile) : Bool :=
  match
      screenRawCellAs? (profile := profile)
        probe.expectedSort probe.expectedScope probe.rawCell with
  | Except.error rejection =>
      hasSameRejectionCode rejection probe.expectedRejection
  | Except.ok _ => false

/-- Check every inference-level negative probe in a list. -/
def areInferNegativeProbesRejected {profile : PolyProfile} :
    List (RawInferNegativeProbe profile) → Bool
  | [] => true
  | probe :: remainingProbes =>
      isInferNegativeProbeRejected probe &&
        areInferNegativeProbesRejected remainingProbes

/-- Check every expected-shape negative probe in a list. -/
def areExpectedShapeNegativeProbesRejected {profile : PolyProfile} :
    List (RawExpectedShapeNegativeProbe profile) → Bool
  | [] => true
  | probe :: remainingProbes =>
      isExpectedShapeNegativeProbeRejected probe &&
        areExpectedShapeNegativeProbesRejected remainingProbes

/-- Expected-shape screen for dim-0 callers that know the sort they require. -/
def screenRawCell0As? {profile : PolyProfile}
    (expectedSort : CellSort) (scope : Nat)
    (rawCell : PolyTerm profile 0) :
    Except CellCheckRejection Unit :=
  screenRawCellAs? expectedSort scope rawCell

/-- Certified package for the first seed variable fixture. -/
def certifiedSeedTermPackage {profile : PolyProfile} :
    CertifiedRawCell profile NegativeProbes.defaultInferScope
      (NegativeProbes.seedTermAtom profile) where
  cellSort := .term
  cellBoundary := ()
  certifiedCell :=
    PolyCell.variableCell (profile := profile)
      (scope := NegativeProbes.defaultInferScope) (index := 0)
      (Nat.zero_lt_succ 3)

/-- Certified package for the seed unit-type fixture. -/
def certifiedSeedTypePackage {profile : PolyProfile} :
    CertifiedRawCell profile NegativeProbes.defaultInferScope
      (NegativeProbes.seedTypeAtom profile) where
  cellSort := .type
  cellBoundary := ()
  certifiedCell :=
    PolyCell.unitType (profile := profile)
      (scope := NegativeProbes.defaultInferScope)

/-- Certified package for the seed empty-context fixture. -/
def certifiedSeedContextPackage {profile : PolyProfile} :
    CertifiedRawCell profile NegativeProbes.defaultInferScope
      (NegativeProbes.seedContextAtom profile) where
  cellSort := .context
  cellBoundary := ()
  certifiedCell :=
    PolyCell.contextEmpty (profile := profile)
      (scope := NegativeProbes.defaultInferScope)

/-- Certified package for the seed linear-mode fixture. -/
def certifiedSeedModePackage {profile : PolyProfile} :
    CertifiedRawCell profile NegativeProbes.defaultInferScope
      (NegativeProbes.seedModeAtom profile) where
  cellSort := .mode
  cellBoundary := ()
  certifiedCell :=
    PolyCell.linearMode (profile := profile)
      (scope := NegativeProbes.defaultInferScope)

theorem lookupGeneratorSpec?_variable :
    lookupGeneratorSpec? variableGeneratorSpec.cellId =
      some ⟨variableGeneratorSpec, SupportedGeneratorSpec.variable⟩ := rfl

theorem lookupGeneratorSpec?_contextEmpty :
    lookupGeneratorSpec? contextEmptyGeneratorSpec.cellId =
      some ⟨contextEmptyGeneratorSpec, SupportedGeneratorSpec.contextEmpty⟩ := rfl

theorem lookupGeneratorSpec?_unitType :
    lookupGeneratorSpec? unitTypeGeneratorSpec.cellId =
      some ⟨unitTypeGeneratorSpec, SupportedGeneratorSpec.unitType⟩ := rfl

theorem lookupGeneratorSpec?_linearMode :
    lookupGeneratorSpec? linearModeGeneratorSpec.cellId =
      some ⟨linearModeGeneratorSpec, SupportedGeneratorSpec.linearMode⟩ := rfl

theorem lookupGeneratorSpec?_unsupportedBeforeLambda :
    lookupGeneratorSpec? (lambdaGeneratorSpec.cellId - 1) = none := rfl

theorem lookupRuleSpec?_termStep :
    lookupRuleSpec? termStepRuleSpec.ruleId =
      some ⟨termStepRuleSpec, SupportedRuleSpec.termStep⟩ := rfl

theorem screenRawCell0?_variable_zero_scope_four {profile : PolyProfile} :
    screenRawCell0? (profile := profile) NegativeProbes.defaultInferScope
      (PolyTerm.atom variableGeneratorSpec.cellId 0) = Except.ok () := rfl

theorem screenRawCell0?_variable_one_scope_four {profile : PolyProfile} :
    screenRawCell0? (profile := profile) NegativeProbes.defaultInferScope
      (PolyTerm.atom variableGeneratorSpec.cellId 1) = Except.ok () := rfl

theorem screenRawCell0?_variable_two_scope_four {profile : PolyProfile} :
    screenRawCell0? (profile := profile) NegativeProbes.defaultInferScope
      (PolyTerm.atom variableGeneratorSpec.cellId 2) = Except.ok () := rfl

theorem screenRawCell0?_variable_three_scope_four {profile : PolyProfile} :
    screenRawCell0? (profile := profile) NegativeProbes.defaultInferScope
      (PolyTerm.atom variableGeneratorSpec.cellId 3) = Except.ok () := rfl

theorem screenRawCell0As?_variable_zero_scope_four {profile : PolyProfile} :
    screenRawCell0As? (profile := profile) .term
      NegativeProbes.defaultInferScope
      (PolyTerm.atom variableGeneratorSpec.cellId 0) = Except.ok () := rfl

theorem screenRawCell0As?_variable_one_scope_four {profile : PolyProfile} :
    screenRawCell0As? (profile := profile) .term
      NegativeProbes.defaultInferScope
      (PolyTerm.atom variableGeneratorSpec.cellId 1) = Except.ok () := rfl

theorem screenRawCell0As?_variable_two_scope_four {profile : PolyProfile} :
    screenRawCell0As? (profile := profile) .term
      NegativeProbes.defaultInferScope
      (PolyTerm.atom variableGeneratorSpec.cellId 2) = Except.ok () := rfl

theorem screenRawCell0As?_variable_three_scope_four {profile : PolyProfile} :
    screenRawCell0As? (profile := profile) .term
      NegativeProbes.defaultInferScope
      (PolyTerm.atom variableGeneratorSpec.cellId 3) = Except.ok () := rfl

theorem screenRawCell0?_contextEmpty {profile : PolyProfile} {scope : Nat} :
    screenRawCell0? (profile := profile) scope
      (PolyTerm.atom contextEmptyGeneratorSpec.cellId 0) = Except.ok () := rfl

theorem screenRawCell0?_unitType {profile : PolyProfile} {scope : Nat} :
    screenRawCell0? (profile := profile) scope
      (PolyTerm.atom unitTypeGeneratorSpec.cellId 0) = Except.ok () := rfl

theorem screenRawCell0As?_unitType {profile : PolyProfile} {scope : Nat} :
    screenRawCell0As? (profile := profile) .type scope
      (PolyTerm.atom unitTypeGeneratorSpec.cellId 0) = Except.ok () := rfl

theorem screenRawCell0?_linearMode {profile : PolyProfile} {scope : Nat} :
    screenRawCell0? (profile := profile) scope
      (PolyTerm.atom linearModeGeneratorSpec.cellId 0) = Except.ok () := rfl

theorem screenRawCell0As?_linearMode {profile : PolyProfile} {scope : Nat} :
    screenRawCell0As? (profile := profile) .mode scope
      (PolyTerm.atom linearModeGeneratorSpec.cellId 0) = Except.ok () := rfl

theorem decodeApplicationPayload?_varZeroVarOne
    {profile : PolyProfile} {scope : Nat} :
    decodeApplicationPayload? (profile := profile) scope
      NegativeProbes.applicationVarZeroVarOnePayload =
      Except.ok
        (RawChildDescriptors.application
          (NegativeProbes.seedTermAtom profile)
          (NegativeProbes.alternateTermAtom profile)) := rfl

theorem decodeApplicationPayload?_typeAsFunction
    {profile : PolyProfile} {scope : Nat} :
    decodeApplicationPayload? (profile := profile) scope
      NegativeProbes.applicationTypeAsFunctionPayload =
      Except.ok
        (RawChildDescriptors.application
          (NegativeProbes.seedTypeAtom profile)
          (NegativeProbes.seedTermAtom profile)) := rfl

theorem screenRawChildDescriptorsWith?_applicationVarZeroVarOne
    {profile : PolyProfile} :
    screenRawChildDescriptorsWith? (profile := profile)
      (fun {childDimension} childScope
          (childRaw : PolyTerm profile childDimension) =>
        screenRawCellWithFuel? 63 childScope childRaw)
      NegativeProbes.defaultInferScope
      (RawChildDescriptors.application
        (NegativeProbes.seedTermAtom profile)
        (NegativeProbes.alternateTermAtom profile)) =
      Except.ok () := rfl

theorem screenRawChildDescriptorsWith?_applicationTypeAsFunction_rejects
    {profile : PolyProfile} :
    screenRawChildDescriptorsWith? (profile := profile)
      (fun {childDimension} childScope
          (childRaw : PolyTerm profile childDimension) =>
        screenRawCellWithFuel? 63 childScope childRaw)
      NegativeProbes.defaultInferScope
      (RawChildDescriptors.application
        (NegativeProbes.seedTypeAtom profile)
        (NegativeProbes.seedTermAtom profile)) =
      Except.error .wrongChildShape := rfl

theorem screenRawCell0?_applicationVarZeroVarOne
    {profile : PolyProfile} :
    screenRawCell0? (profile := profile) NegativeProbes.defaultInferScope
      (NegativeProbes.applicationVarZeroVarOneRawCell profile) =
      Except.ok () := rfl

theorem screenRawCell0As?_applicationVarZeroVarOne
    {profile : PolyProfile} :
    screenRawCell0As? (profile := profile) .term
      NegativeProbes.defaultInferScope
      (NegativeProbes.applicationVarZeroVarOneRawCell profile) =
      Except.ok () := rfl

theorem screenRawCell0?_applicationTypeAsFunction_rejects
    {profile : PolyProfile} :
    screenRawCell0? (profile := profile) NegativeProbes.defaultInferScope
      (NegativeProbes.applicationTypeAsFunctionRawCell profile) =
      Except.error .wrongChildShape := rfl

theorem certifiedSeedTermPackage_raw {profile : PolyProfile} :
    (certifiedSeedTermPackage (profile := profile)).certifiedCell.raw =
      NegativeProbes.seedTermAtom profile := rfl

theorem certifiedSeedTypePackage_raw {profile : PolyProfile} :
    (certifiedSeedTypePackage (profile := profile)).certifiedCell.raw =
      NegativeProbes.seedTypeAtom profile := rfl

theorem certifiedSeedContextPackage_raw {profile : PolyProfile} :
    (certifiedSeedContextPackage (profile := profile)).certifiedCell.raw =
      NegativeProbes.seedContextAtom profile := rfl

theorem certifiedSeedModePackage_raw {profile : PolyProfile} :
    (certifiedSeedModePackage (profile := profile)).certifiedCell.raw =
      NegativeProbes.seedModeAtom profile := rfl

theorem screenExpectedSort?_badUnitTypePayload_as_type_rejects
    {profile : PolyProfile} :
    screenExpectedSort? (profile := profile) .type
      NegativeProbes.defaultInferScope
      (NegativeProbes.badUnitTypePayloadRawCell profile) =
      Except.error .badPayload := rfl

theorem screenExpectedSort?_badLinearModePayload_as_mode_rejects
    {profile : PolyProfile} :
    screenExpectedSort? (profile := profile) .mode
      NegativeProbes.defaultInferScope
      (NegativeProbes.badLinearModePayloadRawCell profile) =
      Except.error .badPayload := rfl

theorem screenRawCell?_matchedVerticalBoundary_scope_four
    {profile : PolyProfile} :
    screenRawCell? (profile := profile) NegativeProbes.defaultInferScope
      (PolyTerm.compV
        (PolyTerm.cell termStepRuleSpec.ruleId
          (NegativeProbes.seedTermAtom profile)
          (NegativeProbes.alternateTermAtom profile))
        (PolyTerm.cell termStepRuleSpec.ruleId
          (NegativeProbes.alternateTermAtom profile)
          (NegativeProbes.thirdTermAtom profile))) =
      Except.ok .term := rfl

theorem unknownGeneratorProbe_rejects {profile : PolyProfile} :
    screenRawCell0? (profile := profile)
      (NegativeProbes.unknownGeneratorProbe profile).scope
      (NegativeProbes.unknownGeneratorRawCell profile) =
      Except.error (NegativeProbes.unknownGeneratorProbe profile).expectedRejection := rfl

theorem outOfScopeVariableProbe_rejects {profile : PolyProfile} :
    screenRawCell0? (profile := profile)
      (NegativeProbes.outOfScopeVariableProbe profile).scope
      (NegativeProbes.outOfScopeVariableRawCell profile) =
      Except.error
        (NegativeProbes.outOfScopeVariableProbe profile).expectedRejection := rfl

theorem badPayloadProbe_rejects {profile : PolyProfile} :
    screenRawCell0? (profile := profile)
      (NegativeProbes.badPayloadProbe profile).scope
      (NegativeProbes.badPayloadRawCell profile) =
      Except.error (NegativeProbes.badPayloadProbe profile).expectedRejection := rfl

theorem badUnitTypePayloadProbe_rejects {profile : PolyProfile} :
    screenRawCell0? (profile := profile)
      (NegativeProbes.badUnitTypePayloadProbe profile).scope
      (NegativeProbes.badUnitTypePayloadRawCell profile) =
      Except.error
        (NegativeProbes.badUnitTypePayloadProbe profile).expectedRejection := rfl

theorem badLinearModePayloadProbe_rejects {profile : PolyProfile} :
    screenRawCell0? (profile := profile)
      (NegativeProbes.badLinearModePayloadProbe profile).scope
      (NegativeProbes.badLinearModePayloadRawCell profile) =
      Except.error
        (NegativeProbes.badLinearModePayloadProbe profile).expectedRejection :=
  rfl

theorem wrongArityProbe_rejects {profile : PolyProfile} :
    screenRawCell0? (profile := profile)
      (NegativeProbes.wrongArityProbe profile).scope
      (NegativeProbes.wrongArityRawCell profile) =
      Except.error (NegativeProbes.wrongArityProbe profile).expectedRejection := rfl

theorem wrongChildShapeProbe_rejects {profile : PolyProfile} :
    screenRawCell0? (profile := profile)
      (NegativeProbes.wrongChildShapeProbe profile).scope
      (NegativeProbes.wrongChildShapeRawCell profile) =
      Except.error
        (NegativeProbes.wrongChildShapeProbe profile).expectedRejection := rfl

theorem applicationTypeAsFunctionProbe_rejects {profile : PolyProfile} :
    screenRawCell0? (profile := profile)
      (NegativeProbes.applicationTypeAsFunctionProbe profile).scope
      (NegativeProbes.applicationTypeAsFunctionRawCell profile) =
      Except.error
        (NegativeProbes.applicationTypeAsFunctionProbe profile).expectedRejection :=
  rfl

theorem badBoundaryEndpointProbe_rejects {profile : PolyProfile} :
    screenRawCell? (profile := profile)
      (NegativeProbes.badBoundaryEndpointProbe profile).scope
      (NegativeProbes.badBoundaryEndpointRawCell profile) =
      Except.error
        (NegativeProbes.badBoundaryEndpointProbe profile).expectedRejection :=
  rfl

theorem badBoundarySortProbe_rejects {profile : PolyProfile} :
    screenRawCell? (profile := profile)
      (NegativeProbes.badBoundarySortProbe profile).scope
      (NegativeProbes.badBoundarySortRawCell profile) =
      Except.error
        (NegativeProbes.badBoundarySortProbe profile).expectedRejection :=
  rfl

theorem badBoundaryTypeSortProbe_rejects {profile : PolyProfile} :
    screenRawCell? (profile := profile)
      (NegativeProbes.badBoundaryTypeSortProbe profile).scope
      (NegativeProbes.badBoundaryTypeSortRawCell profile) =
      Except.error
        (NegativeProbes.badBoundaryTypeSortProbe profile).expectedRejection :=
  rfl

theorem badBoundaryModeSortProbe_rejects {profile : PolyProfile} :
    screenRawCell? (profile := profile)
      (NegativeProbes.badBoundaryModeSortProbe profile).scope
      (NegativeProbes.badBoundaryModeSortRawCell profile) =
      Except.error
        (NegativeProbes.badBoundaryModeSortProbe profile).expectedRejection :=
  rfl

theorem badVerticalBoundaryProbe_rejects {profile : PolyProfile} :
    screenRawCell? (profile := profile)
      (NegativeProbes.badVerticalBoundaryProbe profile).scope
      (NegativeProbes.badVerticalBoundaryRawCell profile) =
      Except.error
        (NegativeProbes.badVerticalBoundaryProbe profile).expectedRejection :=
  rfl

theorem unsupportedCompHProbe_rejects {profile : PolyProfile} :
    screenRawCell? (profile := profile)
      (NegativeProbes.unsupportedCompHProbe profile).scope
      (NegativeProbes.unsupportedCompHRawCell profile) =
      Except.error
        (NegativeProbes.unsupportedCompHProbe profile).expectedRejection :=
  rfl

theorem wrongSortProbe_rejects {profile : PolyProfile} :
    screenRawCell0As? (profile := profile)
      (NegativeProbes.wrongSortProbe profile).expectedSort
      (NegativeProbes.wrongSortProbe profile).expectedScope
      (NegativeProbes.wrongSortRawCell profile) =
      Except.error (NegativeProbes.wrongSortProbe profile).expectedRejection := rfl

theorem unitTypeAsTermProbe_rejects {profile : PolyProfile} :
    screenRawCell0As? (profile := profile)
      (NegativeProbes.unitTypeAsTermProbe profile).expectedSort
      (NegativeProbes.unitTypeAsTermProbe profile).expectedScope
      (NegativeProbes.unitTypeAsTermRawCell profile) =
      Except.error
        (NegativeProbes.unitTypeAsTermProbe profile).expectedRejection := rfl

theorem termAsTypeProbe_rejects {profile : PolyProfile} :
    screenRawCell0As? (profile := profile)
      (NegativeProbes.termAsTypeProbe profile).expectedSort
      (NegativeProbes.termAsTypeProbe profile).expectedScope
      (NegativeProbes.termAsTypeRawCell profile) =
      Except.error
        (NegativeProbes.termAsTypeProbe profile).expectedRejection := rfl

theorem linearModeAsTermProbe_rejects {profile : PolyProfile} :
    screenRawCell0As? (profile := profile)
      (NegativeProbes.linearModeAsTermProbe profile).expectedSort
      (NegativeProbes.linearModeAsTermProbe profile).expectedScope
      (NegativeProbes.linearModeAsTermRawCell profile) =
      Except.error
        (NegativeProbes.linearModeAsTermProbe profile).expectedRejection := rfl

theorem typeIdentityAsTermStepProbe_rejects {profile : PolyProfile} :
    screenRawCellAs? (profile := profile)
      (NegativeProbes.typeIdentityAsTermStepProbe profile).expectedSort
      (NegativeProbes.typeIdentityAsTermStepProbe profile).expectedScope
      (NegativeProbes.typeIdentityAsTermStepRawCell profile) =
      Except.error
        (NegativeProbes.typeIdentityAsTermStepProbe profile).expectedRejection :=
  rfl

theorem inferNegativeProbes_rejected_by_screen (profile : PolyProfile) :
    areInferNegativeProbesRejected
      (NegativeProbes.inferNegativeProbes profile) = true := rfl

theorem expectedShapeNegativeProbes_rejected_by_screen
    (profile : PolyProfile) :
    areExpectedShapeNegativeProbesRejected
      (NegativeProbes.expectedShapeNegativeProbes profile) = true := rfl

end Check

end LeanFX2.Foundation.PolyCell.Core
