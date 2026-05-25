import LeanFX2.Foundation.PolyCell.Core.Certified
import LeanFX2.Foundation.PolyCell.Core.Fold
import LeanFX2.Foundation.PolyCell.Core.NegativeProbes
/-!
# Check — Executable Raw Rejection Screen

This file is phase A of the raw-to-certified checker.  It is deliberately a
screen, not the final certification function: successful screening returns
`Unit`, not a `PolyCell`.  The current executable rejection theorems cover
the dim-0 malformed raw probes; positive-dimensional probes remain fixtures
until the boundary screen can satisfy the strict TCB audit.
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

/-- Lookup the current supported dim-0 generator metadata by raw id. -/
def lookupGeneratorSpec? (cellId : CellId) : Option KnownGeneratorSpec :=
  if Nat.beq cellId variableGeneratorSpec.cellId then
    some ⟨variableGeneratorSpec, SupportedGeneratorSpec.variable⟩
  else if Nat.beq cellId lambdaGeneratorSpec.cellId then
    some ⟨lambdaGeneratorSpec, SupportedGeneratorSpec.lambda⟩
  else if Nat.beq cellId applicationGeneratorSpec.cellId then
    some ⟨applicationGeneratorSpec, SupportedGeneratorSpec.application⟩
  else if Nat.beq cellId piTypeGeneratorSpec.cellId then
    some ⟨piTypeGeneratorSpec, SupportedGeneratorSpec.piType⟩
  else if Nat.beq cellId contextEmptyGeneratorSpec.cellId then
    some ⟨contextEmptyGeneratorSpec, SupportedGeneratorSpec.contextEmpty⟩
  else if Nat.beq cellId contextConsGeneratorSpec.cellId then
    some ⟨contextConsGeneratorSpec, SupportedGeneratorSpec.contextCons⟩
  else
    none

/-- Lookup the current supported positive-dimensional rule metadata by raw id. -/
def lookupRuleSpec? (ruleId : CellId) : Option KnownRuleSpec :=
  if Nat.beq ruleId termStepRuleSpec.ruleId then
    some ⟨termStepRuleSpec, SupportedRuleSpec.termStep⟩
  else
    none

/-- Preliminary payload screen for a known generator.

Only variable and empty-context payloads are accepted.  Non-nullary generators
remain rejected until real payload decoding is implemented.  The sentinel
payloads route the negative probes to the precise rejection labels that the
future decoder must preserve. -/
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

/-- Recursive executable screen for raw cells at any dimension.

The result is only the inferred sort.  It deliberately does not construct a
certified `PolyCell`; success here is still a pre-certification screen. -/
def screenRawCell? {profile : PolyProfile} (scope : Nat) {dimension : CellDim} :
    PolyTerm profile dimension → Except CellCheckRejection CellSort
  | .atom cellId payload =>
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
                  (screenRawCell? scope source),
                screenEndpointResultAs? knownRule.1.cellSort
                  (screenRawCell? scope targetCell) with
            | Except.ok (), Except.ok () => Except.ok knownRule.1.cellSort
            | Except.error rejection, _ => Except.error rejection
            | _, Except.error rejection => Except.error rejection
          else
            Except.error .unknownGenerator
      | none => Except.error .unknownGenerator
  | .compV first second =>
      match screenRawCell? scope first, screenRawCell? scope second with
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
  | .identity base => screenRawCell? scope base

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

/-- Expected-sort check after the recursive structural screen has succeeded. -/
def screenExpectedSort? {profile : PolyProfile} {dimension : CellDim}
    (expectedSort : CellSort) (rawCell : PolyTerm profile dimension) :
    Except CellCheckRejection Unit :=
  match inferRawCellSort? rawCell with
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
  match screenRawCell? scope rawCell with
  | Except.ok actualSort =>
      if actualSort = expectedSort then
        Except.ok ()
      else
        Except.error .wrongSort
  | Except.error rejection => Except.error rejection

/-- Expected-shape screen for dim-0 callers that know the sort they require. -/
def screenRawCell0As? {profile : PolyProfile}
    (expectedSort : CellSort) (scope : Nat)
    (rawCell : PolyTerm profile 0) :
    Except CellCheckRejection Unit :=
  screenRawCellAs? expectedSort scope rawCell

theorem lookupGeneratorSpec?_variable :
    lookupGeneratorSpec? variableGeneratorSpec.cellId =
      some ⟨variableGeneratorSpec, SupportedGeneratorSpec.variable⟩ := rfl

theorem lookupGeneratorSpec?_contextEmpty :
    lookupGeneratorSpec? contextEmptyGeneratorSpec.cellId =
      some ⟨contextEmptyGeneratorSpec, SupportedGeneratorSpec.contextEmpty⟩ := rfl

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

theorem badPayloadProbe_rejects {profile : PolyProfile} :
    screenRawCell0? (profile := profile)
      (NegativeProbes.badPayloadProbe profile).scope
      (NegativeProbes.badPayloadRawCell profile) =
      Except.error (NegativeProbes.badPayloadProbe profile).expectedRejection := rfl

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

end Check

end LeanFX2.Foundation.PolyCell.Core
