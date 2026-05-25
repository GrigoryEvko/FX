import LeanFX2.Foundation.PolyCell.Core.Certified
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
  match rawCell with
  | .atom cellId payload =>
      match lookupGeneratorSpec? cellId with
      | some knownGenerator => screenAtomPayload? knownGenerator.2 scope payload
      | none => Except.error .unknownGenerator

/-- Expected-shape screen for dim-0 callers that know the sort they require. -/
def screenRawCell0As? {profile : PolyProfile}
    (expectedSort : CellSort) (scope : Nat)
    (rawCell : PolyTerm profile 0) :
    Except CellCheckRejection Unit :=
  match screenRawCell0? scope rawCell with
  | Except.error rejection => Except.error rejection
  | Except.ok () => screenExpectedSort? expectedSort rawCell

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

theorem wrongSortProbe_rejects {profile : PolyProfile} :
    screenRawCell0As? (profile := profile)
      (NegativeProbes.wrongSortProbe profile).expectedSort
      (NegativeProbes.wrongSortProbe profile).expectedScope
      (NegativeProbes.wrongSortRawCell profile) =
      Except.error (NegativeProbes.wrongSortProbe profile).expectedRejection := rfl

end Check

end LeanFX2.Foundation.PolyCell.Core
