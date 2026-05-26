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

/-- Boolean equality test for Nat, local to the PolyCell checker TCB. -/
def hasSameNat : Nat → Nat → Bool
  | 0, secondNumber =>
      match secondNumber with
      | 0 => true
      | _ + 1 => false
  | firstNumber + 1, secondNumber =>
      match secondNumber with
      | 0 => false
      | secondNumber + 1 => hasSameNat firstNumber secondNumber

/-- Local Nat equality recognizes identical inputs by structural recursion. -/
theorem hasSameNat_self (number : Nat) :
    hasSameNat number number = true := by
  induction number with
  | zero => rfl
  | succ _ numberInduction =>
      dsimp [hasSameNat]
      exact numberInduction

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
          hasSameNat firstHead secondHead && hasSameNatList firstTail secondTail

/-- Raw-code equality recognizes syntactically identical Nat lists. -/
theorem hasSameNatList_self (codes : List Nat) :
    hasSameNatList codes codes = true := by
  induction codes with
  | nil => rfl
  | cons codeHead remainingCodes remainingInduction =>
      dsimp [hasSameNatList]
      rw [hasSameNat_self, remainingInduction]
      rfl

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

namespace CertifiedRawCell

/-- A certified raw-cell package erases through its certified cell to the
raw cell in its type index. -/
theorem certifiedCell_raw {profile : PolyProfile} {scope : Nat}
    {dimension : CellDim} {rawCell : PolyTerm profile dimension}
    (certifiedRawCell : CertifiedRawCell profile scope rawCell) :
    certifiedRawCell.certifiedCell.raw = rawCell := rfl

end CertifiedRawCell

/-- Unindexed certified result returned by the executable ingress.

The result carries an actual `PolyCell` plus a computable raw-code preservation
certificate.  This avoids using dependent eliminators over arbitrary raw input
in the checker itself; concrete seed packages still use `CertifiedRawCell`
when the raw input is known definitionally. -/
structure CertifiedRawCellResult (profile : PolyProfile) (scope : Nat) where
  /-- Dimension of the certified raw cell. -/
  cellDimension : CellDim
  /-- Prefix code of the raw input that produced this result. -/
  inputCode : List Nat
  /-- Certified raw cell returned by the ingress. -/
  rawCell : PolyTerm profile cellDimension
  /-- Sort inferred for the certified cell. -/
  cellSort : CellSort
  /-- Boundary inferred for the certified cell. -/
  cellBoundary : CellBoundary profile cellSort cellDimension scope
  /-- Certified cell over `rawCell`. -/
  certifiedCell :
    PolyCell profile cellSort cellDimension scope cellBoundary rawCell
  /-- The returned raw cell has the same prefix code as the input. -/
  hasInputCode :
    hasSameNatList inputCode (rawCellCode rawCell) = true

namespace CertifiedRawCellResult

/-- A successful certified-result package erases through its certified cell to
the raw cell stored in the result. -/
theorem certifiedCell_raw {profile : PolyProfile} {scope : Nat}
    (certifiedResult : CertifiedRawCellResult profile scope) :
    certifiedResult.certifiedCell.raw = certifiedResult.rawCell := rfl

/-- The result's stored input code matches the raw code of its stored raw
cell. -/
theorem inputCode_matches_rawCellCode {profile : PolyProfile} {scope : Nat}
    (certifiedResult : CertifiedRawCellResult profile scope) :
    hasSameNatList certifiedResult.inputCode
      (rawCellCode certifiedResult.rawCell) = true :=
  certifiedResult.hasInputCode

end CertifiedRawCellResult

/-- Package a raw-indexed certificate into the executable result type. -/
def certifiedRawCellResultOfPackage {profile : PolyProfile} {scope : Nat}
    {dimension : CellDim} {rawCell : PolyTerm profile dimension}
    (inputCode : List Nat)
    (certifiedRawCell : CertifiedRawCell profile scope rawCell)
    (hasInputCode :
      hasSameNatList inputCode (rawCellCode rawCell) = true) :
    CertifiedRawCellResult profile scope where
  cellDimension := dimension
  inputCode := inputCode
  rawCell := rawCell
  cellSort := certifiedRawCell.cellSort
  cellBoundary := certifiedRawCell.cellBoundary
  certifiedCell := certifiedRawCell.certifiedCell
  hasInputCode := hasInputCode

/-- Packaging a raw-indexed certificate preserves its raw erasure. -/
theorem certifiedRawCellResultOfPackage_rawCell {profile : PolyProfile}
    {scope : Nat} {dimension : CellDim}
    {rawCell : PolyTerm profile dimension}
    (inputCode : List Nat)
    (certifiedRawCell : CertifiedRawCell profile scope rawCell)
    (hasInputCode :
      hasSameNatList inputCode (rawCellCode rawCell) = true) :
    (certifiedRawCellResultOfPackage
      inputCode certifiedRawCell hasInputCode).rawCell = rawCell := rfl

/-- Packaging a raw-indexed certificate preserves the certified cell's raw
erasure. -/
theorem certifiedRawCellResultOfPackage_certifiedCell_raw
    {profile : PolyProfile} {scope : Nat} {dimension : CellDim}
    {rawCell : PolyTerm profile dimension}
    (inputCode : List Nat)
    (certifiedRawCell : CertifiedRawCell profile scope rawCell)
    (hasInputCode :
      hasSameNatList inputCode (rawCellCode rawCell) = true) :
    (certifiedRawCellResultOfPackage
      inputCode certifiedRawCell hasInputCode).certifiedCell.raw =
      rawCell := rfl

/-- Construct variable payload evidence by recursion, avoiding propositional
decidable `if` over `<`.

This is the kernel-clean route for variables: successful recursion carries an
actual `<` proof used by `AtomPayloadEvidence.variable`; failure carries no
proof and cannot enter the certified layer. -/
def variablePayloadEvidence? :
    (scope payload : Nat) →
      Option (AtomPayloadEvidence variableGeneratorSpec scope payload)
  | 0, _ => none
  | scope + 1, 0 =>
      some (AtomPayloadEvidence.variable (Nat.zero_lt_succ scope))
  | scope + 1, payload + 1 =>
      match variablePayloadEvidence? scope payload with
      | some (AtomPayloadEvidence.variable hasIndexWithinScope) =>
          some (AtomPayloadEvidence.variable
            (Nat.succ_lt_succ hasIndexWithinScope))
      | none => none

/-- Certified package for any variable payload whose de Bruijn index is
inside the current scope. -/
def certifiedVariablePackage {profile : PolyProfile} {scope index : Nat}
    (hasIndexWithinScope : index < scope) :
    CertifiedRawCell profile scope
      (PolyTerm.atom variableGeneratorSpec.cellId index) where
  cellSort := .term
  cellBoundary := ()
  certifiedCell :=
    PolyCell.variableCell (profile := profile)
      (scope := scope) (index := index) hasIndexWithinScope

/-- Certified package for the nullary unit-type atom at any scope. -/
def certifiedUnitTypePackage {profile : PolyProfile} {scope : Nat} :
    CertifiedRawCell profile scope
      (PolyTerm.atom unitTypeGeneratorSpec.cellId 0) where
  cellSort := .type
  cellBoundary := ()
  certifiedCell :=
    PolyCell.unitType (profile := profile) (scope := scope)

/-- Certified package for the nullary empty-context atom at any scope. -/
def certifiedContextEmptyPackage {profile : PolyProfile} {scope : Nat} :
    CertifiedRawCell profile scope
      (PolyTerm.atom contextEmptyGeneratorSpec.cellId 0) where
  cellSort := .context
  cellBoundary := ()
  certifiedCell :=
    PolyCell.contextEmpty (profile := profile) (scope := scope)

/-- Certified package for the nullary linear-mode atom at any scope. -/
def certifiedLinearModePackage {profile : PolyProfile} {scope : Nat} :
    CertifiedRawCell profile scope
      (PolyTerm.atom linearModeGeneratorSpec.cellId 0) where
  cellSort := .mode
  cellBoundary := ()
  certifiedCell :=
    PolyCell.linearMode (profile := profile) (scope := scope)

/-- Decode the first finite application payloads into raw child descriptors.

This is decoder output only.  The returned children still need recursive
screening or certification before the application atom can be accepted. -/
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
  else if payload = NegativeProbes.applicationTypeAsArgumentPayload then
    Except.ok
      (RawChildDescriptors.application
        (NegativeProbes.seedTermAtom profile)
        (NegativeProbes.seedTypeAtom profile))
  else if payload = NegativeProbes.applicationOutOfScopeArgumentPayload then
    Except.ok
      (RawChildDescriptors.application
        (NegativeProbes.seedTermAtom profile)
        (NegativeProbes.outOfScopeVariableRawCell profile))
  else if payload = NegativeProbes.applicationModeAsFunctionPayload then
    Except.ok
      (RawChildDescriptors.application
        (NegativeProbes.seedModeAtom profile)
        (NegativeProbes.seedTermAtom profile))
  else if payload = NegativeProbes.applicationContextAsFunctionPayload then
    Except.ok
      (RawChildDescriptors.application
        (NegativeProbes.seedContextAtom profile)
        (NegativeProbes.seedTermAtom profile))
  else if payload = NegativeProbes.applicationModeAsArgumentPayload then
    Except.ok
      (RawChildDescriptors.application
        (NegativeProbes.seedTermAtom profile)
        (NegativeProbes.seedModeAtom profile))
  else if payload = NegativeProbes.applicationContextAsArgumentPayload then
    Except.ok
      (RawChildDescriptors.application
        (NegativeProbes.seedTermAtom profile)
        (NegativeProbes.seedContextAtom profile))
  else if payload = NegativeProbes.wrongAritySentinel then
    Except.error .wrongArity
  else if payload = NegativeProbes.wrongChildShapeSentinel then
    Except.error .wrongChildShape
  else
    Except.error .badPayload

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
  | 0 => Except.error .fuelExhausted
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

/-- Fuel zero is reported as checker-budget exhaustion, not as malformed
payload data. -/
theorem screenRawCellWithFuel?_zero_rejects_fuelExhausted
    {profile : PolyProfile} {scope : Nat} {dimension : CellDim}
    (rawCell : PolyTerm profile dimension) :
    screenRawCellWithFuel? 0 scope rawCell =
      Except.error .fuelExhausted := rfl

/-- Certified decoded children for the first finite application payload.

This is deliberately narrower than a general application decoder.  It records
the two certified variable children and the heterogeneous child spine dictated
by `applicationGeneratorSpec`. -/
structure CertifiedApplicationVarZeroVarOneChildren
    (profile : PolyProfile) (scope : Nat) where
  /-- Certified function child, decoded as `var 0`. -/
  functionCell :
    PolyCell profile .term 0 scope ()
      (.atom variableGeneratorSpec.cellId 0)
  /-- Certified argument child, decoded as `var 1`. -/
  argumentCell :
    PolyCell profile .term 0 scope ()
      (.atom variableGeneratorSpec.cellId 1)

namespace CertifiedApplicationVarZeroVarOneChildren

/-- Certified child spine matching the application generator metadata.

The spine is derived from the two certified children instead of being stored
as an independent field.  This prevents an inconsistent package from carrying
`functionCell`/`argumentCell` together with an unrelated child spine. -/
def applicationChildSpine {profile : PolyProfile} {scope : Nat}
    (certifiedChildren :
      CertifiedApplicationVarZeroVarOneChildren profile scope) :
    CellChildren.ForGenerator (PolyCell.CertifiedChild profile) scope
      applicationGeneratorSpec :=
  PolyCell.applicationVarZeroVarOneChildren
    certifiedChildren.functionCell
    certifiedChildren.argumentCell

/-- Descriptor-indexed certified child spine for the accepted application
children. -/
def applicationDescriptorChildSpine {profile : PolyProfile} {scope : Nat}
    (certifiedChildren :
      CertifiedApplicationVarZeroVarOneChildren profile scope) :
    PolyCell.CertifiedChildSpineForRawDescriptors profile scope
      (RawChildDescriptors.application (profile := profile)
        (parentScope := scope)
        (PolyTerm.atom variableGeneratorSpec.cellId 0)
        (PolyTerm.atom variableGeneratorSpec.cellId 1)) :=
  PolyCell.applicationVarZeroVarOneChildrenForRawDescriptors
    certifiedChildren.functionCell
    certifiedChildren.argumentCell

/-- Descriptor-indexed application children forget to the ordinary certified
child spine. -/
theorem applicationDescriptorChildSpine_toCertifiedChildren
    {profile : PolyProfile} {scope : Nat}
    (certifiedChildren :
      CertifiedApplicationVarZeroVarOneChildren profile scope) :
    certifiedChildren.applicationDescriptorChildSpine.toCertifiedChildren =
      certifiedChildren.applicationChildSpine := rfl

end CertifiedApplicationVarZeroVarOneChildren

/-- Build the certified child package for `app(var 0, var 1)` from variable
scope evidence. -/
def certifiedApplicationVarZeroVarOneChildren {profile : PolyProfile}
    {scope : Nat}
    (hasFunctionIndexWithinScope : 0 < scope)
    (hasArgumentIndexWithinScope : 1 < scope) :
    CertifiedApplicationVarZeroVarOneChildren profile scope :=
  let functionCell :=
    PolyCell.variableCell (profile := profile)
      (scope := scope) (index := 0) hasFunctionIndexWithinScope
  let argumentCell :=
    PolyCell.variableCell (profile := profile)
      (scope := scope) (index := 1) hasArgumentIndexWithinScope
  { functionCell := functionCell
    argumentCell := argumentCell }

/-- Computably decode certified children for the first finite application
payload.

Scopes 0 and 1 reject before any parent cell can be built, because `var 1` is
not certifiable there.  For larger scopes, the application payload decoder and
generic child screen both run before the certified parent is constructed. -/
def certifyApplicationVarZeroVarOneChildren? {profile : PolyProfile} :
    (scope : Nat) →
      Except CellCheckRejection
        (CertifiedApplicationVarZeroVarOneChildren profile scope)
  | 0 => Except.error .wrongChildShape
  | 1 => Except.error .wrongChildShape
  | scope + 1 + 1 =>
      match
          decodeApplicationPayload? (profile := profile) (scope + 1 + 1)
            applicationVarZeroVarOnePayload with
      | Except.error rejection => Except.error rejection
      | Except.ok rawDescriptors =>
          match
              screenRawChildDescriptorsWith? (profile := profile)
                (fun {childDimension} childScope
                    (childRaw : PolyTerm profile childDimension) =>
                  screenRawCellWithFuel? 63 childScope childRaw)
                (scope + 1 + 1) rawDescriptors with
          | Except.error rejection => Except.error rejection
          | Except.ok () =>
              Except.ok
                (certifiedApplicationVarZeroVarOneChildren
                  (profile := profile) (scope := scope + 1 + 1)
                  (Nat.zero_lt_succ (scope + 1))
                  (Nat.succ_lt_succ (Nat.zero_lt_succ scope)))

/-- Certified package for the first finite application payload.

The package is available only after the decoded variable children have been
screened and certified in the same scope. -/
def certifiedApplicationVarZeroVarOnePackage {profile : PolyProfile}
    {scope : Nat}
    (certifiedChildren :
      CertifiedApplicationVarZeroVarOneChildren profile scope) :
    CertifiedRawCell profile scope
      (PolyTerm.atom applicationGeneratorSpec.cellId
        applicationVarZeroVarOnePayload) where
  cellSort := .term
  cellBoundary := ()
  certifiedCell :=
    PolyCell.applicationVarZeroVarOneCell
      certifiedChildren.functionCell
      certifiedChildren.argumentCell

/-- Certified endpoints for the first finite dim-1 term-step fixture. -/
structure CertifiedTermStepVarZeroVarOneEndpoints
    (profile : PolyProfile) (scope : Nat) where
  /-- Certified source endpoint, decoded as `var 0`. -/
  sourceCell :
    PolyCell profile .term 0 scope ()
      (.atom variableGeneratorSpec.cellId 0)
  /-- Certified target endpoint, decoded as `var 1`. -/
  targetCell :
    PolyCell profile .term 0 scope ()
      (.atom variableGeneratorSpec.cellId 1)

/-- Build certified endpoints for the first finite dim-1 term-step fixture. -/
def certifiedTermStepVarZeroVarOneEndpoints {profile : PolyProfile}
    {scope : Nat}
    (hasSourceIndexWithinScope : 0 < scope)
    (hasTargetIndexWithinScope : 1 < scope) :
    CertifiedTermStepVarZeroVarOneEndpoints profile scope :=
  { sourceCell :=
      PolyCell.variableCell (profile := profile)
        (scope := scope) (index := 0) hasSourceIndexWithinScope
    targetCell :=
      PolyCell.variableCell (profile := profile)
        (scope := scope) (index := 1) hasTargetIndexWithinScope }

/-- Computably certify endpoints for the first finite dim-1 term-step
fixture.

The endpoint screen runs before endpoint witnesses are constructed.  Scopes 0
and 1 reject because `var 1` is not a certifiable endpoint there. -/
def certifyTermStepVarZeroVarOneEndpoints? {profile : PolyProfile} :
    (scope : Nat) →
      Except CellCheckRejection
        (CertifiedTermStepVarZeroVarOneEndpoints profile scope)
  | 0 => Except.error .badBoundaryEndpoint
  | 1 => Except.error .badBoundaryEndpoint
  | scope + 1 + 1 =>
      match
          screenEndpointResultAs? .term
            (screenRawCellWithFuel? (profile := profile) 63
              (scope + 1 + 1) (NegativeProbes.seedTermAtom profile)),
          screenEndpointResultAs? .term
            (screenRawCellWithFuel? (profile := profile) 63
              (scope + 1 + 1) (NegativeProbes.alternateTermAtom profile)) with
      | Except.ok (), Except.ok () =>
          Except.ok
            (certifiedTermStepVarZeroVarOneEndpoints
              (profile := profile) (scope := scope + 1 + 1)
              (Nat.zero_lt_succ (scope + 1))
              (Nat.succ_lt_succ (Nat.zero_lt_succ scope)))
      | Except.error rejection, _ => Except.error rejection
      | _, Except.error rejection => Except.error rejection

/-- Certified package for the first finite dim-1 term-step fixture. -/
def certifiedTermStepVarZeroVarOnePackage {profile : PolyProfile}
    {scope : Nat}
    (certifiedEndpoints :
      CertifiedTermStepVarZeroVarOneEndpoints profile scope) :
    CertifiedRawCell profile scope
      (PolyTerm.cell termStepRuleSpec.ruleId
        (NegativeProbes.seedTermAtom profile)
        (NegativeProbes.alternateTermAtom profile)) where
  cellSort := .term
  cellBoundary :=
    (NegativeProbes.seedTermAtom profile,
      NegativeProbes.alternateTermAtom profile)
  certifiedCell :=
    PolyCell.cell SupportedRuleSpec.termStep
      certifiedEndpoints.sourceCell
      certifiedEndpoints.targetCell

/-- Derived certified identity package over an already certified base cell.

This is a certified-layer operation, not a raw ingress dispatcher: malformed
raw identity bases cannot use it because they have no certified base package. -/
def certifiedIdentityPackage {profile : PolyProfile} {scope : Nat}
    {dimension : CellDim} {baseRaw : PolyTerm profile dimension}
    (certifiedBase : CertifiedRawCell profile scope baseRaw) :
    CertifiedRawCell profile scope (PolyTerm.identity baseRaw) where
  cellSort := certifiedBase.cellSort
  cellBoundary := (baseRaw, baseRaw)
  certifiedCell := PolyCell.identityCell certifiedBase.certifiedCell

/-- Derived certified vertical composite over already certified cells.

The shared middle endpoint is part of the argument types.  This operation does
not inspect raw cells and does not certify arbitrary raw `compV` inputs. -/
def certifiedVerticalCompositePackage {profile : PolyProfile}
    {scope cellDimension : Nat} {cellSort : CellSort}
    {sourceRaw middleRaw targetRaw : PolyTerm profile cellDimension}
    {firstRaw secondRaw : PolyTerm profile (cellDimension + 1)}
    (firstCell :
      PolyCell profile cellSort (cellDimension + 1) scope
        (sourceRaw, middleRaw) firstRaw)
    (secondCell :
      PolyCell profile cellSort (cellDimension + 1) scope
        (middleRaw, targetRaw) secondRaw) :
    CertifiedRawCell profile scope (PolyTerm.compV firstRaw secondRaw) where
  cellSort := cellSort
  cellBoundary := (sourceRaw, targetRaw)
  certifiedCell := PolyCell.verticalCompositeCell firstCell secondCell

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

/-- Does the executable screen reject this inference-level probe with this
specific rejection reason? -/
def isInferNegativeProbeRejectedWith {profile : PolyProfile}
    (targetRejection : CellCheckRejection)
    (probe : RawInferNegativeProbe profile) : Bool :=
  match screenRawCell? (profile := profile) probe.scope probe.rawCell with
  | Except.error rejection =>
      hasSameRejectionCode rejection targetRejection
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

/-- Does the executable expected-shape screen reject this probe with this
specific rejection reason? -/
def isExpectedShapeNegativeProbeRejectedWith {profile : PolyProfile}
    (targetRejection : CellCheckRejection)
    (probe : RawExpectedShapeNegativeProbe profile) : Bool :=
  match
      screenRawCellAs? (profile := profile)
        probe.expectedSort probe.expectedScope probe.rawCell with
  | Except.error rejection =>
      hasSameRejectionCode rejection targetRejection
  | Except.ok _ => false

/-- Does the fuelled screen reject this fuel-budget probe as expected? -/
def isFuelNegativeProbeRejected {profile : PolyProfile}
    (probe : RawFuelNegativeProbe profile) : Bool :=
  match
      screenRawCellWithFuel? (profile := profile)
        probe.fuel probe.scope probe.rawCell with
  | Except.error rejection =>
      hasSameRejectionCode rejection probe.expectedRejection
  | Except.ok _ => false

/-- Does the fuelled screen reject this probe with this specific rejection
reason? -/
def isFuelNegativeProbeRejectedWith {profile : PolyProfile}
    (targetRejection : CellCheckRejection)
    (probe : RawFuelNegativeProbe profile) : Bool :=
  match
      screenRawCellWithFuel? (profile := profile)
        probe.fuel probe.scope probe.rawCell with
  | Except.error rejection =>
      hasSameRejectionCode rejection targetRejection
  | Except.ok _ => false

/-- Check every inference-level negative probe in a list. -/
def areInferNegativeProbesRejected {profile : PolyProfile} :
    List (RawInferNegativeProbe profile) → Bool
  | [] => true
  | probe :: remainingProbes =>
      isInferNegativeProbeRejected probe &&
        areInferNegativeProbesRejected remainingProbes

/-- Check that every inference-level negative probe in a list rejects with
one specific rejection reason. -/
def areInferNegativeProbesRejectedWith {profile : PolyProfile}
    (targetRejection : CellCheckRejection) :
    List (RawInferNegativeProbe profile) → Bool
  | [] => true
  | probe :: remainingProbes =>
      isInferNegativeProbeRejectedWith targetRejection probe &&
        areInferNegativeProbesRejectedWith targetRejection remainingProbes

/-- Check every expected-shape negative probe in a list. -/
def areExpectedShapeNegativeProbesRejected {profile : PolyProfile} :
    List (RawExpectedShapeNegativeProbe profile) → Bool
  | [] => true
  | probe :: remainingProbes =>
      isExpectedShapeNegativeProbeRejected probe &&
        areExpectedShapeNegativeProbesRejected remainingProbes

/-- Check that every expected-shape negative probe in a list rejects with
one specific rejection reason. -/
def areExpectedShapeNegativeProbesRejectedWith {profile : PolyProfile}
    (targetRejection : CellCheckRejection) :
    List (RawExpectedShapeNegativeProbe profile) → Bool
  | [] => true
  | probe :: remainingProbes =>
      isExpectedShapeNegativeProbeRejectedWith targetRejection probe &&
        areExpectedShapeNegativeProbesRejectedWith
          targetRejection remainingProbes

/-- Check every fuel-budget negative probe in a list. -/
def areFuelNegativeProbesRejected {profile : PolyProfile} :
    List (RawFuelNegativeProbe profile) → Bool
  | [] => true
  | probe :: remainingProbes =>
      isFuelNegativeProbeRejected probe &&
        areFuelNegativeProbesRejected remainingProbes

/-- Check that every fuel-budget negative probe in a list rejects with one
specific rejection reason. -/
def areFuelNegativeProbesRejectedWith {profile : PolyProfile}
    (targetRejection : CellCheckRejection) :
    List (RawFuelNegativeProbe profile) → Bool
  | [] => true
  | probe :: remainingProbes =>
      isFuelNegativeProbeRejectedWith targetRejection probe &&
        areFuelNegativeProbesRejectedWith targetRejection remainingProbes

/-- A named inference-probe family has exact coverage only when it is nonempty
and every probe rejects with the named reason. -/
def hasInferNegativeProbeFamilyExactCoverage {profile : PolyProfile}
    (targetRejection : CellCheckRejection) :
    List (RawInferNegativeProbe profile) → Bool
  | [] => false
  | probe :: remainingProbes =>
      areInferNegativeProbesRejectedWith targetRejection
        (probe :: remainingProbes)

/-- A named expected-shape probe family has exact coverage only when it is
nonempty and every probe rejects with the named reason. -/
def hasExpectedShapeNegativeProbeFamilyExactCoverage {profile : PolyProfile}
    (targetRejection : CellCheckRejection) :
    List (RawExpectedShapeNegativeProbe profile) → Bool
  | [] => false
  | probe :: remainingProbes =>
      areExpectedShapeNegativeProbesRejectedWith targetRejection
        (probe :: remainingProbes)

/-- A named fuel-budget probe family has exact coverage only when it is
nonempty and every probe rejects with the named reason. -/
def hasFuelNegativeProbeFamilyExactCoverage {profile : PolyProfile}
    (targetRejection : CellCheckRejection) :
    List (RawFuelNegativeProbe profile) → Bool
  | [] => false
  | probe :: remainingProbes =>
      areFuelNegativeProbesRejectedWith targetRejection
        (probe :: remainingProbes)

/-- Expected-shape screen for dim-0 callers that know the sort they require. -/
def screenRawCell0As? {profile : PolyProfile}
    (expectedSort : CellSort) (scope : Nat)
    (rawCell : PolyTerm profile 0) :
    Except CellCheckRejection Unit :=
  screenRawCellAs? expectedSort scope rawCell

/-- Convert a screen result into a certification-stage rejection.

If the screen already found malformed input, preserve that reason.  If the
screen accepts but the certified ingress has no constructor for this raw shape,
reject explicitly as `unsupportedCertification`. -/
def certificationRejectionAfterScreen? {profile : PolyProfile}
    (scope : Nat) {dimension : CellDim}
    (rawCell : PolyTerm profile dimension) : CellCheckRejection :=
  match screenRawCell? scope rawCell with
  | Except.ok _ => .unsupportedCertification
  | Except.error rejection => rejection

/-- Atom-level executable ingress for payload-evidenced generators.

This accepts only atoms whose payload evidence is already implemented in the
certified layer: in-scope variables, unit type, empty context, and linear
mode.  All other raw cells remain representable but fail certification. -/
def inferRawAtom? {profile : PolyProfile} (scope cellId payload : Nat) :
    Except CellCheckRejection (CertifiedRawCellResult profile scope) :=
  if Nat.beq cellId variableGeneratorSpec.cellId then
    match variablePayloadEvidence? scope payload with
    | some (AtomPayloadEvidence.variable hasIndexWithinScope) =>
        Except.ok
          (certifiedRawCellResultOfPackage
            (profile := profile) (scope := scope)
            (rawCellCode
              (PolyTerm.atom (profile := profile)
                variableGeneratorSpec.cellId payload))
            (certifiedVariablePackage (profile := profile)
              hasIndexWithinScope)
            (hasSameNatList_self _))
    | none => Except.error .badPayload
  else if Nat.beq cellId unitTypeGeneratorSpec.cellId then
    if payload = 0 then
      Except.ok
        (certifiedRawCellResultOfPackage
          (profile := profile) (scope := scope)
          (rawCellCode
            (PolyTerm.atom (profile := profile) unitTypeGeneratorSpec.cellId 0))
          (certifiedUnitTypePackage (profile := profile))
          (hasSameNatList_self _))
    else
      Except.error
        (certificationRejectionAfterScreen? scope
          (PolyTerm.atom (profile := profile) cellId payload))
  else if Nat.beq cellId contextEmptyGeneratorSpec.cellId then
    if payload = 0 then
      Except.ok
        (certifiedRawCellResultOfPackage
          (profile := profile) (scope := scope)
          (rawCellCode
            (PolyTerm.atom (profile := profile)
              contextEmptyGeneratorSpec.cellId 0))
          (certifiedContextEmptyPackage (profile := profile))
          (hasSameNatList_self _))
    else
      Except.error
        (certificationRejectionAfterScreen? scope
          (PolyTerm.atom (profile := profile) cellId payload))
  else if Nat.beq cellId linearModeGeneratorSpec.cellId then
    if payload = 0 then
      Except.ok
        (certifiedRawCellResultOfPackage
          (profile := profile) (scope := scope)
          (rawCellCode
            (PolyTerm.atom (profile := profile)
              linearModeGeneratorSpec.cellId 0))
          (certifiedLinearModePackage (profile := profile))
          (hasSameNatList_self _))
    else
      Except.error
        (certificationRejectionAfterScreen? scope
          (PolyTerm.atom (profile := profile) cellId payload))
  else if Nat.beq cellId applicationGeneratorSpec.cellId then
    if payload = applicationVarZeroVarOnePayload then
      match certifyApplicationVarZeroVarOneChildren?
          (profile := profile) scope with
      | Except.ok certifiedChildren =>
          Except.ok
            (certifiedRawCellResultOfPackage
              (profile := profile) (scope := scope)
              (rawCellCode
                (PolyTerm.atom (profile := profile)
                  applicationGeneratorSpec.cellId
                  applicationVarZeroVarOnePayload))
              (certifiedApplicationVarZeroVarOnePackage (profile := profile)
                certifiedChildren)
              (hasSameNatList_self _))
      | Except.error rejection => Except.error rejection
    else
      Except.error
        (certificationRejectionAfterScreen? scope
          (PolyTerm.atom (profile := profile) cellId payload))
  else
    Except.error
      (certificationRejectionAfterScreen? scope
        (PolyTerm.atom (profile := profile) cellId payload))

/-- First raw-to-certified executable ingress.

The accepted result contains a certified cell and a computable raw-code
preservation certificate.  This slice certifies only dim-0 payload-evidenced
atoms; positive-dimensional cells remain screen-only. -/
def inferRawCell? {profile : PolyProfile} (scope : Nat)
    (rawCell : PolyTerm profile 0) :
    Except CellCheckRejection (CertifiedRawCellResult profile scope) :=
  match rawCell with
  | .atom cellId payload => inferRawAtom? (profile := profile) scope cellId payload

/-- Direct executable certified ingress for the first dim-1 term-step fixture.

This avoids a dependent dispatcher over arbitrary positive-dimensional raw
cells.  The arbitrary dispatcher route is left out until it can be implemented
without adding a trust escape. -/
def inferTermStepVarZeroVarOne? {profile : PolyProfile} (scope : Nat) :
    Except CellCheckRejection (CertifiedRawCellResult profile scope) :=
  match certifyTermStepVarZeroVarOneEndpoints?
      (profile := profile) scope with
  | Except.ok certifiedEndpoints =>
      Except.ok
        (certifiedRawCellResultOfPackage
          (profile := profile) (scope := scope)
          (rawCellCode
            (PolyTerm.cell (profile := profile)
              termStepRuleSpec.ruleId
              (NegativeProbes.seedTermAtom profile)
              (NegativeProbes.alternateTermAtom profile)))
          (certifiedTermStepVarZeroVarOnePackage
            (profile := profile) certifiedEndpoints)
          (hasSameNatList_self _))
  | Except.error rejection => Except.error rejection

/-- Does the certification-stage rejection policy reject this probe as
expected?

This is not a positive certified-ingress dispatcher.  It records that raw
inputs outside the current certified constructor domain still receive the
screen-preserving certification rejection reason. -/
def isCertificationNegativeProbeRejected {profile : PolyProfile}
    (probe : RawCertificationNegativeProbe profile) : Bool :=
  hasSameRejectionCode
    (certificationRejectionAfterScreen? probe.scope probe.rawCell)
    probe.expectedRejection

/-- Does the certification-stage rejection policy reject this probe with this
specific rejection reason? -/
def isCertificationNegativeProbeRejectedWith {profile : PolyProfile}
    (targetRejection : CellCheckRejection)
    (probe : RawCertificationNegativeProbe profile) : Bool :=
  hasSameRejectionCode
    (certificationRejectionAfterScreen? probe.scope probe.rawCell)
    targetRejection

/-- Check every certified-ingress negative probe in a list. -/
def areCertificationNegativeProbesRejected {profile : PolyProfile} :
    List (RawCertificationNegativeProbe profile) → Bool
  | [] => true
  | probe :: remainingProbes =>
      isCertificationNegativeProbeRejected probe &&
        areCertificationNegativeProbesRejected remainingProbes

/-- Check that every certified-ingress negative probe in a list rejects with
one specific rejection reason. -/
def areCertificationNegativeProbesRejectedWith {profile : PolyProfile}
    (targetRejection : CellCheckRejection) :
    List (RawCertificationNegativeProbe profile) → Bool
  | [] => true
  | probe :: remainingProbes =>
      isCertificationNegativeProbeRejectedWith targetRejection probe &&
        areCertificationNegativeProbesRejectedWith
          targetRejection remainingProbes

/-- A named certification-policy probe family has exact coverage only when it
is nonempty and every probe rejects with the named reason. -/
def hasCertificationNegativeProbeFamilyExactCoverage {profile : PolyProfile}
    (targetRejection : CellCheckRejection) :
    List (RawCertificationNegativeProbe profile) → Bool
  | [] => false
  | probe :: remainingProbes =>
      areCertificationNegativeProbesRejectedWith targetRejection
        (probe :: remainingProbes)

/-- Every inference-level negative-probe family is nonempty and rejects with
its named reason. -/
def haveInferNegativeProbeFamiliesExactCoverage
    (profile : PolyProfile) : Bool :=
  hasInferNegativeProbeFamilyExactCoverage .unknownGenerator
    (NegativeProbes.unknownGeneratorInferNegativeProbes profile) &&
  hasInferNegativeProbeFamilyExactCoverage .badPayload
    (NegativeProbes.badPayloadInferNegativeProbes profile) &&
  hasInferNegativeProbeFamilyExactCoverage .wrongArity
    (NegativeProbes.wrongArityInferNegativeProbes profile) &&
  hasInferNegativeProbeFamilyExactCoverage .wrongChildShape
    (NegativeProbes.wrongChildShapeInferNegativeProbes profile) &&
  hasInferNegativeProbeFamilyExactCoverage .badBoundaryEndpoint
    (NegativeProbes.badBoundaryEndpointInferNegativeProbes profile) &&
  hasInferNegativeProbeFamilyExactCoverage .badVerticalBoundary
    (NegativeProbes.badVerticalBoundaryInferNegativeProbes profile) &&
  hasInferNegativeProbeFamilyExactCoverage .unsupportedCompH
    (NegativeProbes.unsupportedCompHInferNegativeProbes profile)

/-- Every expected-shape negative-probe family is nonempty and rejects with
its named reason. -/
def haveExpectedShapeNegativeProbeFamiliesExactCoverage
    (profile : PolyProfile) : Bool :=
  hasExpectedShapeNegativeProbeFamilyExactCoverage .wrongSort
    (NegativeProbes.wrongSortExpectedShapeNegativeProbes profile) &&
  hasExpectedShapeNegativeProbeFamilyExactCoverage .badPayload
    (NegativeProbes.badPayloadExpectedShapeNegativeProbes profile) &&
  hasExpectedShapeNegativeProbeFamilyExactCoverage .wrongArity
    (NegativeProbes.wrongArityExpectedShapeNegativeProbes profile) &&
  hasExpectedShapeNegativeProbeFamilyExactCoverage .wrongChildShape
    (NegativeProbes.wrongChildShapeExpectedShapeNegativeProbes profile)

/-- Every certification-policy negative-probe family is nonempty and rejects
with its named reason. -/
def haveCertificationNegativeProbeFamiliesExactCoverage
    (profile : PolyProfile) : Bool :=
  hasCertificationNegativeProbeFamilyExactCoverage .badBoundaryEndpoint
    (NegativeProbes.badBoundaryEndpointCertificationNegativeProbes profile) &&
  hasCertificationNegativeProbeFamilyExactCoverage .unsupportedCompH
    (NegativeProbes.unsupportedCompHCertificationNegativeProbes profile) &&
  hasCertificationNegativeProbeFamilyExactCoverage .unsupportedCertification
    (NegativeProbes.unsupportedCertificationNegativeProbes profile)

/-- Every fuel-budget negative-probe family is nonempty and rejects with its
named reason. -/
def haveFuelNegativeProbeFamiliesExactCoverage
    (profile : PolyProfile) : Bool :=
  hasFuelNegativeProbeFamilyExactCoverage .fuelExhausted
    (NegativeProbes.fuelExhaustedNegativeProbes profile)

/-- All current negative-probe families are nonempty and reject with their
named reasons. -/
def haveAllNegativeProbeFamiliesExactCoverage
    (profile : PolyProfile) : Bool :=
  haveInferNegativeProbeFamiliesExactCoverage profile &&
  haveExpectedShapeNegativeProbeFamiliesExactCoverage profile &&
  haveCertificationNegativeProbeFamiliesExactCoverage profile &&
  haveFuelNegativeProbeFamiliesExactCoverage profile

/-- Exact probe coverage for one rejection reason.

This is a coverage matrix over the current executable probe layer, not a
non-inhabitation theorem about certified cells.  Reasons that occur in more
than one checker phase require every current phase-family for that reason. -/
def hasNegativeProbeCoverageForRejectionReason
    (profile : PolyProfile) : CellCheckRejection → Bool
  | .unknownGenerator =>
      hasInferNegativeProbeFamilyExactCoverage .unknownGenerator
        (NegativeProbes.unknownGeneratorInferNegativeProbes profile)
  | .wrongSort =>
      hasExpectedShapeNegativeProbeFamilyExactCoverage .wrongSort
        (NegativeProbes.wrongSortExpectedShapeNegativeProbes profile)
  | .badPayload =>
      hasInferNegativeProbeFamilyExactCoverage .badPayload
        (NegativeProbes.badPayloadInferNegativeProbes profile) &&
      hasExpectedShapeNegativeProbeFamilyExactCoverage .badPayload
        (NegativeProbes.badPayloadExpectedShapeNegativeProbes profile)
  | .wrongArity =>
      hasInferNegativeProbeFamilyExactCoverage .wrongArity
        (NegativeProbes.wrongArityInferNegativeProbes profile) &&
      hasExpectedShapeNegativeProbeFamilyExactCoverage .wrongArity
        (NegativeProbes.wrongArityExpectedShapeNegativeProbes profile)
  | .wrongChildShape =>
      hasInferNegativeProbeFamilyExactCoverage .wrongChildShape
        (NegativeProbes.wrongChildShapeInferNegativeProbes profile) &&
      hasExpectedShapeNegativeProbeFamilyExactCoverage .wrongChildShape
        (NegativeProbes.wrongChildShapeExpectedShapeNegativeProbes profile)
  | .badBoundaryEndpoint =>
      hasInferNegativeProbeFamilyExactCoverage .badBoundaryEndpoint
        (NegativeProbes.badBoundaryEndpointInferNegativeProbes profile) &&
      hasCertificationNegativeProbeFamilyExactCoverage .badBoundaryEndpoint
        (NegativeProbes.badBoundaryEndpointCertificationNegativeProbes
          profile)
  | .badVerticalBoundary =>
      hasInferNegativeProbeFamilyExactCoverage .badVerticalBoundary
        (NegativeProbes.badVerticalBoundaryInferNegativeProbes profile)
  | .unsupportedCompH =>
      hasInferNegativeProbeFamilyExactCoverage .unsupportedCompH
        (NegativeProbes.unsupportedCompHInferNegativeProbes profile) &&
      hasCertificationNegativeProbeFamilyExactCoverage .unsupportedCompH
        (NegativeProbes.unsupportedCompHCertificationNegativeProbes profile)
  | .unsupportedCertification =>
      hasCertificationNegativeProbeFamilyExactCoverage
        .unsupportedCertification
        (NegativeProbes.unsupportedCertificationNegativeProbes profile)
  | .fuelExhausted =>
      hasFuelNegativeProbeFamilyExactCoverage .fuelExhausted
        (NegativeProbes.fuelExhaustedNegativeProbes profile)

/-- Check exact probe coverage for each rejection reason in a finite list. -/
def doRejectionReasonsHaveNegativeProbeCoverage
    (profile : PolyProfile) : List CellCheckRejection → Bool
  | [] => true
  | rejectionReason :: remainingReasons =>
      hasNegativeProbeCoverageForRejectionReason profile rejectionReason &&
      doRejectionReasonsHaveNegativeProbeCoverage profile remainingReasons

/-- Every current rejection reason has a nonempty exact probe family at the
checker phase where that reason is supposed to arise. -/
def haveAllCellCheckRejectionReasonsNegativeProbeCoverage
    (profile : PolyProfile) : Bool :=
  doRejectionReasonsHaveNegativeProbeCoverage profile CellCheckRejection.all

/-- Expected-shape wrapper for the dim-0 certified ingress. -/
def checkRawCellAs? {profile : PolyProfile} (expectedSort : CellSort)
    (scope : Nat) (rawCell : PolyTerm profile 0) :
    Except CellCheckRejection (CertifiedRawCellResult profile scope) :=
  match screenRawCell? scope rawCell with
  | Except.ok actualSort =>
      if actualSort = expectedSort then
        inferRawCell? scope rawCell
      else
        Except.error .wrongSort
  | Except.error rejection => Except.error rejection

/-- Extract the sort from an accepted certified-result computation. -/
def certifiedResultSort? {profile : PolyProfile} {scope : Nat} :
    Except CellCheckRejection (CertifiedRawCellResult profile scope) →
      Option CellSort
  | Except.ok certifiedResult => some certifiedResult.cellSort
  | Except.error _ => none

/-- Does an ingress computation accept at this dimension and sort?

This is the lightweight accepted-ingress coverage predicate.  Raw-code
preservation and certified-cell erasure are tracked by separate audited
generic theorem heads to avoid duplicating that normalization here. -/
def hasCertifiedResultShape {profile : PolyProfile} {scope : Nat}
    {dimension : CellDim} (expectedSort : CellSort) :
    Except CellCheckRejection (CertifiedRawCellResult profile scope) → Bool
  | Except.ok certifiedResult =>
      hasSameNat certifiedResult.cellDimension dimension &&
      hasSameNat (CellSort.toCode certifiedResult.cellSort)
        (CellSort.toCode expectedSort)
  | Except.error _ => false

/-- Does an accepted ingress result agree with the structural screen for the
same raw input?

This is executable coverage over the finite accepted frontier.  It checks the
accepted result shape and expected-shape screen without claiming that every
screen-successful raw cell is certifiable.  Raw-code preservation remains
covered by the generic certified-result erasure theorem heads. -/
def hasCertifiedResultScreenCoverage {profile : PolyProfile} {scope : Nat}
    {dimension : CellDim} (expectedSort : CellSort)
    (rawCell : PolyTerm profile dimension) :
    Except CellCheckRejection (CertifiedRawCellResult profile scope) → Bool
  | result =>
      hasCertifiedResultShape (dimension := dimension) expectedSort result &&
      match screenRawCellAs? expectedSort scope rawCell with
      | Except.ok () => true
      | Except.error _ => false

/-- Does an accepted ingress result preserve the raw input code?

This is an executable regression predicate.  It does not identify raw cells
extensionally; it checks the finite prefix-code certificate carried by a
successful ingress result against the raw input.  The separate generic theorem
`CertifiedRawCellResult.inputCode_matches_rawCellCode` links that stored input
code to the returned raw cell. -/
def hasCertifiedResultInputCodeCoverage {profile : PolyProfile} {scope : Nat}
    {dimension : CellDim} (rawCell : PolyTerm profile dimension) :
    Except CellCheckRejection (CertifiedRawCellResult profile scope) → Bool
  | Except.ok result =>
      hasSameNatList result.inputCode (rawCellCode rawCell)
  | Except.error _ => false

/-- Accepted dim-0 ingress coverage for one raw fixture. -/
def hasAcceptedDimZeroIngressCoverage {profile : PolyProfile}
    (expectedSort : CellSort) (expectedRawCell : PolyTerm profile 0) : Bool :=
  hasCertifiedResultShape (dimension := 0) expectedSort
    (inferRawCell? NegativeProbes.defaultInferScope expectedRawCell)

/-- Accepted dim-0 ingress/screen agreement for one raw fixture. -/
def hasAcceptedDimZeroScreenCoverage {profile : PolyProfile}
    (expectedSort : CellSort) (expectedRawCell : PolyTerm profile 0) : Bool :=
  hasCertifiedResultScreenCoverage expectedSort expectedRawCell
    (inferRawCell? NegativeProbes.defaultInferScope expectedRawCell)

/-- Accepted dim-0 ingress/input-code agreement for one raw fixture. -/
def hasAcceptedDimZeroInputCodeCoverage {profile : PolyProfile}
    (expectedRawCell : PolyTerm profile 0) : Bool :=
  hasCertifiedResultInputCodeCoverage expectedRawCell
    (inferRawCell? NegativeProbes.defaultInferScope expectedRawCell)

/-- Current dim-0 accepted ingress fixtures: seed term/type/context/mode atoms
and the first certified application payload. -/
def haveAcceptedDimZeroIngressCoverage (profile : PolyProfile) : Bool :=
  hasAcceptedDimZeroIngressCoverage .term
    (NegativeProbes.seedTermAtom profile) &&
  hasAcceptedDimZeroIngressCoverage .type
    (NegativeProbes.seedTypeAtom profile) &&
  hasAcceptedDimZeroIngressCoverage .context
    (NegativeProbes.seedContextAtom profile) &&
  hasAcceptedDimZeroIngressCoverage .mode
    (NegativeProbes.seedModeAtom profile) &&
  hasAcceptedDimZeroIngressCoverage .term
    (NegativeProbes.applicationVarZeroVarOneRawCell profile)

/-- Current dim-0 accepted ingress fixtures also agree with the structural
screen. -/
def haveAcceptedDimZeroScreenCoverage (profile : PolyProfile) : Bool :=
  hasAcceptedDimZeroScreenCoverage .term
    (NegativeProbes.seedTermAtom profile) &&
  hasAcceptedDimZeroScreenCoverage .type
    (NegativeProbes.seedTypeAtom profile) &&
  hasAcceptedDimZeroScreenCoverage .context
    (NegativeProbes.seedContextAtom profile) &&
  hasAcceptedDimZeroScreenCoverage .mode
    (NegativeProbes.seedModeAtom profile) &&
  hasAcceptedDimZeroScreenCoverage .term
    (NegativeProbes.applicationVarZeroVarOneRawCell profile)

/-- The accepted application package preserves the finite raw input code.

This deliberately checks the certified package directly instead of forcing Lean
to normalize the whole atom dispatcher through the application child screen. -/
def hasAcceptedApplicationVarZeroVarOneInputCodeCoverage
    (profile : PolyProfile) : Bool :=
  hasCertifiedResultInputCodeCoverage
    (NegativeProbes.applicationVarZeroVarOneRawCell profile)
    (Except.ok
      (certifiedRawCellResultOfPackage
        (profile := profile) (scope := NegativeProbes.defaultInferScope)
        (rawCellCode
          (NegativeProbes.applicationVarZeroVarOneRawCell profile))
        (certifiedApplicationVarZeroVarOnePackage
          (profile := profile)
          (certifiedApplicationVarZeroVarOneChildren
            (profile := profile)
            (scope := NegativeProbes.defaultInferScope)
            (Nat.zero_lt_succ 3)
            (Nat.succ_lt_succ (Nat.zero_lt_succ 2))))
        (hasSameNatList_self _)))

/-- Current dim-0 accepted ingress fixtures preserve their raw input codes. -/
def haveAcceptedDimZeroInputCodeCoverage (profile : PolyProfile) : Bool :=
  hasAcceptedDimZeroInputCodeCoverage
    (NegativeProbes.seedTermAtom profile) &&
  hasAcceptedDimZeroInputCodeCoverage
    (NegativeProbes.seedTypeAtom profile) &&
  hasAcceptedDimZeroInputCodeCoverage
    (NegativeProbes.seedContextAtom profile) &&
  hasAcceptedDimZeroInputCodeCoverage
    (NegativeProbes.seedModeAtom profile) &&
  hasAcceptedApplicationVarZeroVarOneInputCodeCoverage profile

/-- Current positive-dimensional accepted ingress fixture: the direct
`termStep(var 0, var 1)` certification path. -/
def hasAcceptedTermStepIngressCoverage (profile : PolyProfile) : Bool :=
  hasCertifiedResultShape (dimension := 1) .term
    (inferTermStepVarZeroVarOne? (profile := profile)
      NegativeProbes.defaultInferScope)

/-- The current positive-dimensional accepted ingress fixture agrees with the
structural screen. -/
def hasAcceptedTermStepScreenCoverage (profile : PolyProfile) : Bool :=
  hasCertifiedResultScreenCoverage .term
    (NegativeProbes.termStepVarZeroVarOneRawCell profile)
    (inferTermStepVarZeroVarOne? (profile := profile)
      NegativeProbes.defaultInferScope)

/-- The current positive-dimensional accepted ingress fixture preserves the
raw input code. -/
def hasAcceptedTermStepInputCodeCoverage (profile : PolyProfile) : Bool :=
  hasCertifiedResultInputCodeCoverage
    (NegativeProbes.termStepVarZeroVarOneRawCell profile)
    (inferTermStepVarZeroVarOne? (profile := profile)
      NegativeProbes.defaultInferScope)

/-- Every current accepted ingress computation has shape coverage.

This is only a coverage matrix for the current finite accepted domain; it is
not a raw dispatcher and does not certify any additional raw shape. -/
def haveCurrentAcceptedIngressCoverage (profile : PolyProfile) : Bool :=
  haveAcceptedDimZeroIngressCoverage profile &&
  hasAcceptedTermStepIngressCoverage profile

/-- Every current accepted ingress computation agrees with its structural
screen. -/
def haveCurrentAcceptedScreenCoverage (profile : PolyProfile) : Bool :=
  haveAcceptedDimZeroScreenCoverage profile &&
  hasAcceptedTermStepScreenCoverage profile

/-- Every current accepted fixture has raw input-code coverage.

Seed atoms and the direct term-step use the executable ingress result; the
application fixture uses its certified package directly to keep this matrix
definitionally cheap. -/
def haveCurrentAcceptedInputCodeCoverage (profile : PolyProfile) : Bool :=
  haveAcceptedDimZeroInputCodeCoverage profile &&
  hasAcceptedTermStepInputCodeCoverage profile

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

/-- Certified package for the first dim-1 term-step fixture at the probe
scope. -/
def certifiedSeedTermStepPackage {profile : PolyProfile} :
    CertifiedRawCell profile NegativeProbes.defaultInferScope
      (NegativeProbes.termStepVarZeroVarOneRawCell profile) :=
  certifiedTermStepVarZeroVarOnePackage (profile := profile)
    (certifiedTermStepVarZeroVarOneEndpoints (profile := profile)
      (scope := NegativeProbes.defaultInferScope)
      (Nat.zero_lt_succ 3)
      (Nat.succ_lt_succ (Nat.zero_lt_succ 2)))

/-- Certified identity over the seed term fixture. -/
def certifiedSeedTermIdentityPackage {profile : PolyProfile} :
    CertifiedRawCell profile NegativeProbes.defaultInferScope
      (PolyTerm.identity (NegativeProbes.seedTermAtom profile)) :=
  certifiedIdentityPackage
    (certifiedSeedTermPackage (profile := profile))

/-- Certified identity over the seed type fixture. -/
def certifiedSeedTypeIdentityPackage {profile : PolyProfile} :
    CertifiedRawCell profile NegativeProbes.defaultInferScope
      (PolyTerm.identity (NegativeProbes.seedTypeAtom profile)) :=
  certifiedIdentityPackage
    (certifiedSeedTypePackage (profile := profile))

/-- Certified identity over the seed context fixture. -/
def certifiedSeedContextIdentityPackage {profile : PolyProfile} :
    CertifiedRawCell profile NegativeProbes.defaultInferScope
      (PolyTerm.identity (NegativeProbes.seedContextAtom profile)) :=
  certifiedIdentityPackage
    (certifiedSeedContextPackage (profile := profile))

/-- Certified identity over the seed mode fixture. -/
def certifiedSeedModeIdentityPackage {profile : PolyProfile} :
    CertifiedRawCell profile NegativeProbes.defaultInferScope
      (PolyTerm.identity (NegativeProbes.seedModeAtom profile)) :=
  certifiedIdentityPackage
    (certifiedSeedModePackage (profile := profile))

/-- Certified identity over the seed dim-1 term-step fixture. -/
def certifiedSeedTermStepIdentityPackage {profile : PolyProfile} :
    CertifiedRawCell profile NegativeProbes.defaultInferScope
      (PolyTerm.identity
        (NegativeProbes.termStepVarZeroVarOneRawCell profile)) :=
  certifiedIdentityPackage
    (certifiedSeedTermStepPackage (profile := profile))

/-- Certified vertical composite of the seed term identity with itself. -/
def certifiedSeedTermIdentityTwicePackage {profile : PolyProfile} :
    CertifiedRawCell profile NegativeProbes.defaultInferScope
      (PolyTerm.compV
        (PolyTerm.identity (NegativeProbes.seedTermAtom profile))
        (PolyTerm.identity (NegativeProbes.seedTermAtom profile))) :=
  certifiedVerticalCompositePackage
    (certifiedSeedTermIdentityPackage (profile := profile)).certifiedCell
    (certifiedSeedTermIdentityPackage (profile := profile)).certifiedCell

theorem lookupGeneratorSpec?_variable :
    lookupGeneratorSpec? variableGeneratorSpec.cellId =
      some ⟨variableGeneratorSpec, SupportedGeneratorSpec.variable⟩ := rfl

theorem lookupGeneratorSpec?_lambda :
    lookupGeneratorSpec? lambdaGeneratorSpec.cellId =
      some ⟨lambdaGeneratorSpec, SupportedGeneratorSpec.lambda⟩ := rfl

theorem lookupGeneratorSpec?_application :
    lookupGeneratorSpec? applicationGeneratorSpec.cellId =
      some ⟨applicationGeneratorSpec, SupportedGeneratorSpec.application⟩ := rfl

theorem lookupGeneratorSpec?_contextEmpty :
    lookupGeneratorSpec? contextEmptyGeneratorSpec.cellId =
      some ⟨contextEmptyGeneratorSpec, SupportedGeneratorSpec.contextEmpty⟩ := rfl

theorem lookupGeneratorSpec?_unitType :
    lookupGeneratorSpec? unitTypeGeneratorSpec.cellId =
      some ⟨unitTypeGeneratorSpec, SupportedGeneratorSpec.unitType⟩ := rfl

theorem lookupGeneratorSpec?_piType :
    lookupGeneratorSpec? piTypeGeneratorSpec.cellId =
      some ⟨piTypeGeneratorSpec, SupportedGeneratorSpec.piType⟩ := rfl

theorem lookupGeneratorSpec?_contextCons :
    lookupGeneratorSpec? contextConsGeneratorSpec.cellId =
      some ⟨contextConsGeneratorSpec, SupportedGeneratorSpec.contextCons⟩ := rfl

theorem lookupGeneratorSpec?_linearMode :
    lookupGeneratorSpec? linearModeGeneratorSpec.cellId =
      some ⟨linearModeGeneratorSpec, SupportedGeneratorSpec.linearMode⟩ := rfl

theorem lookupGeneratorSpec?_unsupportedBeforeLambda :
    lookupGeneratorSpec? (lambdaGeneratorSpec.cellId - 1) = none := rfl

theorem lookupRuleSpec?_termStep :
    lookupRuleSpec? termStepRuleSpec.ruleId =
      some ⟨termStepRuleSpec, SupportedRuleSpec.termStep⟩ := rfl

theorem variablePayloadEvidence?_zero_scope_four :
    variablePayloadEvidence? 4 0 =
      some (AtomPayloadEvidence.variable (Nat.zero_lt_succ 3)) := rfl

theorem variablePayloadEvidence?_four_scope_four :
    variablePayloadEvidence? 4 4 = none := rfl

theorem certifiedVariablePackage_raw {profile : PolyProfile}
    {scope index : Nat} (hasIndexWithinScope : index < scope) :
    (certifiedVariablePackage (profile := profile)
      hasIndexWithinScope).certifiedCell.raw =
      PolyTerm.atom (profile := profile) variableGeneratorSpec.cellId index :=
  rfl

theorem certifiedUnitTypePackage_raw {profile : PolyProfile} {scope : Nat} :
    (certifiedUnitTypePackage (profile := profile)
      (scope := scope)).certifiedCell.raw =
      PolyTerm.atom (profile := profile) unitTypeGeneratorSpec.cellId 0 := rfl

theorem certifiedContextEmptyPackage_raw {profile : PolyProfile}
    {scope : Nat} :
    (certifiedContextEmptyPackage (profile := profile)
      (scope := scope)).certifiedCell.raw =
      PolyTerm.atom (profile := profile) contextEmptyGeneratorSpec.cellId 0 :=
  rfl

theorem certifiedLinearModePackage_raw {profile : PolyProfile}
    {scope : Nat} :
    (certifiedLinearModePackage (profile := profile)
      (scope := scope)).certifiedCell.raw =
      PolyTerm.atom (profile := profile) linearModeGeneratorSpec.cellId 0 :=
  rfl

theorem certifiedApplicationVarZeroVarOnePackage_raw
    {profile : PolyProfile} {scope : Nat}
    (certifiedChildren :
      CertifiedApplicationVarZeroVarOneChildren profile scope) :
    (certifiedApplicationVarZeroVarOnePackage (profile := profile)
      certifiedChildren).certifiedCell.raw =
      PolyTerm.atom (profile := profile) applicationGeneratorSpec.cellId
        applicationVarZeroVarOnePayload := rfl

theorem certifiedTermStepVarZeroVarOnePackage_raw
    {profile : PolyProfile} {scope : Nat}
    (certifiedEndpoints :
      CertifiedTermStepVarZeroVarOneEndpoints profile scope) :
    (certifiedTermStepVarZeroVarOnePackage (profile := profile)
      certifiedEndpoints).certifiedCell.raw =
      NegativeProbes.termStepVarZeroVarOneRawCell profile := rfl

theorem certifiedIdentityPackage_raw
    {profile : PolyProfile} {scope : Nat}
    {dimension : CellDim} {baseRaw : PolyTerm profile dimension}
    (certifiedBase : CertifiedRawCell profile scope baseRaw) :
    (certifiedIdentityPackage certifiedBase).certifiedCell.raw =
      PolyTerm.identity (profile := profile) baseRaw := rfl

theorem certifiedVerticalCompositePackage_raw
    {profile : PolyProfile} {scope cellDimension : Nat}
    {cellSort : CellSort}
    {sourceRaw middleRaw targetRaw : PolyTerm profile cellDimension}
    {firstRaw secondRaw : PolyTerm profile (cellDimension + 1)}
    (firstCell :
      PolyCell profile cellSort (cellDimension + 1) scope
        (sourceRaw, middleRaw) firstRaw)
    (secondCell :
      PolyCell profile cellSort (cellDimension + 1) scope
        (middleRaw, targetRaw) secondRaw) :
    (certifiedVerticalCompositePackage firstCell secondCell).certifiedCell.raw =
      PolyTerm.compV (profile := profile) firstRaw secondRaw := rfl

theorem certifiedSeedTermIdentityTwicePackage_raw
    {profile : PolyProfile} :
    (certifiedSeedTermIdentityTwicePackage
      (profile := profile)).certifiedCell.raw =
      PolyTerm.compV
        (PolyTerm.identity (NegativeProbes.seedTermAtom profile))
        (PolyTerm.identity (NegativeProbes.seedTermAtom profile)) := rfl

theorem certifyApplicationVarZeroVarOneChildren?_scope_zero_rejects
    {profile : PolyProfile} :
    certifyApplicationVarZeroVarOneChildren? (profile := profile) 0 =
      Except.error .wrongChildShape := rfl

theorem certifyApplicationVarZeroVarOneChildren?_scope_one_rejects
    {profile : PolyProfile} :
    certifyApplicationVarZeroVarOneChildren? (profile := profile) 1 =
      Except.error .wrongChildShape := rfl

theorem certifiedApplicationVarZeroVarOneChildren_arity_eq_generator
    {profile : PolyProfile} {scope : Nat}
    (certifiedChildren :
      CertifiedApplicationVarZeroVarOneChildren profile scope) :
    certifiedChildren.applicationChildSpine.arity =
      applicationGeneratorSpec.arity := rfl

theorem certifiedApplicationVarZeroVarOneChildren_rawDescriptors
    {profile : PolyProfile} {scope : Nat}
    (certifiedChildren :
      CertifiedApplicationVarZeroVarOneChildren profile scope) :
    PolyCell.certifiedChildSpineRawDescriptors
      certifiedChildren.applicationChildSpine =
      RawChildDescriptors.application (profile := profile)
        (parentScope := scope)
        (PolyTerm.atom variableGeneratorSpec.cellId 0)
        (PolyTerm.atom variableGeneratorSpec.cellId 1) := rfl

/-- The first certified application child package erases exactly to the
decoder output for the application payload. -/
theorem certifiedApplicationVarZeroVarOneChildren_rawDescriptors_eq_decoder
    {profile : PolyProfile} {scope : Nat}
    (certifiedChildren :
      CertifiedApplicationVarZeroVarOneChildren profile scope) :
    Except.ok
      (PolyCell.certifiedChildSpineRawDescriptors
        certifiedChildren.applicationChildSpine) =
      decodeApplicationPayload? (profile := profile) scope
        applicationVarZeroVarOnePayload := rfl

/-- For every scope where both decoded variables are in scope, certification
followed by child-spine erasure returns the same raw descriptor spine as the
payload decoder. -/
theorem certifyApplicationVarZeroVarOneChildren?_scope_two_plus_rawDescriptors_eq_decoder
    {profile : PolyProfile} {scope : Nat} :
    (match
      certifyApplicationVarZeroVarOneChildren? (profile := profile)
        (scope + 1 + 1) with
    | Except.ok certifiedChildren =>
        Except.ok
          (PolyCell.certifiedChildSpineRawDescriptors
            certifiedChildren.applicationChildSpine)
    | Except.error rejection => Except.error rejection) =
      decodeApplicationPayload? (profile := profile) (scope + 1 + 1)
        applicationVarZeroVarOnePayload := rfl

theorem certifyTermStepVarZeroVarOneEndpoints?_scope_zero_rejects
    {profile : PolyProfile} :
    certifyTermStepVarZeroVarOneEndpoints? (profile := profile) 0 =
      Except.error .badBoundaryEndpoint := rfl

theorem certifyTermStepVarZeroVarOneEndpoints?_scope_one_rejects
    {profile : PolyProfile} :
    certifyTermStepVarZeroVarOneEndpoints? (profile := profile) 1 =
      Except.error .badBoundaryEndpoint := rfl

theorem certifyTermStepVarZeroVarOneEndpoints?_scope_four_accepts
    {profile : PolyProfile} :
    (match
      certifyTermStepVarZeroVarOneEndpoints? (profile := profile)
        NegativeProbes.defaultInferScope with
    | Except.ok _ => true
    | Except.error _ => false) = true := rfl

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

theorem decodeApplicationPayload?_badPayload_rejects
    {profile : PolyProfile} {scope : Nat} :
    decodeApplicationPayload? (profile := profile) scope
      NegativeProbes.badPayloadSentinel =
      Except.error .badPayload := rfl

theorem decodeApplicationPayload?_wrongArity_rejects
    {profile : PolyProfile} {scope : Nat} :
    decodeApplicationPayload? (profile := profile) scope
      NegativeProbes.wrongAritySentinel =
      Except.error .wrongArity := rfl

theorem decodeApplicationPayload?_wrongChildShape_rejects
    {profile : PolyProfile} {scope : Nat} :
    decodeApplicationPayload? (profile := profile) scope
      NegativeProbes.wrongChildShapeSentinel =
      Except.error .wrongChildShape := rfl

theorem decodeApplicationPayload?_typeAsFunction
    {profile : PolyProfile} {scope : Nat} :
    decodeApplicationPayload? (profile := profile) scope
      NegativeProbes.applicationTypeAsFunctionPayload =
      Except.ok
        (RawChildDescriptors.application
          (NegativeProbes.seedTypeAtom profile)
          (NegativeProbes.seedTermAtom profile)) := rfl

theorem decodeApplicationPayload?_typeAsArgument
    {profile : PolyProfile} {scope : Nat} :
    decodeApplicationPayload? (profile := profile) scope
      NegativeProbes.applicationTypeAsArgumentPayload =
      Except.ok
        (RawChildDescriptors.application
          (NegativeProbes.seedTermAtom profile)
          (NegativeProbes.seedTypeAtom profile)) := rfl

theorem decodeApplicationPayload?_outOfScopeArgument
    {profile : PolyProfile} {scope : Nat} :
    decodeApplicationPayload? (profile := profile) scope
      NegativeProbes.applicationOutOfScopeArgumentPayload =
      Except.ok
        (RawChildDescriptors.application
          (NegativeProbes.seedTermAtom profile)
          (NegativeProbes.outOfScopeVariableRawCell profile)) := rfl

theorem decodeApplicationPayload?_modeAsFunction
    {profile : PolyProfile} {scope : Nat} :
    decodeApplicationPayload? (profile := profile) scope
      NegativeProbes.applicationModeAsFunctionPayload =
      Except.ok
        (RawChildDescriptors.application
          (NegativeProbes.seedModeAtom profile)
          (NegativeProbes.seedTermAtom profile)) := rfl

theorem decodeApplicationPayload?_contextAsFunction
    {profile : PolyProfile} {scope : Nat} :
    decodeApplicationPayload? (profile := profile) scope
      NegativeProbes.applicationContextAsFunctionPayload =
      Except.ok
        (RawChildDescriptors.application
          (NegativeProbes.seedContextAtom profile)
          (NegativeProbes.seedTermAtom profile)) := rfl

theorem decodeApplicationPayload?_modeAsArgument
    {profile : PolyProfile} {scope : Nat} :
    decodeApplicationPayload? (profile := profile) scope
      NegativeProbes.applicationModeAsArgumentPayload =
      Except.ok
        (RawChildDescriptors.application
          (NegativeProbes.seedTermAtom profile)
          (NegativeProbes.seedModeAtom profile)) := rfl

theorem decodeApplicationPayload?_contextAsArgument
    {profile : PolyProfile} {scope : Nat} :
    decodeApplicationPayload? (profile := profile) scope
      NegativeProbes.applicationContextAsArgumentPayload =
      Except.ok
        (RawChildDescriptors.application
          (NegativeProbes.seedTermAtom profile)
          (NegativeProbes.seedContextAtom profile)) := rfl

theorem certifyApplicationVarZeroVarOneChildren?_scope_four_accepts
    {profile : PolyProfile} :
    (match
      certifyApplicationVarZeroVarOneChildren? (profile := profile)
        NegativeProbes.defaultInferScope with
    | Except.ok _ => true
    | Except.error _ => false) = true := rfl

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

theorem screenRawChildDescriptorsWith?_applicationTypeAsArgument_rejects
    {profile : PolyProfile} :
    screenRawChildDescriptorsWith? (profile := profile)
      (fun {childDimension} childScope
          (childRaw : PolyTerm profile childDimension) =>
        screenRawCellWithFuel? 63 childScope childRaw)
      NegativeProbes.defaultInferScope
      (RawChildDescriptors.application
        (NegativeProbes.seedTermAtom profile)
        (NegativeProbes.seedTypeAtom profile)) =
      Except.error .wrongChildShape := rfl

theorem screenRawChildDescriptorsWith?_applicationOutOfScopeArgument_rejects
    {profile : PolyProfile} :
    screenRawChildDescriptorsWith? (profile := profile)
      (fun {childDimension} childScope
          (childRaw : PolyTerm profile childDimension) =>
        screenRawCellWithFuel? 63 childScope childRaw)
      NegativeProbes.defaultInferScope
      (RawChildDescriptors.application
        (NegativeProbes.seedTermAtom profile)
        (NegativeProbes.outOfScopeVariableRawCell profile)) =
      Except.error .wrongChildShape := rfl

theorem screenRawCell0?_applicationVarZeroVarOne
    {profile : PolyProfile} :
    screenRawCell0? (profile := profile) NegativeProbes.defaultInferScope
      (NegativeProbes.applicationVarZeroVarOneRawCell profile) =
      Except.ok () := rfl

theorem screenRawCell0?_applicationBadPayload_rejects
    {profile : PolyProfile} :
    screenRawCell0? (profile := profile) NegativeProbes.defaultInferScope
      (NegativeProbes.applicationBadPayloadRawCell profile) =
      Except.error .badPayload := rfl

theorem screenRawCell0?_applicationWrongArity_rejects
    {profile : PolyProfile} :
    screenRawCell0? (profile := profile) NegativeProbes.defaultInferScope
      (NegativeProbes.applicationWrongArityRawCell profile) =
      Except.error .wrongArity := rfl

theorem screenRawCell0?_applicationWrongChildShape_rejects
    {profile : PolyProfile} :
    screenRawCell0? (profile := profile) NegativeProbes.defaultInferScope
      (NegativeProbes.applicationWrongChildShapeRawCell profile) =
      Except.error .wrongChildShape := rfl

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

theorem screenRawCell0?_applicationTypeAsArgument_rejects
    {profile : PolyProfile} :
    screenRawCell0? (profile := profile) NegativeProbes.defaultInferScope
      (NegativeProbes.applicationTypeAsArgumentRawCell profile) =
      Except.error .wrongChildShape := rfl

theorem screenRawCell0?_applicationOutOfScopeArgument_rejects
    {profile : PolyProfile} :
    screenRawCell0? (profile := profile) NegativeProbes.defaultInferScope
      (NegativeProbes.applicationOutOfScopeArgumentRawCell profile) =
      Except.error .wrongChildShape := rfl

theorem screenRawCell0?_badPiTypePayload_rejects
    {profile : PolyProfile} :
    screenRawCell0? (profile := profile) NegativeProbes.defaultInferScope
      (NegativeProbes.badPiTypePayloadRawCell profile) =
      Except.error .badPayload := rfl

theorem screenRawCell0?_badContextConsPayload_rejects
    {profile : PolyProfile} :
    screenRawCell0? (profile := profile) NegativeProbes.defaultInferScope
      (NegativeProbes.badContextConsPayloadRawCell profile) =
      Except.error .badPayload := rfl

theorem screenRawCell0?_wrongPiTypeArity_rejects
    {profile : PolyProfile} :
    screenRawCell0? (profile := profile) NegativeProbes.defaultInferScope
      (NegativeProbes.wrongPiTypeArityRawCell profile) =
      Except.error .wrongArity := rfl

theorem screenRawCell0?_wrongPiTypeChildShape_rejects
    {profile : PolyProfile} :
    screenRawCell0? (profile := profile) NegativeProbes.defaultInferScope
      (NegativeProbes.wrongPiTypeChildShapeRawCell profile) =
      Except.error .wrongChildShape := rfl

theorem screenRawCell0?_wrongContextConsArity_rejects
    {profile : PolyProfile} :
    screenRawCell0? (profile := profile) NegativeProbes.defaultInferScope
      (NegativeProbes.wrongContextConsArityRawCell profile) =
      Except.error .wrongArity := rfl

theorem screenRawCell0?_wrongContextConsChildShape_rejects
    {profile : PolyProfile} :
    screenRawCell0? (profile := profile) NegativeProbes.defaultInferScope
      (NegativeProbes.wrongContextConsChildShapeRawCell profile) =
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

theorem certifiedSeedTermStepPackage_raw {profile : PolyProfile} :
    (certifiedSeedTermStepPackage (profile := profile)).certifiedCell.raw =
      NegativeProbes.termStepVarZeroVarOneRawCell profile := rfl

theorem certifiedSeedTermIdentityPackage_raw {profile : PolyProfile} :
    (certifiedSeedTermIdentityPackage (profile := profile)).certifiedCell.raw =
      PolyTerm.identity (NegativeProbes.seedTermAtom profile) := rfl

theorem certifiedSeedTypeIdentityPackage_raw {profile : PolyProfile} :
    (certifiedSeedTypeIdentityPackage (profile := profile)).certifiedCell.raw =
      PolyTerm.identity (NegativeProbes.seedTypeAtom profile) := rfl

theorem certifiedSeedContextIdentityPackage_raw {profile : PolyProfile} :
    (certifiedSeedContextIdentityPackage
      (profile := profile)).certifiedCell.raw =
      PolyTerm.identity (NegativeProbes.seedContextAtom profile) := rfl

theorem certifiedSeedModeIdentityPackage_raw {profile : PolyProfile} :
    (certifiedSeedModeIdentityPackage (profile := profile)).certifiedCell.raw =
      PolyTerm.identity (NegativeProbes.seedModeAtom profile) := rfl

theorem certifiedSeedTermStepIdentityPackage_raw {profile : PolyProfile} :
    (certifiedSeedTermStepIdentityPackage
      (profile := profile)).certifiedCell.raw =
      PolyTerm.identity
        (NegativeProbes.termStepVarZeroVarOneRawCell profile) := rfl

theorem inferRawCell?_seedTerm_sort {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCell? (profile := profile) NegativeProbes.defaultInferScope
        (NegativeProbes.seedTermAtom profile)) =
      some .term := by
  change
    certifiedResultSort?
      (inferRawAtom? (profile := profile) 4
        variableGeneratorSpec.cellId 0) = some .term
  rfl

theorem inferRawCell?_seedType_sort {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCell? (profile := profile) NegativeProbes.defaultInferScope
        (NegativeProbes.seedTypeAtom profile)) =
      some .type := by
  change
    certifiedResultSort?
      (inferRawAtom? (profile := profile) 4
        unitTypeGeneratorSpec.cellId 0) = some .type
  rfl

theorem inferRawCell?_seedContext_sort {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCell? (profile := profile) NegativeProbes.defaultInferScope
        (NegativeProbes.seedContextAtom profile)) =
      some .context := by
  change
    certifiedResultSort?
      (inferRawAtom? (profile := profile) 4
        contextEmptyGeneratorSpec.cellId 0) = some .context
  rfl

theorem inferRawCell?_seedMode_sort {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCell? (profile := profile) NegativeProbes.defaultInferScope
        (NegativeProbes.seedModeAtom profile)) =
      some .mode := by
  change
    certifiedResultSort?
      (inferRawAtom? (profile := profile) 4
        linearModeGeneratorSpec.cellId 0) = some .mode
  rfl

theorem checkRawCellAs?_seedTerm_sort {profile : PolyProfile} :
    certifiedResultSort?
      (checkRawCellAs? (profile := profile) .term
        NegativeProbes.defaultInferScope
        (NegativeProbes.seedTermAtom profile)) =
      some .term := by
  change
    certifiedResultSort?
      (inferRawAtom? (profile := profile) 4
        variableGeneratorSpec.cellId 0) = some .term
  rfl

theorem checkRawCellAs?_seedTerm_as_type_rejects
    {profile : PolyProfile} :
    checkRawCellAs? (profile := profile) .type
      NegativeProbes.defaultInferScope
      (NegativeProbes.seedTermAtom profile) =
      Except.error .wrongSort := rfl

theorem checkRawCellAs?_seedType_as_term_rejects
    {profile : PolyProfile} :
    checkRawCellAs? (profile := profile) .term
      NegativeProbes.defaultInferScope
      (NegativeProbes.seedTypeAtom profile) =
      Except.error .wrongSort := rfl

theorem checkRawCellAs?_seedContext_as_term_rejects
    {profile : PolyProfile} :
    checkRawCellAs? (profile := profile) .term
      NegativeProbes.defaultInferScope
      (NegativeProbes.seedContextAtom profile) =
      Except.error .wrongSort := rfl

theorem checkRawCellAs?_seedMode_as_term_rejects
    {profile : PolyProfile} :
    checkRawCellAs? (profile := profile) .term
      NegativeProbes.defaultInferScope
      (NegativeProbes.seedModeAtom profile) =
      Except.error .wrongSort := rfl

theorem inferRawCell?_unknownGenerator_rejects
    {profile : PolyProfile} :
    inferRawCell? (profile := profile) NegativeProbes.defaultInferScope
      (NegativeProbes.unknownGeneratorRawCell profile) =
      Except.error .unknownGenerator := by
  change inferRawAtom? (profile := profile) 4
    (lambdaGeneratorSpec.cellId - 1) 0 =
    Except.error .unknownGenerator
  rfl

theorem inferRawCell?_outOfScopeVariable_rejects
    {profile : PolyProfile} :
    inferRawCell? (profile := profile) NegativeProbes.defaultInferScope
      (NegativeProbes.outOfScopeVariableRawCell profile) =
      Except.error .badPayload := by
  change inferRawAtom? (profile := profile) 4
    variableGeneratorSpec.cellId 4 = Except.error .badPayload
  rfl

theorem inferRawCell?_badUnitTypePayload_rejects
    {profile : PolyProfile} :
    inferRawCell? (profile := profile) NegativeProbes.defaultInferScope
      (NegativeProbes.badUnitTypePayloadRawCell profile) =
      Except.error .badPayload := by
  change inferRawAtom? (profile := profile) 4
    unitTypeGeneratorSpec.cellId
    NegativeProbes.badPayloadSentinel =
    Except.error .badPayload
  rfl

theorem inferRawCell?_badLinearModePayload_rejects
    {profile : PolyProfile} :
    inferRawCell? (profile := profile) NegativeProbes.defaultInferScope
      (NegativeProbes.badLinearModePayloadRawCell profile) =
      Except.error .badPayload := by
  change inferRawAtom? (profile := profile) 4
    linearModeGeneratorSpec.cellId
    NegativeProbes.badPayloadSentinel =
      Except.error .badPayload
  rfl

theorem inferRawCell?_applicationVarZeroVarOne_sort
    {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCell? (profile := profile) NegativeProbes.defaultInferScope
        (NegativeProbes.applicationVarZeroVarOneRawCell profile)) =
      some .term := by
  change
    certifiedResultSort?
      (inferRawAtom? (profile := profile) 4
        applicationGeneratorSpec.cellId
        applicationVarZeroVarOnePayload) = some .term
  rfl

theorem checkRawCellAs?_applicationVarZeroVarOne_sort
    {profile : PolyProfile} :
    certifiedResultSort?
      (checkRawCellAs? (profile := profile) .term
        NegativeProbes.defaultInferScope
        (NegativeProbes.applicationVarZeroVarOneRawCell profile)) =
      some .term := by
  change
    certifiedResultSort?
      (inferRawAtom? (profile := profile) 4
        applicationGeneratorSpec.cellId
        applicationVarZeroVarOnePayload) = some .term
  rfl

theorem checkRawCellAs?_applicationVarZeroVarOne_scope_one_rejects
    {profile : PolyProfile} :
    checkRawCellAs? (profile := profile) .term 1
      (NegativeProbes.applicationVarZeroVarOneRawCell profile) =
      Except.error .wrongChildShape := rfl

theorem checkRawCellAs?_applicationVarZeroVarOne_as_type_rejects
    {profile : PolyProfile} :
    checkRawCellAs? (profile := profile) .type
      NegativeProbes.defaultInferScope
      (NegativeProbes.applicationVarZeroVarOneRawCell profile) =
      Except.error .wrongSort := rfl

theorem checkRawCellAs?_applicationVarZeroVarOne_as_context_rejects
    {profile : PolyProfile} :
    checkRawCellAs? (profile := profile) .context
      NegativeProbes.defaultInferScope
      (NegativeProbes.applicationVarZeroVarOneRawCell profile) =
      Except.error .wrongSort := rfl

theorem checkRawCellAs?_applicationVarZeroVarOne_as_mode_rejects
    {profile : PolyProfile} :
    checkRawCellAs? (profile := profile) .mode
      NegativeProbes.defaultInferScope
      (NegativeProbes.applicationVarZeroVarOneRawCell profile) =
      Except.error .wrongSort := rfl

theorem checkRawCellAs?_applicationBadPayload_rejects
    {profile : PolyProfile} :
    checkRawCellAs? (profile := profile) .term
      NegativeProbes.defaultInferScope
      (NegativeProbes.applicationBadPayloadRawCell profile) =
      Except.error .badPayload := rfl

theorem checkRawCellAs?_applicationWrongArity_rejects
    {profile : PolyProfile} :
    checkRawCellAs? (profile := profile) .term
      NegativeProbes.defaultInferScope
      (NegativeProbes.applicationWrongArityRawCell profile) =
      Except.error .wrongArity := rfl

theorem checkRawCellAs?_applicationWrongChildShape_rejects
    {profile : PolyProfile} :
    checkRawCellAs? (profile := profile) .term
      NegativeProbes.defaultInferScope
      (NegativeProbes.applicationWrongChildShapeRawCell profile) =
      Except.error .wrongChildShape := rfl

theorem inferRawAtom?_applicationVarZeroVarOne_scope_one_rejects
    {profile : PolyProfile} :
    inferRawAtom? (profile := profile) 1 applicationGeneratorSpec.cellId
      applicationVarZeroVarOnePayload =
      Except.error .wrongChildShape := rfl

theorem inferRawAtom?_applicationVarZeroVarOne_scope_zero_rejects
    {profile : PolyProfile} :
    inferRawAtom? (profile := profile) 0 applicationGeneratorSpec.cellId
      applicationVarZeroVarOnePayload =
      Except.error .wrongChildShape := rfl

theorem inferRawCell?_applicationTypeAsFunction_rejects
    {profile : PolyProfile} :
    inferRawCell? (profile := profile) NegativeProbes.defaultInferScope
      (NegativeProbes.applicationTypeAsFunctionRawCell profile) =
      Except.error .wrongChildShape := by
  change
    inferRawAtom? (profile := profile) 4
      applicationGeneratorSpec.cellId
      NegativeProbes.applicationTypeAsFunctionPayload =
      Except.error .wrongChildShape
  rfl

theorem inferRawCell?_applicationTypeAsArgument_rejects
    {profile : PolyProfile} :
    inferRawCell? (profile := profile) NegativeProbes.defaultInferScope
      (NegativeProbes.applicationTypeAsArgumentRawCell profile) =
      Except.error .wrongChildShape := by
  change
    inferRawAtom? (profile := profile) 4
      applicationGeneratorSpec.cellId
      NegativeProbes.applicationTypeAsArgumentPayload =
      Except.error .wrongChildShape
  rfl

theorem inferRawCell?_applicationOutOfScopeArgument_rejects
    {profile : PolyProfile} :
    inferRawCell? (profile := profile) NegativeProbes.defaultInferScope
      (NegativeProbes.applicationOutOfScopeArgumentRawCell profile) =
      Except.error .wrongChildShape := by
  change
    inferRawAtom? (profile := profile) 4
      applicationGeneratorSpec.cellId
      NegativeProbes.applicationOutOfScopeArgumentPayload =
      Except.error .wrongChildShape
  rfl

theorem inferTermStepVarZeroVarOne?_sort
    {profile : PolyProfile} :
    certifiedResultSort?
      (inferTermStepVarZeroVarOne? (profile := profile)
        NegativeProbes.defaultInferScope) =
      some .term := by
  change
    certifiedResultSort?
      (inferTermStepVarZeroVarOne? (profile := profile) 4) = some .term
  rfl

/-- Accepted-ingress coverage for the seed term atom. -/
theorem acceptedSeedTermIngress_hasCoverage {profile : PolyProfile} :
    hasAcceptedDimZeroIngressCoverage .term
      (NegativeProbes.seedTermAtom profile) = true := by
  change
    hasCertifiedResultShape (dimension := 0) .term
      (inferRawAtom? (profile := profile) 4
        variableGeneratorSpec.cellId 0) = true
  rfl

/-- Accepted-ingress coverage for the seed type atom. -/
theorem acceptedSeedTypeIngress_hasCoverage {profile : PolyProfile} :
    hasAcceptedDimZeroIngressCoverage .type
      (NegativeProbes.seedTypeAtom profile) = true := by
  change
    hasCertifiedResultShape (dimension := 0) .type
      (inferRawAtom? (profile := profile) 4
        unitTypeGeneratorSpec.cellId 0) = true
  rfl

/-- Accepted-ingress coverage for the seed context atom. -/
theorem acceptedSeedContextIngress_hasCoverage {profile : PolyProfile} :
    hasAcceptedDimZeroIngressCoverage .context
      (NegativeProbes.seedContextAtom profile) = true := by
  change
    hasCertifiedResultShape (dimension := 0) .context
      (inferRawAtom? (profile := profile) 4
        contextEmptyGeneratorSpec.cellId 0) = true
  rfl

/-- Accepted-ingress coverage for the seed mode atom. -/
theorem acceptedSeedModeIngress_hasCoverage {profile : PolyProfile} :
    hasAcceptedDimZeroIngressCoverage .mode
      (NegativeProbes.seedModeAtom profile) = true := by
  change
    hasCertifiedResultShape (dimension := 0) .mode
      (inferRawAtom? (profile := profile) 4
        linearModeGeneratorSpec.cellId 0) = true
  rfl

/-- Accepted-ingress coverage for the first certified application payload. -/
theorem acceptedApplicationVarZeroVarOneIngress_hasCoverage
    {profile : PolyProfile} :
    hasAcceptedDimZeroIngressCoverage .term
      (NegativeProbes.applicationVarZeroVarOneRawCell profile) = true := by
  change
    hasCertifiedResultShape (dimension := 0) .term
      (inferRawAtom? (profile := profile) 4
        applicationGeneratorSpec.cellId
        applicationVarZeroVarOnePayload) = true
  rfl

/-- Accepted-ingress coverage headline for the current dim-0 certified
domain. -/
theorem acceptedDimZeroIngresses_haveCoverage (profile : PolyProfile) :
    haveAcceptedDimZeroIngressCoverage profile = true := by
  dsimp [haveAcceptedDimZeroIngressCoverage]
  rw [acceptedSeedTermIngress_hasCoverage,
    acceptedSeedTypeIngress_hasCoverage,
    acceptedSeedContextIngress_hasCoverage,
    acceptedSeedModeIngress_hasCoverage,
    acceptedApplicationVarZeroVarOneIngress_hasCoverage]
  rfl

/-- Accepted-ingress coverage headline for the current direct dim-1
term-step path. -/
theorem acceptedTermStepIngress_hasCoverage (profile : PolyProfile) :
    hasAcceptedTermStepIngressCoverage profile = true := by
  change
    hasCertifiedResultShape (dimension := 1) .term
      (inferTermStepVarZeroVarOne? (profile := profile) 4) = true
  rfl

/-- Accepted-ingress coverage headline for every currently certified raw
ingress computation. -/
theorem currentAcceptedIngresses_haveCoverage (profile : PolyProfile) :
    haveCurrentAcceptedIngressCoverage profile = true := by
  dsimp [haveCurrentAcceptedIngressCoverage]
  rw [acceptedDimZeroIngresses_haveCoverage,
    acceptedTermStepIngress_hasCoverage]
  rfl

/-- Accepted ingress for the seed term atom agrees with the structural screen. -/
theorem acceptedSeedTermScreen_hasCoverage {profile : PolyProfile} :
    hasAcceptedDimZeroScreenCoverage .term
      (NegativeProbes.seedTermAtom profile) = true := by
  change
    hasCertifiedResultScreenCoverage .term
      (NegativeProbes.seedTermAtom profile)
      (inferRawAtom? (profile := profile) 4
        variableGeneratorSpec.cellId 0) = true
  rfl

/-- Accepted ingress for the seed type atom agrees with the structural screen. -/
theorem acceptedSeedTypeScreen_hasCoverage {profile : PolyProfile} :
    hasAcceptedDimZeroScreenCoverage .type
      (NegativeProbes.seedTypeAtom profile) = true := by
  change
    hasCertifiedResultScreenCoverage .type
      (NegativeProbes.seedTypeAtom profile)
      (inferRawAtom? (profile := profile) 4
        unitTypeGeneratorSpec.cellId 0) = true
  rfl

/-- Accepted ingress for the seed context atom agrees with the structural
screen. -/
theorem acceptedSeedContextScreen_hasCoverage {profile : PolyProfile} :
    hasAcceptedDimZeroScreenCoverage .context
      (NegativeProbes.seedContextAtom profile) = true := by
  change
    hasCertifiedResultScreenCoverage .context
      (NegativeProbes.seedContextAtom profile)
      (inferRawAtom? (profile := profile) 4
        contextEmptyGeneratorSpec.cellId 0) = true
  rfl

/-- Accepted ingress for the seed mode atom agrees with the structural screen. -/
theorem acceptedSeedModeScreen_hasCoverage {profile : PolyProfile} :
    hasAcceptedDimZeroScreenCoverage .mode
      (NegativeProbes.seedModeAtom profile) = true := by
  change
    hasCertifiedResultScreenCoverage .mode
      (NegativeProbes.seedModeAtom profile)
      (inferRawAtom? (profile := profile) 4
        linearModeGeneratorSpec.cellId 0) = true
  rfl

/-- Accepted ingress for the first application payload agrees with the
structural screen. -/
theorem acceptedApplicationVarZeroVarOneScreen_hasCoverage
    {profile : PolyProfile} :
    hasAcceptedDimZeroScreenCoverage .term
      (NegativeProbes.applicationVarZeroVarOneRawCell profile) = true := by
  change
    (hasAcceptedDimZeroIngressCoverage .term
      (NegativeProbes.applicationVarZeroVarOneRawCell profile) &&
      (match
        screenRawCellAs? (profile := profile) .term
          NegativeProbes.defaultInferScope
          (NegativeProbes.applicationVarZeroVarOneRawCell profile) with
      | Except.ok () => true
      | Except.error _ => false)) = true
  have hasApplicationScreen :
      screenRawCellAs? (profile := profile) .term
        NegativeProbes.defaultInferScope
        (NegativeProbes.applicationVarZeroVarOneRawCell profile) =
        Except.ok () :=
    screenRawCell0As?_applicationVarZeroVarOne (profile := profile)
  rw [acceptedApplicationVarZeroVarOneIngress_hasCoverage,
    hasApplicationScreen]
  rfl

/-- Accepted dim-0 ingress agrees with the structural screen for every current
accepted dim-0 fixture. -/
theorem acceptedDimZeroScreens_haveCoverage (profile : PolyProfile) :
    haveAcceptedDimZeroScreenCoverage profile = true := by
  dsimp [haveAcceptedDimZeroScreenCoverage]
  rw [acceptedSeedTermScreen_hasCoverage,
    acceptedSeedTypeScreen_hasCoverage,
    acceptedSeedContextScreen_hasCoverage,
    acceptedSeedModeScreen_hasCoverage,
    acceptedApplicationVarZeroVarOneScreen_hasCoverage]
  rfl

/-- Accepted ingress for the seed term atom preserves the raw input code. -/
theorem acceptedSeedTermInputCode_hasCoverage {profile : PolyProfile} :
    hasAcceptedDimZeroInputCodeCoverage
      (NegativeProbes.seedTermAtom profile) = true := by
  change
    hasCertifiedResultInputCodeCoverage
      (NegativeProbes.seedTermAtom profile)
      (inferRawAtom? (profile := profile) 4
        variableGeneratorSpec.cellId 0) = true
  rfl

/-- Accepted ingress for the seed type atom preserves the raw input code. -/
theorem acceptedSeedTypeInputCode_hasCoverage {profile : PolyProfile} :
    hasAcceptedDimZeroInputCodeCoverage
      (NegativeProbes.seedTypeAtom profile) = true := by
  change
    hasCertifiedResultInputCodeCoverage
      (NegativeProbes.seedTypeAtom profile)
      (inferRawAtom? (profile := profile) 4
        unitTypeGeneratorSpec.cellId 0) = true
  rfl

/-- Accepted ingress for the seed context atom preserves the raw input code. -/
theorem acceptedSeedContextInputCode_hasCoverage {profile : PolyProfile} :
    hasAcceptedDimZeroInputCodeCoverage
      (NegativeProbes.seedContextAtom profile) = true := by
  change
    hasCertifiedResultInputCodeCoverage
      (NegativeProbes.seedContextAtom profile)
      (inferRawAtom? (profile := profile) 4
        contextEmptyGeneratorSpec.cellId 0) = true
  rfl

/-- Accepted ingress for the seed mode atom preserves the raw input code. -/
theorem acceptedSeedModeInputCode_hasCoverage {profile : PolyProfile} :
    hasAcceptedDimZeroInputCodeCoverage
      (NegativeProbes.seedModeAtom profile) = true := by
  change
    hasCertifiedResultInputCodeCoverage
      (NegativeProbes.seedModeAtom profile)
      (inferRawAtom? (profile := profile) 4
        linearModeGeneratorSpec.cellId 0) = true
  rfl

/-- The accepted certified package for the first application payload preserves
the raw input code. -/
theorem acceptedApplicationVarZeroVarOneInputCode_hasCoverage
    {profile : PolyProfile} :
    hasAcceptedApplicationVarZeroVarOneInputCodeCoverage profile = true := by
  change
    hasSameNatList
      (rawCellCode (NegativeProbes.applicationVarZeroVarOneRawCell profile))
      (rawCellCode (NegativeProbes.applicationVarZeroVarOneRawCell profile)) =
      true
  exact hasSameNatList_self _

/-- Accepted dim-0 ingress preserves raw input codes for every current accepted
dim-0 fixture. -/
theorem acceptedDimZeroInputCodes_haveCoverage (profile : PolyProfile) :
    haveAcceptedDimZeroInputCodeCoverage profile = true := by
  dsimp [haveAcceptedDimZeroInputCodeCoverage]
  rw [acceptedSeedTermInputCode_hasCoverage,
    acceptedSeedTypeInputCode_hasCoverage,
    acceptedSeedContextInputCode_hasCoverage,
    acceptedSeedModeInputCode_hasCoverage,
    acceptedApplicationVarZeroVarOneInputCode_hasCoverage]
  rfl

/-- Accepted ingress for the direct dim-1 term-step path agrees with the
structural screen. -/
theorem acceptedTermStepScreen_hasCoverage (profile : PolyProfile) :
    hasAcceptedTermStepScreenCoverage profile = true := by
  change
    hasCertifiedResultScreenCoverage .term
      (NegativeProbes.termStepVarZeroVarOneRawCell profile)
      (inferTermStepVarZeroVarOne? (profile := profile) 4) = true
  rfl

/-- Accepted ingress for the direct dim-1 term-step path preserves the raw
input code. -/
theorem acceptedTermStepInputCode_hasCoverage (profile : PolyProfile) :
    hasAcceptedTermStepInputCodeCoverage profile = true := by
  change
    hasCertifiedResultInputCodeCoverage
      (NegativeProbes.termStepVarZeroVarOneRawCell profile)
      (inferTermStepVarZeroVarOne? (profile := profile) 4) = true
  rfl

/-- Every current accepted ingress computation agrees with its structural
screen. -/
theorem currentAcceptedScreens_haveCoverage (profile : PolyProfile) :
    haveCurrentAcceptedScreenCoverage profile = true := by
  dsimp [haveCurrentAcceptedScreenCoverage]
  rw [acceptedDimZeroScreens_haveCoverage,
    acceptedTermStepScreen_hasCoverage]
  rfl

/-- Every current accepted fixture has raw input-code coverage. -/
theorem currentAcceptedInputCodes_haveCoverage (profile : PolyProfile) :
    haveCurrentAcceptedInputCodeCoverage profile = true := by
  dsimp [haveCurrentAcceptedInputCodeCoverage]
  rw [acceptedDimZeroInputCodes_haveCoverage,
    acceptedTermStepInputCode_hasCoverage]
  rfl

theorem inferTermStepVarZeroVarOne?_scope_one_rejects
    {profile : PolyProfile} :
    inferTermStepVarZeroVarOne? (profile := profile) 1 =
      Except.error .badBoundaryEndpoint := rfl

theorem certificationRejectionAfterScreen?_unsupportedTermStep_rejects
    {profile : PolyProfile} :
    certificationRejectionAfterScreen? (profile := profile)
      NegativeProbes.defaultInferScope
      (NegativeProbes.unsupportedTermStepVarZeroVarTwoRawCell profile) =
      CellCheckRejection.unsupportedCertification := rfl

theorem certificationRejectionAfterScreen?_unsupportedReversedTermStep_rejects
    {profile : PolyProfile} :
    certificationRejectionAfterScreen? (profile := profile)
      NegativeProbes.defaultInferScope
      (NegativeProbes.unsupportedTermStepVarOneVarZeroRawCell profile) =
      CellCheckRejection.unsupportedCertification := rfl

theorem certificationRejectionAfterScreen?_unsupportedReflexiveTermStep_rejects
    {profile : PolyProfile} :
    certificationRejectionAfterScreen? (profile := profile)
      NegativeProbes.defaultInferScope
      (NegativeProbes.unsupportedTermStepVarZeroVarZeroRawCell profile) =
      CellCheckRejection.unsupportedCertification := rfl

theorem certificationRejectionAfterScreen?_matchedVertical_rejects
    {profile : PolyProfile} :
    certificationRejectionAfterScreen? (profile := profile)
      NegativeProbes.defaultInferScope
      (NegativeProbes.matchedVerticalBoundaryRawCell profile) =
      CellCheckRejection.unsupportedCertification := rfl

theorem certificationRejectionAfterScreen?_termIdentityVertical_rejects
    {profile : PolyProfile} :
    certificationRejectionAfterScreen? (profile := profile)
      NegativeProbes.defaultInferScope
      (NegativeProbes.termIdentityVerticalRawCell profile) =
      CellCheckRejection.unsupportedCertification := rfl

theorem certificationRejectionAfterScreen?_typeIdentityVertical_rejects
    {profile : PolyProfile} :
    certificationRejectionAfterScreen? (profile := profile)
      NegativeProbes.defaultInferScope
      (NegativeProbes.typeIdentityVerticalRawCell profile) =
      CellCheckRejection.unsupportedCertification := rfl

theorem certificationRejectionAfterScreen?_contextIdentityVertical_rejects
    {profile : PolyProfile} :
    certificationRejectionAfterScreen? (profile := profile)
      NegativeProbes.defaultInferScope
      (NegativeProbes.contextIdentityVerticalRawCell profile) =
      CellCheckRejection.unsupportedCertification := rfl

theorem certificationRejectionAfterScreen?_modeIdentityVertical_rejects
    {profile : PolyProfile} :
    certificationRejectionAfterScreen? (profile := profile)
      NegativeProbes.defaultInferScope
      (NegativeProbes.modeIdentityVerticalRawCell profile) =
      CellCheckRejection.unsupportedCertification := rfl

theorem screenRawCell?_unsupportedCompHWellScreened_rejects
    {profile : PolyProfile} :
    screenRawCell? (profile := profile) NegativeProbes.defaultInferScope
      (NegativeProbes.unsupportedCompHWellScreenedRawCell profile) =
      Except.error .unsupportedCompH := rfl

theorem screenRawCell?_badIdentityBase_rejects
    {profile : PolyProfile} :
    screenRawCell? (profile := profile) NegativeProbes.defaultInferScope
      (NegativeProbes.badIdentityBaseRawCell profile) =
      Except.error .badPayload := rfl

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
      (NegativeProbes.matchedVerticalBoundaryRawCell profile) =
      Except.ok .term := rfl

theorem screenRawCell?_termIdentityVertical_scope_four
    {profile : PolyProfile} :
    screenRawCell? (profile := profile) NegativeProbes.defaultInferScope
      (NegativeProbes.termIdentityVerticalRawCell profile) =
      Except.ok .term := rfl

theorem screenRawCell?_typeIdentityVertical_scope_four
    {profile : PolyProfile} :
    screenRawCell? (profile := profile) NegativeProbes.defaultInferScope
      (NegativeProbes.typeIdentityVerticalRawCell profile) =
      Except.ok .type := rfl

theorem screenRawCell?_contextIdentityVertical_scope_four
    {profile : PolyProfile} :
    screenRawCell? (profile := profile) NegativeProbes.defaultInferScope
      (NegativeProbes.contextIdentityVerticalRawCell profile) =
      Except.ok .context := rfl

theorem screenRawCell?_modeIdentityVertical_scope_four
    {profile : PolyProfile} :
    screenRawCell? (profile := profile) NegativeProbes.defaultInferScope
      (NegativeProbes.modeIdentityVerticalRawCell profile) =
      Except.ok .mode := rfl

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

theorem badPiTypePayloadProbe_rejects {profile : PolyProfile} :
    screenRawCell0? (profile := profile)
      (NegativeProbes.badPiTypePayloadProbe profile).scope
      (NegativeProbes.badPiTypePayloadRawCell profile) =
      Except.error
        (NegativeProbes.badPiTypePayloadProbe profile).expectedRejection := rfl

theorem badContextConsPayloadProbe_rejects {profile : PolyProfile} :
    screenRawCell0? (profile := profile)
      (NegativeProbes.badContextConsPayloadProbe profile).scope
      (NegativeProbes.badContextConsPayloadRawCell profile) =
      Except.error
        (NegativeProbes.badContextConsPayloadProbe
          profile).expectedRejection := rfl

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

theorem wrongPiTypeArityProbe_rejects {profile : PolyProfile} :
    screenRawCell0? (profile := profile)
      (NegativeProbes.wrongPiTypeArityProbe profile).scope
      (NegativeProbes.wrongPiTypeArityRawCell profile) =
      Except.error
        (NegativeProbes.wrongPiTypeArityProbe profile).expectedRejection := rfl

theorem wrongPiTypeChildShapeProbe_rejects {profile : PolyProfile} :
    screenRawCell0? (profile := profile)
      (NegativeProbes.wrongPiTypeChildShapeProbe profile).scope
      (NegativeProbes.wrongPiTypeChildShapeRawCell profile) =
      Except.error
        (NegativeProbes.wrongPiTypeChildShapeProbe
          profile).expectedRejection := rfl

theorem wrongContextConsArityProbe_rejects {profile : PolyProfile} :
    screenRawCell0? (profile := profile)
      (NegativeProbes.wrongContextConsArityProbe profile).scope
      (NegativeProbes.wrongContextConsArityRawCell profile) =
      Except.error
        (NegativeProbes.wrongContextConsArityProbe
          profile).expectedRejection := rfl

theorem wrongContextConsChildShapeProbe_rejects {profile : PolyProfile} :
    screenRawCell0? (profile := profile)
      (NegativeProbes.wrongContextConsChildShapeProbe profile).scope
      (NegativeProbes.wrongContextConsChildShapeRawCell profile) =
      Except.error
        (NegativeProbes.wrongContextConsChildShapeProbe
          profile).expectedRejection := rfl

theorem applicationBadPayloadProbe_rejects {profile : PolyProfile} :
    screenRawCell0? (profile := profile)
      (NegativeProbes.applicationBadPayloadProbe profile).scope
      (NegativeProbes.applicationBadPayloadRawCell profile) =
      Except.error
        (NegativeProbes.applicationBadPayloadProbe profile).expectedRejection :=
  rfl

theorem applicationWrongArityProbe_rejects {profile : PolyProfile} :
    screenRawCell0? (profile := profile)
      (NegativeProbes.applicationWrongArityProbe profile).scope
      (NegativeProbes.applicationWrongArityRawCell profile) =
      Except.error
        (NegativeProbes.applicationWrongArityProbe profile).expectedRejection :=
  rfl

theorem applicationWrongChildShapeProbe_rejects {profile : PolyProfile} :
    screenRawCell0? (profile := profile)
      (NegativeProbes.applicationWrongChildShapeProbe profile).scope
      (NegativeProbes.applicationWrongChildShapeRawCell profile) =
      Except.error
        (NegativeProbes.applicationWrongChildShapeProbe
          profile).expectedRejection := rfl

theorem applicationTypeAsFunctionProbe_rejects {profile : PolyProfile} :
    screenRawCell0? (profile := profile)
      (NegativeProbes.applicationTypeAsFunctionProbe profile).scope
      (NegativeProbes.applicationTypeAsFunctionRawCell profile) =
      Except.error
        (NegativeProbes.applicationTypeAsFunctionProbe profile).expectedRejection :=
  rfl

theorem applicationTypeAsArgumentProbe_rejects {profile : PolyProfile} :
    screenRawCell0? (profile := profile)
      (NegativeProbes.applicationTypeAsArgumentProbe profile).scope
      (NegativeProbes.applicationTypeAsArgumentRawCell profile) =
      Except.error
        (NegativeProbes.applicationTypeAsArgumentProbe profile).expectedRejection :=
  rfl

theorem applicationOutOfScopeArgumentProbe_rejects {profile : PolyProfile} :
    screenRawCell0? (profile := profile)
      (NegativeProbes.applicationOutOfScopeArgumentProbe profile).scope
      (NegativeProbes.applicationOutOfScopeArgumentRawCell profile) =
      Except.error
        (RawInferNegativeProbe.expectedRejection
          (NegativeProbes.applicationOutOfScopeArgumentProbe profile)) :=
  rfl

theorem applicationModeAsFunctionProbe_rejects {profile : PolyProfile} :
    screenRawCell0? (profile := profile)
      (NegativeProbes.applicationModeAsFunctionProbe profile).scope
      (NegativeProbes.applicationModeAsFunctionRawCell profile) =
      Except.error
        (NegativeProbes.applicationModeAsFunctionProbe profile).expectedRejection :=
  rfl

theorem applicationContextAsFunctionProbe_rejects {profile : PolyProfile} :
    screenRawCell0? (profile := profile)
      (NegativeProbes.applicationContextAsFunctionProbe profile).scope
      (NegativeProbes.applicationContextAsFunctionRawCell profile) =
      Except.error
        (NegativeProbes.applicationContextAsFunctionProbe profile).expectedRejection :=
  rfl

theorem applicationModeAsArgumentProbe_rejects {profile : PolyProfile} :
    screenRawCell0? (profile := profile)
      (NegativeProbes.applicationModeAsArgumentProbe profile).scope
      (NegativeProbes.applicationModeAsArgumentRawCell profile) =
      Except.error
        (NegativeProbes.applicationModeAsArgumentProbe profile).expectedRejection :=
  rfl

theorem applicationContextAsArgumentProbe_rejects {profile : PolyProfile} :
    screenRawCell0? (profile := profile)
      (NegativeProbes.applicationContextAsArgumentProbe profile).scope
      (NegativeProbes.applicationContextAsArgumentRawCell profile) =
      Except.error
        (NegativeProbes.applicationContextAsArgumentProbe profile).expectedRejection :=
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

theorem wrongRuleEndpointDimensionProbe_rejects {profile : PolyProfile} :
    screenRawCell? (profile := profile)
      (NegativeProbes.wrongRuleEndpointDimensionProbe profile).scope
      (NegativeProbes.wrongRuleEndpointDimensionRawCell profile) =
      Except.error
        (RawInferNegativeProbe.expectedRejection
          (NegativeProbes.wrongRuleEndpointDimensionProbe profile)) :=
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

theorem unsupportedCompHWellScreenedProbe_rejects
    {profile : PolyProfile} :
    screenRawCell? (profile := profile)
      (NegativeProbes.unsupportedCompHWellScreenedProbe profile).scope
      (NegativeProbes.unsupportedCompHWellScreenedRawCell profile) =
      Except.error
        (NegativeProbes.unsupportedCompHWellScreenedProbe
          profile).expectedRejection := rfl

theorem badIdentityBaseProbe_rejects {profile : PolyProfile} :
    screenRawCell? (profile := profile)
      (NegativeProbes.badIdentityBaseProbe profile).scope
      (NegativeProbes.badIdentityBaseRawCell profile) =
      Except.error
        (NegativeProbes.badIdentityBaseProbe profile).expectedRejection := rfl

theorem certificationBadBoundaryEndpointProbe_rejects
    {profile : PolyProfile} :
    certificationRejectionAfterScreen? (profile := profile)
      (NegativeProbes.certificationBadBoundaryEndpointProbe profile).scope
      (NegativeProbes.badBoundaryEndpointRawCell profile) =
      (NegativeProbes.certificationBadBoundaryEndpointProbe profile).expectedRejection :=
  rfl

theorem certificationUnsupportedCompHProbe_rejects
    {profile : PolyProfile} :
    certificationRejectionAfterScreen? (profile := profile)
      (NegativeProbes.certificationUnsupportedCompHProbe profile).scope
      (NegativeProbes.unsupportedCompHRawCell profile) =
      (NegativeProbes.certificationUnsupportedCompHProbe profile).expectedRejection :=
  rfl

theorem certificationUnsupportedTermStepProbe_rejects
    {profile : PolyProfile} :
    certificationRejectionAfterScreen? (profile := profile)
      (NegativeProbes.certificationUnsupportedTermStepProbe profile).scope
      (NegativeProbes.unsupportedTermStepVarZeroVarTwoRawCell profile) =
      (NegativeProbes.certificationUnsupportedTermStepProbe profile).expectedRejection :=
  rfl

theorem certificationUnsupportedReversedTermStepProbe_rejects
    {profile : PolyProfile} :
    certificationRejectionAfterScreen? (profile := profile)
      (NegativeProbes.certificationUnsupportedReversedTermStepProbe
        profile).scope
      (NegativeProbes.unsupportedTermStepVarOneVarZeroRawCell profile) =
      (NegativeProbes.certificationUnsupportedReversedTermStepProbe
        profile).expectedRejection := rfl

theorem certificationUnsupportedReflexiveTermStepProbe_rejects
    {profile : PolyProfile} :
    certificationRejectionAfterScreen? (profile := profile)
      (NegativeProbes.certificationUnsupportedReflexiveTermStepProbe
        profile).scope
      (NegativeProbes.unsupportedTermStepVarZeroVarZeroRawCell profile) =
      (NegativeProbes.certificationUnsupportedReflexiveTermStepProbe
        profile).expectedRejection := rfl

theorem certificationMatchedVerticalBoundaryProbe_rejects
    {profile : PolyProfile} :
    certificationRejectionAfterScreen? (profile := profile)
      (NegativeProbes.certificationMatchedVerticalBoundaryProbe profile).scope
      (NegativeProbes.matchedVerticalBoundaryRawCell profile) =
      (NegativeProbes.certificationMatchedVerticalBoundaryProbe profile).expectedRejection :=
  rfl

theorem certificationTermIdentityVerticalProbe_rejects
    {profile : PolyProfile} :
    certificationRejectionAfterScreen? (profile := profile)
      (NegativeProbes.certificationTermIdentityVerticalProbe profile).scope
      (NegativeProbes.termIdentityVerticalRawCell profile) =
      (NegativeProbes.certificationTermIdentityVerticalProbe
        profile).expectedRejection := rfl

theorem certificationTypeIdentityVerticalProbe_rejects
    {profile : PolyProfile} :
    certificationRejectionAfterScreen? (profile := profile)
      (NegativeProbes.certificationTypeIdentityVerticalProbe profile).scope
      (NegativeProbes.typeIdentityVerticalRawCell profile) =
      (NegativeProbes.certificationTypeIdentityVerticalProbe
        profile).expectedRejection := rfl

theorem certificationContextIdentityVerticalProbe_rejects
    {profile : PolyProfile} :
    certificationRejectionAfterScreen? (profile := profile)
      (NegativeProbes.certificationContextIdentityVerticalProbe profile).scope
      (NegativeProbes.contextIdentityVerticalRawCell profile) =
      (NegativeProbes.certificationContextIdentityVerticalProbe
        profile).expectedRejection := rfl

theorem certificationModeIdentityVerticalProbe_rejects
    {profile : PolyProfile} :
    certificationRejectionAfterScreen? (profile := profile)
      (NegativeProbes.certificationModeIdentityVerticalProbe profile).scope
      (NegativeProbes.modeIdentityVerticalRawCell profile) =
      (NegativeProbes.certificationModeIdentityVerticalProbe
        profile).expectedRejection := rfl

theorem wrongSortProbe_rejects {profile : PolyProfile} :
    screenRawCell0As? (profile := profile)
      (NegativeProbes.wrongSortProbe profile).expectedSort
      (NegativeProbes.wrongSortProbe profile).expectedScope
      (NegativeProbes.wrongSortRawCell profile) =
      Except.error (NegativeProbes.wrongSortProbe profile).expectedRejection := rfl

theorem contextAsTypeProbe_rejects {profile : PolyProfile} :
    screenRawCell0As? (profile := profile)
      (NegativeProbes.contextAsTypeProbe profile).expectedSort
      (NegativeProbes.contextAsTypeProbe profile).expectedScope
      (NegativeProbes.contextAsTypeRawCell profile) =
      Except.error
        (NegativeProbes.contextAsTypeProbe profile).expectedRejection := rfl

theorem unitTypeAsTermProbe_rejects {profile : PolyProfile} :
    screenRawCell0As? (profile := profile)
      (NegativeProbes.unitTypeAsTermProbe profile).expectedSort
      (NegativeProbes.unitTypeAsTermProbe profile).expectedScope
      (NegativeProbes.unitTypeAsTermRawCell profile) =
      Except.error
        (NegativeProbes.unitTypeAsTermProbe profile).expectedRejection := rfl

theorem unitTypeAsContextProbe_rejects {profile : PolyProfile} :
    screenRawCell0As? (profile := profile)
      (NegativeProbes.unitTypeAsContextProbe profile).expectedSort
      (NegativeProbes.unitTypeAsContextProbe profile).expectedScope
      (NegativeProbes.unitTypeAsContextRawCell profile) =
      Except.error
        (NegativeProbes.unitTypeAsContextProbe profile).expectedRejection := rfl

theorem termAsTypeProbe_rejects {profile : PolyProfile} :
    screenRawCell0As? (profile := profile)
      (NegativeProbes.termAsTypeProbe profile).expectedSort
      (NegativeProbes.termAsTypeProbe profile).expectedScope
      (NegativeProbes.termAsTypeRawCell profile) =
      Except.error
        (NegativeProbes.termAsTypeProbe profile).expectedRejection := rfl

theorem termAsContextProbe_rejects {profile : PolyProfile} :
    screenRawCell0As? (profile := profile)
      (NegativeProbes.termAsContextProbe profile).expectedSort
      (NegativeProbes.termAsContextProbe profile).expectedScope
      (NegativeProbes.termAsContextRawCell profile) =
      Except.error
        (NegativeProbes.termAsContextProbe profile).expectedRejection := rfl

theorem linearModeAsTermProbe_rejects {profile : PolyProfile} :
    screenRawCell0As? (profile := profile)
      (NegativeProbes.linearModeAsTermProbe profile).expectedSort
      (NegativeProbes.linearModeAsTermProbe profile).expectedScope
      (NegativeProbes.linearModeAsTermRawCell profile) =
      Except.error
        (NegativeProbes.linearModeAsTermProbe profile).expectedRejection := rfl

theorem linearModeAsTypeProbe_rejects {profile : PolyProfile} :
    screenRawCell0As? (profile := profile)
      (NegativeProbes.linearModeAsTypeProbe profile).expectedSort
      (NegativeProbes.linearModeAsTypeProbe profile).expectedScope
      (NegativeProbes.linearModeAsTypeRawCell profile) =
      Except.error
        (NegativeProbes.linearModeAsTypeProbe profile).expectedRejection := rfl

theorem typeIdentityAsTermStepProbe_rejects {profile : PolyProfile} :
    screenRawCellAs? (profile := profile)
      (NegativeProbes.typeIdentityAsTermStepProbe profile).expectedSort
      (NegativeProbes.typeIdentityAsTermStepProbe profile).expectedScope
      (NegativeProbes.typeIdentityAsTermStepRawCell profile) =
      Except.error
        (NegativeProbes.typeIdentityAsTermStepProbe profile).expectedRejection :=
  rfl

theorem applicationVarZeroVarOneAsTypeProbe_rejects
    {profile : PolyProfile} :
    screenRawCell0As? (profile := profile)
      (NegativeProbes.applicationVarZeroVarOneAsTypeProbe profile).expectedSort
      (NegativeProbes.applicationVarZeroVarOneAsTypeProbe
        profile).expectedScope
      (NegativeProbes.applicationVarZeroVarOneRawCell profile) =
      Except.error
        (NegativeProbes.applicationVarZeroVarOneAsTypeProbe
          profile).expectedRejection := rfl

theorem applicationVarZeroVarOneAsContextProbe_rejects
    {profile : PolyProfile} :
    screenRawCell0As? (profile := profile)
      (NegativeProbes.applicationVarZeroVarOneAsContextProbe
        profile).expectedSort
      (NegativeProbes.applicationVarZeroVarOneAsContextProbe
        profile).expectedScope
      (NegativeProbes.applicationVarZeroVarOneRawCell profile) =
      Except.error
        (NegativeProbes.applicationVarZeroVarOneAsContextProbe
          profile).expectedRejection := rfl

theorem applicationVarZeroVarOneAsModeProbe_rejects
    {profile : PolyProfile} :
    screenRawCell0As? (profile := profile)
      (NegativeProbes.applicationVarZeroVarOneAsModeProbe
        profile).expectedSort
      (NegativeProbes.applicationVarZeroVarOneAsModeProbe
        profile).expectedScope
      (NegativeProbes.applicationVarZeroVarOneRawCell profile) =
      Except.error
        (NegativeProbes.applicationVarZeroVarOneAsModeProbe
          profile).expectedRejection := rfl

theorem applicationBadPayloadExpectedShapeProbe_rejects
    {profile : PolyProfile} :
    screenRawCell0As? (profile := profile)
      (NegativeProbes.applicationBadPayloadExpectedShapeProbe
        profile).expectedSort
      (NegativeProbes.applicationBadPayloadExpectedShapeProbe
        profile).expectedScope
      (NegativeProbes.applicationBadPayloadRawCell profile) =
      Except.error
        (NegativeProbes.applicationBadPayloadExpectedShapeProbe
          profile).expectedRejection := rfl

theorem applicationWrongArityExpectedShapeProbe_rejects
    {profile : PolyProfile} :
    screenRawCell0As? (profile := profile)
      (NegativeProbes.applicationWrongArityExpectedShapeProbe
        profile).expectedSort
      (NegativeProbes.applicationWrongArityExpectedShapeProbe
        profile).expectedScope
      (NegativeProbes.applicationWrongArityRawCell profile) =
      Except.error
        (NegativeProbes.applicationWrongArityExpectedShapeProbe
          profile).expectedRejection := rfl

theorem applicationWrongChildShapeExpectedShapeProbe_rejects
    {profile : PolyProfile} :
    screenRawCell0As? (profile := profile)
      (NegativeProbes.applicationWrongChildShapeExpectedShapeProbe
        profile).expectedSort
      (NegativeProbes.applicationWrongChildShapeExpectedShapeProbe
        profile).expectedScope
      (NegativeProbes.applicationWrongChildShapeRawCell profile) =
      Except.error
        (NegativeProbes.applicationWrongChildShapeExpectedShapeProbe
          profile).expectedRejection := rfl

theorem inferNegativeProbes_rejected_by_screen (profile : PolyProfile) :
    areInferNegativeProbesRejected
      (NegativeProbes.inferNegativeProbes profile) = true := rfl

theorem expectedShapeNegativeProbes_rejected_by_screen
    (profile : PolyProfile) :
    areExpectedShapeNegativeProbesRejected
      (NegativeProbes.expectedShapeNegativeProbes profile) = true := rfl

theorem certificationNegativeProbes_rejected_by_policy
    (profile : PolyProfile) :
    areCertificationNegativeProbesRejected
      (NegativeProbes.certificationNegativeProbes profile) = true := rfl

theorem fuelExhaustedProbe_rejects {profile : PolyProfile} :
    screenRawCellWithFuel? (profile := profile)
      (NegativeProbes.fuelExhaustedProbe profile).fuel
      (NegativeProbes.fuelExhaustedProbe profile).scope
      (NegativeProbes.fuelExhaustedProbe profile).rawCell =
      Except.error
        (NegativeProbes.fuelExhaustedProbe profile).expectedRejection := rfl

/-- Headline theorem: all unknown-generator inference probes reject. -/
theorem unknownGeneratorInferNegativeProbes_rejected_by_screen
    (profile : PolyProfile) :
    areInferNegativeProbesRejected
      (NegativeProbes.unknownGeneratorInferNegativeProbes profile) = true :=
  rfl

/-- Headline theorem: all bad-payload inference probes reject. -/
theorem badPayloadInferNegativeProbes_rejected_by_screen
    (profile : PolyProfile) :
    areInferNegativeProbesRejected
      (NegativeProbes.badPayloadInferNegativeProbes profile) = true := rfl

/-- Headline theorem: all wrong-arity inference probes reject. -/
theorem wrongArityInferNegativeProbes_rejected_by_screen
    (profile : PolyProfile) :
    areInferNegativeProbesRejected
      (NegativeProbes.wrongArityInferNegativeProbes profile) = true := rfl

/-- Headline theorem: all wrong-child-shape inference probes reject. -/
theorem wrongChildShapeInferNegativeProbes_rejected_by_screen
    (profile : PolyProfile) :
    areInferNegativeProbesRejected
      (NegativeProbes.wrongChildShapeInferNegativeProbes profile) = true :=
  rfl

/-- Headline theorem: all bad-endpoint inference probes reject. -/
theorem badBoundaryEndpointInferNegativeProbes_rejected_by_screen
    (profile : PolyProfile) :
    areInferNegativeProbesRejected
      (NegativeProbes.badBoundaryEndpointInferNegativeProbes profile) =
      true := rfl

/-- Headline theorem: all bad-vertical-boundary probes reject. -/
theorem badVerticalBoundaryInferNegativeProbes_rejected_by_screen
    (profile : PolyProfile) :
    areInferNegativeProbesRejected
      (NegativeProbes.badVerticalBoundaryInferNegativeProbes profile) =
      true := rfl

/-- Headline theorem: all unsupported-`compH` inference probes reject. -/
theorem unsupportedCompHInferNegativeProbes_rejected_by_screen
    (profile : PolyProfile) :
    areInferNegativeProbesRejected
      (NegativeProbes.unsupportedCompHInferNegativeProbes profile) = true :=
  rfl

/-- Headline theorem: all wrong-sort expected-shape probes reject. -/
theorem wrongSortExpectedShapeNegativeProbes_rejected_by_screen
    (profile : PolyProfile) :
    areExpectedShapeNegativeProbesRejected
      (NegativeProbes.wrongSortExpectedShapeNegativeProbes profile) = true :=
  rfl

/-- Headline theorem: all bad-payload expected-shape probes reject. -/
theorem badPayloadExpectedShapeNegativeProbes_rejected_by_screen
    (profile : PolyProfile) :
    areExpectedShapeNegativeProbesRejected
      (NegativeProbes.badPayloadExpectedShapeNegativeProbes profile) =
      true := rfl

/-- Headline theorem: all wrong-arity expected-shape probes reject. -/
theorem wrongArityExpectedShapeNegativeProbes_rejected_by_screen
    (profile : PolyProfile) :
    areExpectedShapeNegativeProbesRejected
      (NegativeProbes.wrongArityExpectedShapeNegativeProbes profile) =
      true := rfl

/-- Headline theorem: all wrong-child-shape expected-shape probes reject. -/
theorem wrongChildShapeExpectedShapeNegativeProbes_rejected_by_screen
    (profile : PolyProfile) :
    areExpectedShapeNegativeProbesRejected
      (NegativeProbes.wrongChildShapeExpectedShapeNegativeProbes profile) =
      true := rfl

/-- Headline theorem: certification preserves bad-endpoint failures. -/
theorem badBoundaryEndpointCertificationNegativeProbes_rejected_by_policy
    (profile : PolyProfile) :
    areCertificationNegativeProbesRejected
      (NegativeProbes.badBoundaryEndpointCertificationNegativeProbes
        profile) = true := rfl

/-- Headline theorem: certification preserves unsupported `compH`. -/
theorem unsupportedCompHCertificationNegativeProbes_rejected_by_policy
    (profile : PolyProfile) :
    areCertificationNegativeProbesRejected
      (NegativeProbes.unsupportedCompHCertificationNegativeProbes
        profile) = true := rfl

/-- Headline theorem: all screen-passing but uncertified probes reject. -/
theorem unsupportedCertificationNegativeProbes_rejected_by_policy
    (profile : PolyProfile) :
    areCertificationNegativeProbesRejected
      (NegativeProbes.unsupportedCertificationNegativeProbes profile) =
      true := rfl

/-- Headline theorem: all fuel-budget probes reject. -/
theorem fuelExhaustedNegativeProbes_rejected_by_screen
    (profile : PolyProfile) :
    areFuelNegativeProbesRejected
      (NegativeProbes.fuelExhaustedNegativeProbes profile) = true := rfl

/-- Exact-reason headline: all unknown-generator inference probes reject as
`unknownGenerator`. -/
theorem unknownGeneratorInferNegativeProbes_rejected_with_unknownGenerator
    (profile : PolyProfile) :
    areInferNegativeProbesRejectedWith .unknownGenerator
      (NegativeProbes.unknownGeneratorInferNegativeProbes profile) = true :=
  rfl

/-- Exact-reason headline: all bad-payload inference probes reject as
`badPayload`. -/
theorem badPayloadInferNegativeProbes_rejected_with_badPayload
    (profile : PolyProfile) :
    areInferNegativeProbesRejectedWith .badPayload
      (NegativeProbes.badPayloadInferNegativeProbes profile) = true := rfl

/-- Exact-reason headline: all wrong-arity inference probes reject as
`wrongArity`. -/
theorem wrongArityInferNegativeProbes_rejected_with_wrongArity
    (profile : PolyProfile) :
    areInferNegativeProbesRejectedWith .wrongArity
      (NegativeProbes.wrongArityInferNegativeProbes profile) = true := rfl

/-- Exact-reason headline: all wrong-child-shape inference probes reject as
`wrongChildShape`. -/
theorem wrongChildShapeInferNegativeProbes_rejected_with_wrongChildShape
    (profile : PolyProfile) :
    areInferNegativeProbesRejectedWith .wrongChildShape
      (NegativeProbes.wrongChildShapeInferNegativeProbes profile) = true :=
  rfl

/-- Exact-reason headline: all bad-endpoint inference probes reject as
`badBoundaryEndpoint`. -/
theorem
    badBoundaryEndpointInferNegativeProbes_rejected_with_badBoundaryEndpoint
    (profile : PolyProfile) :
    areInferNegativeProbesRejectedWith .badBoundaryEndpoint
      (NegativeProbes.badBoundaryEndpointInferNegativeProbes profile) =
      true := rfl

/-- Exact-reason headline: all bad-vertical-boundary probes reject as
`badVerticalBoundary`. -/
theorem
    badVerticalBoundaryInferNegativeProbes_rejected_with_badVerticalBoundary
    (profile : PolyProfile) :
    areInferNegativeProbesRejectedWith .badVerticalBoundary
      (NegativeProbes.badVerticalBoundaryInferNegativeProbes profile) =
      true := rfl

/-- Exact-reason headline: all unsupported-`compH` inference probes reject as
`unsupportedCompH`. -/
theorem unsupportedCompHInferNegativeProbes_rejected_with_unsupportedCompH
    (profile : PolyProfile) :
    areInferNegativeProbesRejectedWith .unsupportedCompH
      (NegativeProbes.unsupportedCompHInferNegativeProbes profile) = true :=
  rfl

/-- Exact-reason headline: all wrong-sort expected-shape probes reject as
`wrongSort`. -/
theorem wrongSortExpectedShapeNegativeProbes_rejected_with_wrongSort
    (profile : PolyProfile) :
    areExpectedShapeNegativeProbesRejectedWith .wrongSort
      (NegativeProbes.wrongSortExpectedShapeNegativeProbes profile) = true :=
  rfl

/-- Exact-reason headline: all bad-payload expected-shape probes reject as
`badPayload`. -/
theorem badPayloadExpectedShapeNegativeProbes_rejected_with_badPayload
    (profile : PolyProfile) :
    areExpectedShapeNegativeProbesRejectedWith .badPayload
      (NegativeProbes.badPayloadExpectedShapeNegativeProbes profile) =
      true := rfl

/-- Exact-reason headline: all wrong-arity expected-shape probes reject as
`wrongArity`. -/
theorem wrongArityExpectedShapeNegativeProbes_rejected_with_wrongArity
    (profile : PolyProfile) :
    areExpectedShapeNegativeProbesRejectedWith .wrongArity
      (NegativeProbes.wrongArityExpectedShapeNegativeProbes profile) =
      true := rfl

/-- Exact-reason headline: all wrong-child-shape expected-shape probes reject
as `wrongChildShape`. -/
theorem
    wrongChildShapeExpectedShapeNegativeProbes_rejected_with_wrongChildShape
    (profile : PolyProfile) :
    areExpectedShapeNegativeProbesRejectedWith .wrongChildShape
      (NegativeProbes.wrongChildShapeExpectedShapeNegativeProbes profile) =
      true := rfl

/-- Exact-reason headline: certification preserves bad-endpoint failures as
`badBoundaryEndpoint`. -/
theorem
    badBoundaryEndpointCertificationNegativeProbes_rejected_with_badBoundaryEndpoint
    (profile : PolyProfile) :
    areCertificationNegativeProbesRejectedWith .badBoundaryEndpoint
      (NegativeProbes.badBoundaryEndpointCertificationNegativeProbes
        profile) = true := rfl

/-- Exact-reason headline: certification preserves unsupported `compH` as
`unsupportedCompH`. -/
theorem
    unsupportedCompHCertificationNegativeProbes_rejected_with_unsupportedCompH
    (profile : PolyProfile) :
    areCertificationNegativeProbesRejectedWith .unsupportedCompH
      (NegativeProbes.unsupportedCompHCertificationNegativeProbes
        profile) = true := rfl

/-- Exact-reason headline: all screen-passing but uncertified probes reject as
`unsupportedCertification`. -/
theorem
    unsupportedCertificationNegativeProbes_rejected_with_unsupportedCertification
    (profile : PolyProfile) :
    areCertificationNegativeProbesRejectedWith .unsupportedCertification
      (NegativeProbes.unsupportedCertificationNegativeProbes profile) =
      true := rfl

/-- Exact-reason headline: all fuel-budget probes reject as
`fuelExhausted`. -/
theorem fuelExhaustedNegativeProbes_rejected_with_fuelExhausted
    (profile : PolyProfile) :
    areFuelNegativeProbesRejectedWith .fuelExhausted
      (NegativeProbes.fuelExhaustedNegativeProbes profile) = true := rfl

/-- Coverage headline: every inference-level negative-probe family is
nonempty and rejects with its named reason. -/
theorem inferNegativeProbeFamilies_haveExactCoverage
    (profile : PolyProfile) :
    haveInferNegativeProbeFamiliesExactCoverage profile = true := rfl

/-- Coverage headline: every expected-shape negative-probe family is nonempty
and rejects with its named reason. -/
theorem expectedShapeNegativeProbeFamilies_haveExactCoverage
    (profile : PolyProfile) :
    haveExpectedShapeNegativeProbeFamiliesExactCoverage profile = true := rfl

/-- Coverage headline: every certification-policy negative-probe family is
nonempty and rejects with its named reason. -/
theorem certificationNegativeProbeFamilies_haveExactCoverage
    (profile : PolyProfile) :
    haveCertificationNegativeProbeFamiliesExactCoverage profile = true := rfl

/-- Coverage headline: every fuel-budget negative-probe family is nonempty
and rejects with its named reason. -/
theorem fuelNegativeProbeFamilies_haveExactCoverage
    (profile : PolyProfile) :
    haveFuelNegativeProbeFamiliesExactCoverage profile = true := rfl

/-- Coverage headline: every current negative-probe family is nonempty and
rejects with its named reason. -/
theorem allNegativeProbeFamilies_haveExactCoverage
    (profile : PolyProfile) :
    haveAllNegativeProbeFamiliesExactCoverage profile = true := rfl

/-- Coverage headline: every current `CellCheckRejection` constructor has
nonempty exact negative-probe coverage at its checker phase. -/
theorem allCellCheckRejectionReasons_haveNegativeProbeCoverage
    (profile : PolyProfile) :
    haveAllCellCheckRejectionReasonsNegativeProbeCoverage profile = true := rfl

end Check

end LeanFX2.Foundation.PolyCell.Core
