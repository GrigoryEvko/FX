import LeanFX2.Foundation.PolyCell.Core.CellChildren
/-!
# Certified — Intrinsic Boundary Layer for Raw PolyTerms

This file is the first certified layer over permissive raw `PolyTerm` syntax.
It does not implement legacy typing, reduction semantics, confluence, or
horizontal composition.  Its job is narrower: certified cells carry their
sort, dimension, scope, boundary, and raw erasure in the type.

Raw `compH` intentionally has no certified constructor here.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- Boundary index for a certified cell.

Dim-0 cells have no lower-dimensional boundary.  A dim-(n+1) cell carries a
raw source and target at dimension n; constructors are responsible for
requiring certificates for those endpoints when they introduce generating
cells or composites. -/
def CellBoundary (profile : PolyProfile) :
    CellSort → CellDim → Nat → Type
  | _, 0, _ => Unit
  | _, dimension + 1, _ => PolyTerm profile dimension × PolyTerm profile dimension

/-- Seed generator specs currently admitted by the certified structural layer.

This is evidence that a generator belongs to the current small supported
table; it is not payload evidence and does not by itself certify an atom. -/
inductive SupportedGeneratorSpec : GeneratorSpec → Type where
  /-- Variable term generator. -/
  | variable :
      SupportedGeneratorSpec variableGeneratorSpec
  /-- Lambda term generator. Payload decoding is not implemented yet. -/
  | lambda :
      SupportedGeneratorSpec lambdaGeneratorSpec
  /-- Application term generator. Only the first finite decoded payload is
  certified today. -/
  | application :
      SupportedGeneratorSpec applicationGeneratorSpec
  /-- Nullary unit type generator. -/
  | unitType :
      SupportedGeneratorSpec unitTypeGeneratorSpec
  /-- Dependent-function type generator. Payload decoding is not implemented yet. -/
  | piType :
      SupportedGeneratorSpec piTypeGeneratorSpec
  /-- Empty-context generator. -/
  | contextEmpty :
      SupportedGeneratorSpec contextEmptyGeneratorSpec
  /-- Context-extension generator. Payload decoding is not implemented yet. -/
  | contextCons :
      SupportedGeneratorSpec contextConsGeneratorSpec
  /-- Nullary linear mode generator. -/
  | linearMode :
      SupportedGeneratorSpec linearModeGeneratorSpec

/-- Seed rule specs currently admitted by the certified structural layer.

The rule evidence only records that the rule id/sort/dimension metadata is in
the supported table.  It does not prove the operational semantics of that
rule. -/
inductive SupportedRuleSpec : RuleSpec → Type where
  /-- Current dim-1 term-step rule shell. -/
  | termStep :
      SupportedRuleSpec termStepRuleSpec

/-- Payload evidence for atom generators that are already safe to certify.

The absence of constructors for lambda/pi/context-extension is intentional:
until payload decoding is real, those atoms cannot be certified by this file.
Application gets only the first finite decoded payload through a separate
`PolyCell` constructor that demands certified child terms. -/
inductive AtomPayloadEvidence :
    (generatorSpec : GeneratorSpec) → (scope : Nat) → (payload : Nat) → Type where
  /-- A variable payload is certified only when the de Bruijn index is inside
  the current scope. -/
  | variable {scope index : Nat} :
      index < scope →
      AtomPayloadEvidence variableGeneratorSpec scope index
  /-- Empty context has the unique accepted payload 0. -/
  | contextEmpty {scope : Nat} :
      AtomPayloadEvidence contextEmptyGeneratorSpec scope 0
  /-- Unit type has the unique accepted payload 0. -/
  | unitType {scope : Nat} :
      AtomPayloadEvidence unitTypeGeneratorSpec scope 0
  /-- Linear mode has the unique accepted payload 0. -/
  | linearMode {scope : Nat} :
      AtomPayloadEvidence linearModeGeneratorSpec scope 0

/-- Certified cell indexed by sort, dimension, scope, boundary, and raw erasure.

The constructors are the trusted introduction rules for this structural layer.
There is no `compH` constructor. -/
inductive PolyCell (profile : PolyProfile) :
    (cellSort : CellSort) →
    (cellDimension : CellDim) →
    (scope : Nat) →
    CellBoundary profile cellSort cellDimension scope →
    PolyTerm profile cellDimension →
    Type where
  /-- Certified dim-0 atom.

  Payload evidence blocks arbitrary raw atoms from entering the certified
  layer.  Since payload decoding for non-nullary generators is not implemented
  yet, the only atoms constructible today are the payload-evidenced nullary
  seed atoms. -/
  | atom {generatorSpec : GeneratorSpec} {scope payload : Nat} :
      SupportedGeneratorSpec generatorSpec →
      AtomPayloadEvidence generatorSpec scope payload →
      PolyCell profile generatorSpec.cellSort 0 scope ()
        (.atom generatorSpec.cellId payload)

  /-- Certified application for the first finite decoded payload.

  The constructor is deliberately narrow: it certifies only the payload whose
  decoded children are `var 0` and `var 1`, and it requires those two children
  to already be certified in the same scope. -/
  | applicationVarZeroVarOne {scope : Nat} :
      PolyCell profile .term 0 scope ()
        (.atom variableGeneratorSpec.cellId 0) →
      PolyCell profile .term 0 scope ()
        (.atom variableGeneratorSpec.cellId 1) →
      PolyCell profile .term 0 scope ()
        (.atom applicationGeneratorSpec.cellId applicationVarZeroVarOnePayload)

  /-- Certified generating cell between certified endpoints.

  This is structural endpoint certification, not yet a proof of the named
  rule's computation behavior. -/
  | cell {ruleSpec : RuleSpec} {scope : Nat}
      {sourceRaw targetRaw : PolyTerm profile ruleSpec.endpointDimension}
      {sourceBoundary targetBoundary :
        CellBoundary profile ruleSpec.cellSort ruleSpec.endpointDimension scope} :
      SupportedRuleSpec ruleSpec →
      PolyCell profile ruleSpec.cellSort ruleSpec.endpointDimension scope
        sourceBoundary sourceRaw →
      PolyCell profile ruleSpec.cellSort ruleSpec.endpointDimension scope
        targetBoundary targetRaw →
      PolyCell profile ruleSpec.cellSort (ruleSpec.endpointDimension + 1) scope
        (sourceRaw, targetRaw)
        (.cell ruleSpec.ruleId sourceRaw targetRaw)

  /-- Certified vertical composition with a definitionally shared middle
  endpoint. -/
  | compV {cellSort : CellSort} {cellDimension scope : Nat}
      {sourceRaw middleRaw targetRaw : PolyTerm profile cellDimension}
      {firstRaw secondRaw : PolyTerm profile (cellDimension + 1)} :
      PolyCell profile cellSort (cellDimension + 1) scope
        (sourceRaw, middleRaw) firstRaw →
      PolyCell profile cellSort (cellDimension + 1) scope
        (middleRaw, targetRaw) secondRaw →
      PolyCell profile cellSort (cellDimension + 1) scope
        (sourceRaw, targetRaw)
        (.compV firstRaw secondRaw)

  /-- Certified identity cell. -/
  | identity {cellSort : CellSort} {cellDimension scope : Nat}
      {boundary : CellBoundary profile cellSort cellDimension scope}
      {baseRaw : PolyTerm profile cellDimension} :
      PolyCell profile cellSort cellDimension scope boundary baseRaw →
      PolyCell profile cellSort (cellDimension + 1) scope
        (baseRaw, baseRaw)
        (.identity baseRaw)

namespace PolyCell

/-- Extract the raw erasure index of a certified cell. -/
def raw {profile : PolyProfile} {cellSort : CellSort} {cellDimension scope : Nat}
    {cellBoundary : CellBoundary profile cellSort cellDimension scope}
    {rawCell : PolyTerm profile cellDimension}
    (_cell : PolyCell profile cellSort cellDimension scope cellBoundary rawCell) :
    PolyTerm profile cellDimension :=
  rawCell

/-- The variable helper certifies exactly the raw variable atom it names. -/
def variableCell {profile : PolyProfile} {scope index : Nat}
    (hasIndexWithinScope : index < scope) :
    PolyCell profile .term 0 scope ()
      (.atom variableGeneratorSpec.cellId index) :=
  .atom SupportedGeneratorSpec.variable
    (AtomPayloadEvidence.variable hasIndexWithinScope)

/-- The empty-context helper certifies exactly the raw empty-context atom. -/
def contextEmpty {profile : PolyProfile} {scope : Nat} :
    PolyCell profile .context 0 scope ()
      (.atom contextEmptyGeneratorSpec.cellId 0) :=
  .atom SupportedGeneratorSpec.contextEmpty
    AtomPayloadEvidence.contextEmpty

/-- The unit-type helper certifies exactly the raw unit-type atom. -/
def unitType {profile : PolyProfile} {scope : Nat} :
    PolyCell profile .type 0 scope ()
      (.atom unitTypeGeneratorSpec.cellId 0) :=
  .atom SupportedGeneratorSpec.unitType
    AtomPayloadEvidence.unitType

/-- The linear-mode helper certifies exactly the raw linear-mode atom. -/
def linearMode {profile : PolyProfile} {scope : Nat} :
    PolyCell profile .mode 0 scope ()
      (.atom linearModeGeneratorSpec.cellId 0) :=
  .atom SupportedGeneratorSpec.linearMode
    AtomPayloadEvidence.linearMode

/-- The first certified application payload requires certified `var 0` and
`var 1` children. -/
def applicationVarZeroVarOneCell {profile : PolyProfile} {scope : Nat}
    (functionCell :
      PolyCell profile .term 0 scope ()
        (.atom variableGeneratorSpec.cellId 0))
    (argumentCell :
      PolyCell profile .term 0 scope ()
        (.atom variableGeneratorSpec.cellId 1)) :
    PolyCell profile .term 0 scope ()
      (.atom applicationGeneratorSpec.cellId applicationVarZeroVarOnePayload) :=
  .applicationVarZeroVarOne functionCell argumentCell

/-- Derive a certified identity cell from an already certified base cell. -/
def identityCell {profile : PolyProfile} {cellSort : CellSort}
    {cellDimension scope : Nat}
    {cellBoundary : CellBoundary profile cellSort cellDimension scope}
    {baseRaw : PolyTerm profile cellDimension}
    (baseCell :
      PolyCell profile cellSort cellDimension scope cellBoundary baseRaw) :
    PolyCell profile cellSort (cellDimension + 1) scope
      (baseRaw, baseRaw) (.identity baseRaw) :=
  .identity baseCell

/-- Certified child descriptor used by non-nullary generator certificates. -/
structure CertifiedChild
    (profile : PolyProfile) (cellSort : CellSort)
    (cellDimension : CellDim) (scope : Nat) where
  /-- Raw erasure of the certified child. -/
  rawCell : PolyTerm profile cellDimension
  /-- Boundary index of the certified child. -/
  cellBoundary : CellBoundary profile cellSort cellDimension scope
  /-- Certified child witness. -/
  certifiedCell :
    PolyCell profile cellSort cellDimension scope cellBoundary rawCell

namespace CertifiedChild

/-- Package a certified child from its raw-indexed witness. -/
def ofCell {profile : PolyProfile} {cellSort : CellSort}
    {cellDimension scope : Nat}
    {cellBoundary : CellBoundary profile cellSort cellDimension scope}
    {rawCell : PolyTerm profile cellDimension}
    (certifiedCell :
      PolyCell profile cellSort cellDimension scope cellBoundary rawCell) :
    CertifiedChild profile cellSort cellDimension scope where
  rawCell := rawCell
  cellBoundary := cellBoundary
  certifiedCell := certifiedCell

end CertifiedChild

/-- Certified child spine for the first finite application payload. -/
def applicationVarZeroVarOneChildren {profile : PolyProfile} {scope : Nat}
    (functionCell :
      PolyCell profile .term 0 scope ()
        (.atom variableGeneratorSpec.cellId 0))
    (argumentCell :
      PolyCell profile .term 0 scope ()
        (.atom variableGeneratorSpec.cellId 1)) :
    CellChildren.ForGenerator (CertifiedChild profile) scope
      applicationGeneratorSpec :=
  CellChildren.cons
    (CertifiedChild.ofCell functionCell)
    (CellChildren.cons
      (CertifiedChild.ofCell argumentCell)
      CellChildren.nil)

/-- Raw erasure of the variable-cell helper is definitional. -/
theorem raw_variableCell {profile : PolyProfile} {scope index : Nat}
    (hasIndexWithinScope : index < scope) :
    (variableCell (profile := profile) hasIndexWithinScope).raw =
      PolyTerm.atom (profile := profile) variableGeneratorSpec.cellId index := rfl

/-- Raw erasure of the empty-context helper is definitional. -/
theorem raw_contextEmpty {profile : PolyProfile} {scope : Nat} :
    (contextEmpty (profile := profile) (scope := scope)).raw =
      PolyTerm.atom (profile := profile) contextEmptyGeneratorSpec.cellId 0 := rfl

/-- Raw erasure of the unit-type helper is definitional. -/
theorem raw_unitType {profile : PolyProfile} {scope : Nat} :
    (unitType (profile := profile) (scope := scope)).raw =
      PolyTerm.atom (profile := profile) unitTypeGeneratorSpec.cellId 0 := rfl

/-- Raw erasure of the linear-mode helper is definitional. -/
theorem raw_linearMode {profile : PolyProfile} {scope : Nat} :
    (linearMode (profile := profile) (scope := scope)).raw =
      PolyTerm.atom (profile := profile) linearModeGeneratorSpec.cellId 0 := rfl

/-- Raw erasure of the first certified application helper is definitional. -/
theorem raw_applicationVarZeroVarOne {profile : PolyProfile} {scope : Nat}
    (functionCell :
      PolyCell profile .term 0 scope ()
        (.atom variableGeneratorSpec.cellId 0))
    (argumentCell :
      PolyCell profile .term 0 scope ()
        (.atom variableGeneratorSpec.cellId 1)) :
    (applicationVarZeroVarOneCell functionCell argumentCell).raw =
      PolyTerm.atom (profile := profile) applicationGeneratorSpec.cellId
        applicationVarZeroVarOnePayload := rfl

/-- Raw erasure of a derived identity cell is definitional. -/
theorem raw_identityCell {profile : PolyProfile} {cellSort : CellSort}
    {cellDimension scope : Nat}
    {cellBoundary : CellBoundary profile cellSort cellDimension scope}
    {baseRaw : PolyTerm profile cellDimension}
    (baseCell :
      PolyCell profile cellSort cellDimension scope cellBoundary baseRaw) :
    (identityCell baseCell).raw =
      PolyTerm.identity (profile := profile) baseRaw := rfl

/-- The certified child spine for the first application payload has the
application generator arity. -/
theorem applicationVarZeroVarOneChildren_arity_eq_generator
    {profile : PolyProfile} {scope : Nat}
    (functionCell :
      PolyCell profile .term 0 scope ()
        (.atom variableGeneratorSpec.cellId 0))
    (argumentCell :
      PolyCell profile .term 0 scope ()
        (.atom variableGeneratorSpec.cellId 1)) :
    (applicationVarZeroVarOneChildren functionCell argumentCell).arity =
      applicationGeneratorSpec.arity := rfl

end PolyCell

end LeanFX2.Foundation.PolyCell.Core
