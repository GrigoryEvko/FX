import LeanFX2.Foundation.PolyCell.Core.GeneratorSpec
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
  /-- Application term generator. Payload decoding is not implemented yet. -/
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

/-- Seed rule specs currently admitted by the certified structural layer.

The rule evidence only records that the rule id/sort/dimension metadata is in
the supported table.  It does not prove the operational semantics of that
rule. -/
inductive SupportedRuleSpec : RuleSpec → Type where
  /-- Current dim-1 term-step rule shell. -/
  | termStep :
      SupportedRuleSpec termStepRuleSpec

/-- Payload evidence for atom generators that are already safe to certify.

The absence of constructors for lambda/application/pi/context-extension is
intentional: until payload decoding is real, those atoms cannot be certified
by this file. -/
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

end PolyCell

end LeanFX2.Foundation.PolyCell.Core
