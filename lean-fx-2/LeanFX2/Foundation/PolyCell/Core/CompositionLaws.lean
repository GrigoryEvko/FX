import LeanFX2.Foundation.PolyCell.Core.Fold
/-!
# PolyTerm Composition Scaffolds

This file records syntactic higher cells for the composition shapes needed by
the PolyCell plan.  It does not prove strict category equations, boundary
compatibility, or interchange laws.  Those are later construction levels.

The shipped content is deliberately smaller:

- rule-id constants for the intended composition coherence cells,
- syntactic cells connecting the intended tree shapes,
- definitional size and fold equations.

Reference target: polycell.md §4, Burroni 1993 §2.
Zero external dependencies.
-/

namespace LeanFX2.Foundation.PolyCell.Core

universe u

/-- Construction milestones for the current Core namespace.
The ledger is an honesty boundary: later stages must move this value forward
only when the corresponding data or theorem is present in Lean. -/
inductive CoreConstructionLevel where
  /-- The five-constructor indexed syntax exists. -/
  | structuralInductive : CoreConstructionLevel
  /-- The structural catamorphism exists. -/
  | foldCatamorphism : CoreConstructionLevel
  /-- Syntactic composition/coherence cells exist, without boundary checks. -/
  | compositionScaffold : CoreConstructionLevel
  /-- Vertical composition can require explicit source/target evidence. -/
  | verticalBoundaryEvidence : CoreConstructionLevel
  /-- Composition checks source and target boundaries. -/
  | boundaryCheckedComposition : CoreConstructionLevel
  /-- Associativity, unit, and interchange laws are proved. -/
  | strictCategoryLawProofs : CoreConstructionLevel
  /-- Legacy `Term`/`Step`/`Conv` views are bridged to the Core syntax. -/
  | legacyReplacementBridge : CoreConstructionLevel
  /-- Concrete rename/substitution/evaluation/complete-development algebras exist. -/
  | concreteOperationSuite : CoreConstructionLevel
  deriving DecidableEq, Repr

/-- Has the structural `PolyTerm` inductive shipped? -/
def CoreConstructionLevel.hasStructuralInductive : CoreConstructionLevel → Bool
  | .structuralInductive => true
  | .foldCatamorphism => true
  | .compositionScaffold => true
  | .verticalBoundaryEvidence => true
  | .boundaryCheckedComposition => true
  | .strictCategoryLawProofs => true
  | .legacyReplacementBridge => true
  | .concreteOperationSuite => true

/-- Has the structural fold shipped? -/
def CoreConstructionLevel.hasFoldCatamorphism : CoreConstructionLevel → Bool
  | .structuralInductive => false
  | .foldCatamorphism => true
  | .compositionScaffold => true
  | .verticalBoundaryEvidence => true
  | .boundaryCheckedComposition => true
  | .strictCategoryLawProofs => true
  | .legacyReplacementBridge => true
  | .concreteOperationSuite => true

/-- Has the syntactic composition-cell scaffold shipped? -/
def CoreConstructionLevel.hasCompositionScaffold : CoreConstructionLevel → Bool
  | .structuralInductive => false
  | .foldCatamorphism => false
  | .compositionScaffold => true
  | .verticalBoundaryEvidence => true
  | .boundaryCheckedComposition => true
  | .strictCategoryLawProofs => true
  | .legacyReplacementBridge => true
  | .concreteOperationSuite => true

/-- Can vertical composition be guarded by explicit boundary evidence? -/
def CoreConstructionLevel.hasVerticalBoundaryEvidence :
    CoreConstructionLevel → Bool
  | .structuralInductive => false
  | .foldCatamorphism => false
  | .compositionScaffold => false
  | .verticalBoundaryEvidence => true
  | .boundaryCheckedComposition => true
  | .strictCategoryLawProofs => true
  | .legacyReplacementBridge => true
  | .concreteOperationSuite => true

/-- Does composition enforce source/target boundary compatibility? -/
def CoreConstructionLevel.hasBoundaryCheckedComposition :
    CoreConstructionLevel → Bool
  | .structuralInductive => false
  | .foldCatamorphism => false
  | .compositionScaffold => false
  | .verticalBoundaryEvidence => false
  | .boundaryCheckedComposition => true
  | .strictCategoryLawProofs => true
  | .legacyReplacementBridge => true
  | .concreteOperationSuite => true

/-- Are strict associativity, unit, and interchange laws proved? -/
def CoreConstructionLevel.hasStrictCategoryLawProofs :
    CoreConstructionLevel → Bool
  | .structuralInductive => false
  | .foldCatamorphism => false
  | .compositionScaffold => false
  | .verticalBoundaryEvidence => false
  | .boundaryCheckedComposition => false
  | .strictCategoryLawProofs => true
  | .legacyReplacementBridge => true
  | .concreteOperationSuite => true

/-- Is there a legacy replacement bridge for `Term`/`Step`/`Conv`? -/
def CoreConstructionLevel.hasLegacyReplacementBridge :
    CoreConstructionLevel → Bool
  | .structuralInductive => false
  | .foldCatamorphism => false
  | .compositionScaffold => false
  | .verticalBoundaryEvidence => false
  | .boundaryCheckedComposition => false
  | .strictCategoryLawProofs => false
  | .legacyReplacementBridge => true
  | .concreteOperationSuite => true

/-- Do concrete operation algebras exist for the planned kernel operations? -/
def CoreConstructionLevel.hasConcreteOperationSuite :
    CoreConstructionLevel → Bool
  | .structuralInductive => false
  | .foldCatamorphism => false
  | .compositionScaffold => false
  | .verticalBoundaryEvidence => false
  | .boundaryCheckedComposition => false
  | .strictCategoryLawProofs => false
  | .legacyReplacementBridge => false
  | .concreteOperationSuite => true

/-- Current Core status: syntax, fold, composition scaffolds, and explicit
vertical-boundary evidence for checked sequential composition. -/
def fxCoreConstructionLevel : CoreConstructionLevel :=
  .verticalBoundaryEvidence

theorem fxCoreConstructionLevel_eq :
    fxCoreConstructionLevel =
      CoreConstructionLevel.verticalBoundaryEvidence := rfl

theorem fxCore_hasStructuralInductive :
    fxCoreConstructionLevel.hasStructuralInductive = true := rfl

theorem fxCore_hasFoldCatamorphism :
    fxCoreConstructionLevel.hasFoldCatamorphism = true := rfl

theorem fxCore_hasCompositionScaffold :
    fxCoreConstructionLevel.hasCompositionScaffold = true := rfl

theorem fxCore_hasVerticalBoundaryEvidence :
    fxCoreConstructionLevel.hasVerticalBoundaryEvidence = true := rfl

theorem fxCore_hasNoBoundaryCheckedComposition :
    fxCoreConstructionLevel.hasBoundaryCheckedComposition = false := rfl

theorem fxCore_hasNoStrictCategoryLawProofs :
    fxCoreConstructionLevel.hasStrictCategoryLawProofs = false := rfl

theorem fxCore_hasNoLegacyReplacementBridge :
    fxCoreConstructionLevel.hasLegacyReplacementBridge = false := rfl

theorem fxCore_hasNoConcreteOperationSuite :
    fxCoreConstructionLevel.hasConcreteOperationSuite = false := rfl

/-- Provisional rule id for the vertical associator scaffold. -/
def verticalAssociatorRuleId : CellId := 0

/-- Provisional rule id for the vertical left-unitor scaffold. -/
def verticalLeftUnitorRuleId : CellId := 1

/-- Provisional rule id for the vertical right-unitor scaffold. -/
def verticalRightUnitorRuleId : CellId := 2

/-- Provisional rule id for the horizontal associator scaffold. -/
def horizontalAssociatorRuleId : CellId := 3

/-- Provisional rule id for the interchange scaffold. -/
def interchangeRuleId : CellId := 4

/-- Proof-relevant endpoint data for a positive-dimensional `PolyTerm`.
This records the source and target exposed by the structural boundary
projection.  It does not assert equality between those endpoints or validate
that a composite's middle boundary was checked. -/
structure PolyTerm.EndpointEvidence {profile : PolyProfile}
    {dimension : CellDim}
    (cell : PolyTerm profile (dimension + 1)) where
  /-- The source cell exposed by the structural boundary projection. -/
  sourceCell : PolyTerm profile dimension
  /-- The target cell exposed by the structural boundary projection. -/
  targetCell : PolyTerm profile dimension
  /-- The source projection computes to `sourceCell`. -/
  source_eq : cell.source? = some sourceCell
  /-- The target projection computes to `targetCell`. -/
  target_eq : cell.target? = some targetCell

/-- Endpoint evidence for a generator cell. -/
def PolyTerm.EndpointEvidence.cell {profile : PolyProfile}
    {dimension : CellDim}
    (ruleId : CellId)
    (source target : PolyTerm profile dimension) :
    PolyTerm.EndpointEvidence (.cell ruleId source target) where
  sourceCell := source
  targetCell := target
  source_eq := PolyTerm.source?_cell ruleId source target
  target_eq := PolyTerm.target?_cell ruleId source target

/-- Endpoint evidence for an identity cell. -/
def PolyTerm.EndpointEvidence.identity {profile : PolyProfile}
    {dimension : CellDim}
    (base : PolyTerm profile dimension) :
    PolyTerm.EndpointEvidence (.identity base) where
  sourceCell := base
  targetCell := base
  source_eq := PolyTerm.source?_identity base
  target_eq := PolyTerm.target?_identity base

/-- Endpoint evidence for a raw vertical composite.
This records only outer endpoints; it does not require or manufacture middle
boundary compatibility. -/
def PolyTerm.EndpointEvidence.compV {profile : PolyProfile}
    {dimension : CellDim}
    {first second : PolyTerm profile (dimension + 1)}
    (firstEndpointEvidence : PolyTerm.EndpointEvidence first)
    (secondEndpointEvidence : PolyTerm.EndpointEvidence second) :
    PolyTerm.EndpointEvidence (.compV first second) where
  sourceCell := firstEndpointEvidence.sourceCell
  targetCell := secondEndpointEvidence.targetCell
  source_eq := by
    rw [PolyTerm.source?_compV]
    exact firstEndpointEvidence.source_eq
  target_eq := by
    rw [PolyTerm.target?_compV]
    exact secondEndpointEvidence.target_eq

/-- Evidence that two positive-dimensional cells share the boundary needed
for sequential composition.  This is a proof-relevant guard for the current
raw `compV`; it does not yet make `compV` itself boundary-indexed. -/
structure PolyTerm.VerticalBoundaryEvidence {profile : PolyProfile}
    {dimension : CellDim}
    (first second : PolyTerm profile (dimension + 1)) where
  /-- The shared lower-dimensional boundary. -/
  middle : PolyTerm profile dimension
  /-- The first cell targets the shared boundary. -/
  firstTarget_eq : first.target? = some middle
  /-- The second cell starts at the shared boundary. -/
  secondSource_eq : second.source? = some middle

/-- Boundary evidence determines the actual endpoint equality required for
sequential composition. -/
theorem PolyTerm.VerticalBoundaryEvidence.firstTarget?_eq_secondSource?
    {profile : PolyProfile} {dimension : CellDim}
    {first second : PolyTerm profile (dimension + 1)}
    (boundaryEvidence : PolyTerm.VerticalBoundaryEvidence first second) :
    first.target? = second.source? := by
  rw [boundaryEvidence.firstTarget_eq, boundaryEvidence.secondSource_eq]

/-- Checked vertical composition: callers must provide explicit evidence that
the target of the first cell and source of the second cell agree. -/
def PolyTerm.compVChecked {profile : PolyProfile} {dimension : CellDim}
    (first second : PolyTerm profile (dimension + 1))
    (_boundaryEvidence : PolyTerm.VerticalBoundaryEvidence first second) :
    PolyTerm profile (dimension + 1) :=
  .compV first second

theorem PolyTerm.compVChecked_eq_compV {profile : PolyProfile}
    {dimension : CellDim}
    (first second : PolyTerm profile (dimension + 1))
    (boundaryEvidence : PolyTerm.VerticalBoundaryEvidence first second) :
    PolyTerm.compVChecked first second boundaryEvidence =
      PolyTerm.compV first second := rfl

theorem PolyTerm.source?_compVChecked {profile : PolyProfile}
    {dimension : CellDim}
    (first second : PolyTerm profile (dimension + 1))
    (boundaryEvidence : PolyTerm.VerticalBoundaryEvidence first second) :
    (PolyTerm.compVChecked first second boundaryEvidence).source? =
      first.source? := rfl

theorem PolyTerm.target?_compVChecked {profile : PolyProfile}
    {dimension : CellDim}
    (first second : PolyTerm profile (dimension + 1))
    (boundaryEvidence : PolyTerm.VerticalBoundaryEvidence first second) :
    (PolyTerm.compVChecked first second boundaryEvidence).target? =
      second.target? := rfl

/-- Endpoint evidence for checked vertical composition.
The supplied boundary evidence validates the middle boundary; endpoint evidence
records the outer source and target. -/
def PolyTerm.EndpointEvidence.compVChecked {profile : PolyProfile}
    {dimension : CellDim}
    {first second : PolyTerm profile (dimension + 1)}
    (boundaryEvidence : PolyTerm.VerticalBoundaryEvidence first second)
    (firstEndpointEvidence : PolyTerm.EndpointEvidence first)
    (secondEndpointEvidence : PolyTerm.EndpointEvidence second) :
    PolyTerm.EndpointEvidence
      (PolyTerm.compVChecked first second boundaryEvidence) where
  sourceCell := firstEndpointEvidence.sourceCell
  targetCell := secondEndpointEvidence.targetCell
  source_eq := by
    rw [PolyTerm.source?_compVChecked]
    exact firstEndpointEvidence.source_eq
  target_eq := by
    rw [PolyTerm.target?_compVChecked]
    exact secondEndpointEvidence.target_eq

/-- Boundary evidence for composing two generator cells through the same
middle cell. -/
def PolyTerm.VerticalBoundaryEvidence.cellCell {profile : PolyProfile}
    {dimension : CellDim}
    (firstRuleId secondRuleId : CellId)
    (source middle target : PolyTerm profile dimension) :
    PolyTerm.VerticalBoundaryEvidence
      (.cell firstRuleId source middle)
      (.cell secondRuleId middle target) where
  middle := middle
  firstTarget_eq := PolyTerm.target?_cell firstRuleId source middle
  secondSource_eq := PolyTerm.source?_cell secondRuleId middle target

/-- Boundary evidence for composing an identity on the left when the following
cell exposes the same source. -/
def PolyTerm.VerticalBoundaryEvidence.identityLeft {profile : PolyProfile}
    {dimension : CellDim}
    (base : PolyTerm profile dimension)
    (cell : PolyTerm profile (dimension + 1))
    (cellSource_eq : cell.source? = some base) :
    PolyTerm.VerticalBoundaryEvidence (.identity base) cell where
  middle := base
  firstTarget_eq := PolyTerm.target?_identity base
  secondSource_eq := cellSource_eq

/-- Boundary evidence for composing an identity on the right when the previous
cell exposes the same target. -/
def PolyTerm.VerticalBoundaryEvidence.identityRight {profile : PolyProfile}
    {dimension : CellDim}
    (cell : PolyTerm profile (dimension + 1))
    (base : PolyTerm profile dimension)
    (cellTarget_eq : cell.target? = some base) :
    PolyTerm.VerticalBoundaryEvidence cell (.identity base) where
  middle := base
  firstTarget_eq := cellTarget_eq
  secondSource_eq := PolyTerm.source?_identity base

/-- Boundary evidence for composing `(first ; second)` with `third`, assuming
both adjacent boundaries were already checked.  This is only evidence
transport through `compVChecked`, not an associativity theorem. -/
def PolyTerm.VerticalBoundaryEvidence.compVLeft {profile : PolyProfile}
    {dimension : CellDim}
    (first second third : PolyTerm profile (dimension + 1))
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first second)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second third) :
    PolyTerm.VerticalBoundaryEvidence
      (PolyTerm.compVChecked first second firstSecondEvidence)
      third where
  middle := secondThirdEvidence.middle
  firstTarget_eq := by
    rw [PolyTerm.target?_compVChecked]
    exact secondThirdEvidence.firstTarget_eq
  secondSource_eq := secondThirdEvidence.secondSource_eq

/-- Boundary evidence for composing `first` with `(second ; third)`, assuming
both adjacent boundaries were already checked.  This keeps checked chains
usable without asserting a category law. -/
def PolyTerm.VerticalBoundaryEvidence.compVRight {profile : PolyProfile}
    {dimension : CellDim}
    (first second third : PolyTerm profile (dimension + 1))
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first second)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second third) :
    PolyTerm.VerticalBoundaryEvidence
      first
      (PolyTerm.compVChecked second third secondThirdEvidence) where
  middle := firstSecondEvidence.middle
  firstTarget_eq := firstSecondEvidence.firstTarget_eq
  secondSource_eq := by
    rw [PolyTerm.source?_compVChecked]
    exact firstSecondEvidence.secondSource_eq

/-- Checked left-associated composition of three cells.  This constructs the
syntax tree `(first ; second) ; third` using only adjacent boundary evidence;
it does not identify it with the right-associated tree. -/
def PolyTerm.compVCheckedLeftAssociated {profile : PolyProfile}
    {dimension : CellDim}
    (first second third : PolyTerm profile (dimension + 1))
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first second)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second third) :
    PolyTerm profile (dimension + 1) :=
  PolyTerm.compVChecked
    (PolyTerm.compVChecked first second firstSecondEvidence)
    third
    (PolyTerm.VerticalBoundaryEvidence.compVLeft
      first second third firstSecondEvidence secondThirdEvidence)

/-- Checked right-associated composition of three cells.  This constructs the
syntax tree `first ; (second ; third)` using only adjacent boundary evidence;
it is deliberately separate from `compVCheckedLeftAssociated`. -/
def PolyTerm.compVCheckedRightAssociated {profile : PolyProfile}
    {dimension : CellDim}
    (first second third : PolyTerm profile (dimension + 1))
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first second)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second third) :
    PolyTerm profile (dimension + 1) :=
  PolyTerm.compVChecked
    first
    (PolyTerm.compVChecked second third secondThirdEvidence)
    (PolyTerm.VerticalBoundaryEvidence.compVRight
      first second third firstSecondEvidence secondThirdEvidence)

theorem PolyTerm.source?_compVCheckedLeftAssociated
    {profile : PolyProfile} {dimension : CellDim}
    (first second third : PolyTerm profile (dimension + 1))
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first second)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second third) :
    (PolyTerm.compVCheckedLeftAssociated
      first second third firstSecondEvidence secondThirdEvidence).source? =
      first.source? := by
  rw [PolyTerm.compVCheckedLeftAssociated, PolyTerm.source?_compVChecked,
    PolyTerm.source?_compVChecked]

theorem PolyTerm.target?_compVCheckedLeftAssociated
    {profile : PolyProfile} {dimension : CellDim}
    (first second third : PolyTerm profile (dimension + 1))
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first second)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second third) :
    (PolyTerm.compVCheckedLeftAssociated
      first second third firstSecondEvidence secondThirdEvidence).target? =
      third.target? := by
  rw [PolyTerm.compVCheckedLeftAssociated, PolyTerm.target?_compVChecked]

theorem PolyTerm.source?_compVCheckedRightAssociated
    {profile : PolyProfile} {dimension : CellDim}
    (first second third : PolyTerm profile (dimension + 1))
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first second)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second third) :
    (PolyTerm.compVCheckedRightAssociated
      first second third firstSecondEvidence secondThirdEvidence).source? =
      first.source? := by
  rw [PolyTerm.compVCheckedRightAssociated, PolyTerm.source?_compVChecked]

theorem PolyTerm.target?_compVCheckedRightAssociated
    {profile : PolyProfile} {dimension : CellDim}
    (first second third : PolyTerm profile (dimension + 1))
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first second)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second third) :
    (PolyTerm.compVCheckedRightAssociated
      first second third firstSecondEvidence secondThirdEvidence).target? =
      third.target? := by
  rw [PolyTerm.compVCheckedRightAssociated, PolyTerm.target?_compVChecked,
    PolyTerm.target?_compVChecked]

/-- Checked left-associated composition specialized to three generator cells
with explicit dim-`dimension` endpoints. -/
def PolyTerm.compVThreeCellsCheckedLeftAssociated {profile : PolyProfile}
    {dimension : CellDim}
    (firstRuleId secondRuleId thirdRuleId : CellId)
    (source firstMiddle secondMiddle target : PolyTerm profile dimension) :
    PolyTerm profile (dimension + 1) :=
  PolyTerm.compVCheckedLeftAssociated
    (.cell firstRuleId source firstMiddle)
    (.cell secondRuleId firstMiddle secondMiddle)
    (.cell thirdRuleId secondMiddle target)
    (PolyTerm.VerticalBoundaryEvidence.cellCell firstRuleId secondRuleId
      source firstMiddle secondMiddle)
    (PolyTerm.VerticalBoundaryEvidence.cellCell secondRuleId thirdRuleId
      firstMiddle secondMiddle target)

/-- Checked right-associated composition specialized to three generator cells
with explicit dim-`dimension` endpoints. -/
def PolyTerm.compVThreeCellsCheckedRightAssociated {profile : PolyProfile}
    {dimension : CellDim}
    (firstRuleId secondRuleId thirdRuleId : CellId)
    (source firstMiddle secondMiddle target : PolyTerm profile dimension) :
    PolyTerm profile (dimension + 1) :=
  PolyTerm.compVCheckedRightAssociated
    (.cell firstRuleId source firstMiddle)
    (.cell secondRuleId firstMiddle secondMiddle)
    (.cell thirdRuleId secondMiddle target)
    (PolyTerm.VerticalBoundaryEvidence.cellCell firstRuleId secondRuleId
      source firstMiddle secondMiddle)
    (PolyTerm.VerticalBoundaryEvidence.cellCell secondRuleId thirdRuleId
      firstMiddle secondMiddle target)

theorem PolyTerm.source?_compVThreeCellsCheckedLeftAssociated
    {profile : PolyProfile} {dimension : CellDim}
    (firstRuleId secondRuleId thirdRuleId : CellId)
    (source firstMiddle secondMiddle target : PolyTerm profile dimension) :
    (PolyTerm.compVThreeCellsCheckedLeftAssociated
      firstRuleId secondRuleId thirdRuleId
      source firstMiddle secondMiddle target).source? =
      some source := by
  rw [PolyTerm.compVThreeCellsCheckedLeftAssociated,
    PolyTerm.source?_compVCheckedLeftAssociated, PolyTerm.source?_cell]

theorem PolyTerm.target?_compVThreeCellsCheckedLeftAssociated
    {profile : PolyProfile} {dimension : CellDim}
    (firstRuleId secondRuleId thirdRuleId : CellId)
    (source firstMiddle secondMiddle target : PolyTerm profile dimension) :
    (PolyTerm.compVThreeCellsCheckedLeftAssociated
      firstRuleId secondRuleId thirdRuleId
      source firstMiddle secondMiddle target).target? =
      some target := by
  rw [PolyTerm.compVThreeCellsCheckedLeftAssociated,
    PolyTerm.target?_compVCheckedLeftAssociated, PolyTerm.target?_cell]

theorem PolyTerm.source?_compVThreeCellsCheckedRightAssociated
    {profile : PolyProfile} {dimension : CellDim}
    (firstRuleId secondRuleId thirdRuleId : CellId)
    (source firstMiddle secondMiddle target : PolyTerm profile dimension) :
    (PolyTerm.compVThreeCellsCheckedRightAssociated
      firstRuleId secondRuleId thirdRuleId
      source firstMiddle secondMiddle target).source? =
      some source := by
  rw [PolyTerm.compVThreeCellsCheckedRightAssociated,
    PolyTerm.source?_compVCheckedRightAssociated, PolyTerm.source?_cell]

theorem PolyTerm.target?_compVThreeCellsCheckedRightAssociated
    {profile : PolyProfile} {dimension : CellDim}
    (firstRuleId secondRuleId thirdRuleId : CellId)
    (source firstMiddle secondMiddle target : PolyTerm profile dimension) :
    (PolyTerm.compVThreeCellsCheckedRightAssociated
      firstRuleId secondRuleId thirdRuleId
      source firstMiddle secondMiddle target).target? =
      some target := by
  rw [PolyTerm.compVThreeCellsCheckedRightAssociated,
    PolyTerm.target?_compVCheckedRightAssociated, PolyTerm.target?_cell]

/-- Boundary-aware associator scaffold.  Its endpoints are the two checked
three-cell chain shapes; this is a higher cell, not a proof that the two
endpoint terms are propositionally equal. -/
def PolyTerm.associatorVChecked {profile : PolyProfile} {dimension : CellDim}
    (first second third : PolyTerm profile (dimension + 1))
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first second)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second third) :
    PolyTerm profile (dimension + 2) :=
  .cell verticalAssociatorRuleId
    (PolyTerm.compVCheckedLeftAssociated
      first second third firstSecondEvidence secondThirdEvidence)
    (PolyTerm.compVCheckedRightAssociated
      first second third firstSecondEvidence secondThirdEvidence)

theorem PolyTerm.source?_associatorVChecked
    {profile : PolyProfile} {dimension : CellDim}
    (first second third : PolyTerm profile (dimension + 1))
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first second)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second third) :
    (PolyTerm.associatorVChecked
      first second third firstSecondEvidence secondThirdEvidence).source? =
      some (PolyTerm.compVCheckedLeftAssociated
        first second third firstSecondEvidence secondThirdEvidence) := by
  rw [PolyTerm.associatorVChecked, PolyTerm.source?_cell]

theorem PolyTerm.target?_associatorVChecked
    {profile : PolyProfile} {dimension : CellDim}
    (first second third : PolyTerm profile (dimension + 1))
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first second)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second third) :
    (PolyTerm.associatorVChecked
      first second third firstSecondEvidence secondThirdEvidence).target? =
      some (PolyTerm.compVCheckedRightAssociated
        first second third firstSecondEvidence secondThirdEvidence) := by
  rw [PolyTerm.associatorVChecked, PolyTerm.target?_cell]

/-- Endpoint evidence for the checked associator scaffold.
This records the two bracketing trees as endpoints; it is not an
associativity theorem. -/
def PolyTerm.EndpointEvidence.associatorVChecked {profile : PolyProfile}
    {dimension : CellDim}
    (first second third : PolyTerm profile (dimension + 1))
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first second)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second third) :
    PolyTerm.EndpointEvidence
      (PolyTerm.associatorVChecked
        first second third firstSecondEvidence secondThirdEvidence) where
  sourceCell :=
    PolyTerm.compVCheckedLeftAssociated
      first second third firstSecondEvidence secondThirdEvidence
  targetCell :=
    PolyTerm.compVCheckedRightAssociated
      first second third firstSecondEvidence secondThirdEvidence
  source_eq :=
    PolyTerm.source?_associatorVChecked
      first second third firstSecondEvidence secondThirdEvidence
  target_eq :=
    PolyTerm.target?_associatorVChecked
      first second third firstSecondEvidence secondThirdEvidence

/-- Boundary-aware left-unitor scaffold.  The source endpoint uses checked
composition with an identity cell, and the target is the original cell. -/
def PolyTerm.leftUnitorVChecked {profile : PolyProfile} {dimension : CellDim}
    (source : PolyTerm profile dimension)
    (cell : PolyTerm profile (dimension + 1))
    (cellSource_eq : cell.source? = some source) :
    PolyTerm profile (dimension + 2) :=
  .cell verticalLeftUnitorRuleId
    (PolyTerm.compVChecked (.identity source) cell
      (PolyTerm.VerticalBoundaryEvidence.identityLeft
        source cell cellSource_eq))
    cell

theorem PolyTerm.source?_leftUnitorVChecked
    {profile : PolyProfile} {dimension : CellDim}
    (source : PolyTerm profile dimension)
    (cell : PolyTerm profile (dimension + 1))
    (cellSource_eq : cell.source? = some source) :
    (PolyTerm.leftUnitorVChecked source cell cellSource_eq).source? =
      some (PolyTerm.compVChecked (.identity source) cell
        (PolyTerm.VerticalBoundaryEvidence.identityLeft
          source cell cellSource_eq)) := by
  rw [PolyTerm.leftUnitorVChecked, PolyTerm.source?_cell]

theorem PolyTerm.target?_leftUnitorVChecked
    {profile : PolyProfile} {dimension : CellDim}
    (source : PolyTerm profile dimension)
    (cell : PolyTerm profile (dimension + 1))
    (cellSource_eq : cell.source? = some source) :
    (PolyTerm.leftUnitorVChecked source cell cellSource_eq).target? =
      some cell := by
  rw [PolyTerm.leftUnitorVChecked, PolyTerm.target?_cell]

/-- Endpoint evidence for the checked left-unitor scaffold.
This records the checked `id ; cell` tree and the original cell as endpoints;
it is not a unit law. -/
def PolyTerm.EndpointEvidence.leftUnitorVChecked {profile : PolyProfile}
    {dimension : CellDim}
    (source : PolyTerm profile dimension)
    (cell : PolyTerm profile (dimension + 1))
    (cellSource_eq : cell.source? = some source) :
    PolyTerm.EndpointEvidence
      (PolyTerm.leftUnitorVChecked source cell cellSource_eq) where
  sourceCell :=
    PolyTerm.compVChecked (.identity source) cell
      (PolyTerm.VerticalBoundaryEvidence.identityLeft
        source cell cellSource_eq)
  targetCell := cell
  source_eq :=
    PolyTerm.source?_leftUnitorVChecked source cell cellSource_eq
  target_eq :=
    PolyTerm.target?_leftUnitorVChecked source cell cellSource_eq

/-- Boundary-aware right-unitor scaffold.  The source endpoint uses checked
composition with an identity cell, and the target is the original cell. -/
def PolyTerm.rightUnitorVChecked {profile : PolyProfile} {dimension : CellDim}
    (target : PolyTerm profile dimension)
    (cell : PolyTerm profile (dimension + 1))
    (cellTarget_eq : cell.target? = some target) :
    PolyTerm profile (dimension + 2) :=
  .cell verticalRightUnitorRuleId
    (PolyTerm.compVChecked cell (.identity target)
      (PolyTerm.VerticalBoundaryEvidence.identityRight
        cell target cellTarget_eq))
    cell

theorem PolyTerm.source?_rightUnitorVChecked
    {profile : PolyProfile} {dimension : CellDim}
    (target : PolyTerm profile dimension)
    (cell : PolyTerm profile (dimension + 1))
    (cellTarget_eq : cell.target? = some target) :
    (PolyTerm.rightUnitorVChecked target cell cellTarget_eq).source? =
      some (PolyTerm.compVChecked cell (.identity target)
        (PolyTerm.VerticalBoundaryEvidence.identityRight
          cell target cellTarget_eq)) := by
  rw [PolyTerm.rightUnitorVChecked, PolyTerm.source?_cell]

theorem PolyTerm.target?_rightUnitorVChecked
    {profile : PolyProfile} {dimension : CellDim}
    (target : PolyTerm profile dimension)
    (cell : PolyTerm profile (dimension + 1))
    (cellTarget_eq : cell.target? = some target) :
    (PolyTerm.rightUnitorVChecked target cell cellTarget_eq).target? =
      some cell := by
  rw [PolyTerm.rightUnitorVChecked, PolyTerm.target?_cell]

/-- Endpoint evidence for the checked right-unitor scaffold.
This records the checked `cell ; id` tree and the original cell as endpoints;
it is not a unit law. -/
def PolyTerm.EndpointEvidence.rightUnitorVChecked {profile : PolyProfile}
    {dimension : CellDim}
    (target : PolyTerm profile dimension)
    (cell : PolyTerm profile (dimension + 1))
    (cellTarget_eq : cell.target? = some target) :
    PolyTerm.EndpointEvidence
      (PolyTerm.rightUnitorVChecked target cell cellTarget_eq) where
  sourceCell :=
    PolyTerm.compVChecked cell (.identity target)
      (PolyTerm.VerticalBoundaryEvidence.identityRight
        cell target cellTarget_eq)
  targetCell := cell
  source_eq :=
    PolyTerm.source?_rightUnitorVChecked target cell cellTarget_eq
  target_eq :=
    PolyTerm.target?_rightUnitorVChecked target cell cellTarget_eq

/-- Syntactic cell connecting `(first ; second) ; third` to
`first ; (second ; third)`.  Boundary compatibility is not checked. -/
def PolyTerm.associatorV {profile : PolyProfile} {dimension : CellDim}
    (first second third : PolyTerm profile (dimension + 1)) :
    PolyTerm profile (dimension + 2) :=
  .cell verticalAssociatorRuleId
    (.compV (.compV first second) third)
    (.compV first (.compV second third))

/-- Syntactic cell connecting `id ; cell` to `cell`. -/
def PolyTerm.leftUnitorV {profile : PolyProfile} {dimension : CellDim}
    (source : PolyTerm profile dimension)
    (cell : PolyTerm profile (dimension + 1)) :
    PolyTerm profile (dimension + 2) :=
  .cell verticalLeftUnitorRuleId (.compV (.identity source) cell) cell

/-- Syntactic cell connecting `cell ; id` to `cell`. -/
def PolyTerm.rightUnitorV {profile : PolyProfile} {dimension : CellDim}
    (target : PolyTerm profile dimension)
    (cell : PolyTerm profile (dimension + 1)) :
    PolyTerm profile (dimension + 2) :=
  .cell verticalRightUnitorRuleId (.compV cell (.identity target)) cell

/-- Syntactic cell connecting `(first tensor second) tensor third` to
`first tensor (second tensor third)`. -/
def PolyTerm.associatorH {profile : PolyProfile} {dimension : CellDim}
    (first second third : PolyTerm profile (dimension + 1)) :
    PolyTerm profile (dimension + 2) :=
  .cell horizontalAssociatorRuleId
    (.compH (.compH first second) third)
    (.compH first (.compH second third))

/-- Syntactic interchange cell.  This is not an interchange theorem. -/
def PolyTerm.interchanger {profile : PolyProfile} {dimension : CellDim}
    (leftFirst leftSecond rightFirst rightSecond :
      PolyTerm profile (dimension + 1)) :
    PolyTerm profile (dimension + 2) :=
  .cell interchangeRuleId
    (.compH (.compV leftFirst leftSecond) (.compV rightFirst rightSecond))
    (.compV (.compH leftFirst rightFirst) (.compH leftSecond rightSecond))

theorem PolyTerm.source?_associatorV {profile : PolyProfile} {dimension : CellDim}
    (first second third : PolyTerm profile (dimension + 1)) :
    (PolyTerm.associatorV first second third).source? =
      some (.compV (.compV first second) third) := by
  rw [PolyTerm.associatorV, PolyTerm.source?_cell]

theorem PolyTerm.target?_associatorV {profile : PolyProfile} {dimension : CellDim}
    (first second third : PolyTerm profile (dimension + 1)) :
    (PolyTerm.associatorV first second third).target? =
      some (.compV first (.compV second third)) := by
  rw [PolyTerm.associatorV, PolyTerm.target?_cell]

theorem PolyTerm.source?_leftUnitorV {profile : PolyProfile} {dimension : CellDim}
    (source : PolyTerm profile dimension)
    (cell : PolyTerm profile (dimension + 1)) :
    (PolyTerm.leftUnitorV source cell).source? =
      some (.compV (.identity source) cell) := by
  rw [PolyTerm.leftUnitorV, PolyTerm.source?_cell]

theorem PolyTerm.target?_leftUnitorV {profile : PolyProfile} {dimension : CellDim}
    (source : PolyTerm profile dimension)
    (cell : PolyTerm profile (dimension + 1)) :
    (PolyTerm.leftUnitorV source cell).target? =
      some cell := by
  rw [PolyTerm.leftUnitorV, PolyTerm.target?_cell]

theorem PolyTerm.source?_rightUnitorV {profile : PolyProfile} {dimension : CellDim}
    (target : PolyTerm profile dimension)
    (cell : PolyTerm profile (dimension + 1)) :
    (PolyTerm.rightUnitorV target cell).source? =
      some (.compV cell (.identity target)) := by
  rw [PolyTerm.rightUnitorV, PolyTerm.source?_cell]

theorem PolyTerm.target?_rightUnitorV {profile : PolyProfile} {dimension : CellDim}
    (target : PolyTerm profile dimension)
    (cell : PolyTerm profile (dimension + 1)) :
    (PolyTerm.rightUnitorV target cell).target? =
      some cell := by
  rw [PolyTerm.rightUnitorV, PolyTerm.target?_cell]

theorem PolyTerm.source?_associatorH {profile : PolyProfile} {dimension : CellDim}
    (first second third : PolyTerm profile (dimension + 1)) :
    (PolyTerm.associatorH first second third).source? =
      some (.compH (.compH first second) third) := by
  rw [PolyTerm.associatorH, PolyTerm.source?_cell]

theorem PolyTerm.target?_associatorH {profile : PolyProfile} {dimension : CellDim}
    (first second third : PolyTerm profile (dimension + 1)) :
    (PolyTerm.associatorH first second third).target? =
      some (.compH first (.compH second third)) := by
  rw [PolyTerm.associatorH, PolyTerm.target?_cell]

theorem PolyTerm.source?_interchanger {profile : PolyProfile} {dimension : CellDim}
    (leftFirst leftSecond rightFirst rightSecond :
      PolyTerm profile (dimension + 1)) :
    (PolyTerm.interchanger
      leftFirst leftSecond rightFirst rightSecond).source? =
      some (.compH
        (.compV leftFirst leftSecond)
        (.compV rightFirst rightSecond)) := by
  rw [PolyTerm.interchanger, PolyTerm.source?_cell]

theorem PolyTerm.target?_interchanger {profile : PolyProfile} {dimension : CellDim}
    (leftFirst leftSecond rightFirst rightSecond :
      PolyTerm profile (dimension + 1)) :
    (PolyTerm.interchanger
      leftFirst leftSecond rightFirst rightSecond).target? =
      some (.compV
        (.compH leftFirst rightFirst)
        (.compH leftSecond rightSecond)) := by
  rw [PolyTerm.interchanger, PolyTerm.target?_cell]

/-- Endpoint evidence for the raw vertical associator scaffold.
This records the two raw bracketing trees and does not check boundaries. -/
def PolyTerm.EndpointEvidence.associatorV {profile : PolyProfile}
    {dimension : CellDim}
    (first second third : PolyTerm profile (dimension + 1)) :
    PolyTerm.EndpointEvidence (PolyTerm.associatorV first second third) where
  sourceCell := .compV (.compV first second) third
  targetCell := .compV first (.compV second third)
  source_eq := PolyTerm.source?_associatorV first second third
  target_eq := PolyTerm.target?_associatorV first second third

/-- Endpoint evidence for the raw vertical left-unitor scaffold.
This records the raw `id ; cell` tree and the original cell. -/
def PolyTerm.EndpointEvidence.leftUnitorV {profile : PolyProfile}
    {dimension : CellDim}
    (source : PolyTerm profile dimension)
    (cell : PolyTerm profile (dimension + 1)) :
    PolyTerm.EndpointEvidence (PolyTerm.leftUnitorV source cell) where
  sourceCell := .compV (.identity source) cell
  targetCell := cell
  source_eq := PolyTerm.source?_leftUnitorV source cell
  target_eq := PolyTerm.target?_leftUnitorV source cell

/-- Endpoint evidence for the raw vertical right-unitor scaffold.
This records the raw `cell ; id` tree and the original cell. -/
def PolyTerm.EndpointEvidence.rightUnitorV {profile : PolyProfile}
    {dimension : CellDim}
    (target : PolyTerm profile dimension)
    (cell : PolyTerm profile (dimension + 1)) :
    PolyTerm.EndpointEvidence (PolyTerm.rightUnitorV target cell) where
  sourceCell := .compV cell (.identity target)
  targetCell := cell
  source_eq := PolyTerm.source?_rightUnitorV target cell
  target_eq := PolyTerm.target?_rightUnitorV target cell

/-- Endpoint evidence for the raw horizontal associator scaffold.
This records the two tensor bracketing trees and does not prove a law. -/
def PolyTerm.EndpointEvidence.associatorH {profile : PolyProfile}
    {dimension : CellDim}
    (first second third : PolyTerm profile (dimension + 1)) :
    PolyTerm.EndpointEvidence (PolyTerm.associatorH first second third) where
  sourceCell := .compH (.compH first second) third
  targetCell := .compH first (.compH second third)
  source_eq := PolyTerm.source?_associatorH first second third
  target_eq := PolyTerm.target?_associatorH first second third

/-- Endpoint evidence for the raw interchange scaffold.
This records the two syntactic sides only; it is not an interchange theorem. -/
def PolyTerm.EndpointEvidence.interchanger {profile : PolyProfile}
    {dimension : CellDim}
    (leftFirst leftSecond rightFirst rightSecond :
      PolyTerm profile (dimension + 1)) :
    PolyTerm.EndpointEvidence
      (PolyTerm.interchanger
        leftFirst leftSecond rightFirst rightSecond) where
  sourceCell :=
    .compH (.compV leftFirst leftSecond) (.compV rightFirst rightSecond)
  targetCell :=
    .compV (.compH leftFirst rightFirst) (.compH leftSecond rightSecond)
  source_eq :=
    PolyTerm.source?_interchanger
      leftFirst leftSecond rightFirst rightSecond
  target_eq :=
    PolyTerm.target?_interchanger
      leftFirst leftSecond rightFirst rightSecond

/-- Size of compositions grows predictably. -/
theorem PolyTerm.size_compV {profile : PolyProfile} {dimension : CellDim}
    (first second : PolyTerm profile (dimension + 1)) :
    (compV first second).size = 1 + first.size + second.size := rfl

theorem PolyTerm.size_compH {profile : PolyProfile} {dimension : CellDim}
    (left right : PolyTerm profile (dimension + 1)) :
    (compH left right).size = 1 + left.size + right.size := rfl

theorem PolyTerm.size_identity {profile : PolyProfile} {dimension : CellDim}
    (base : PolyTerm profile dimension) :
    (identity base).size = 1 + base.size := rfl

/-- The fold of a compV is the algebra's interpretCompV applied to folded parts. -/
theorem PolyTerm.fold_compV {profile : PolyProfile} {dimension : CellDim}
    {target : CellDim → Type u}
    (algebra : PolyTermAlgebra profile target)
    (first second : PolyTerm profile (dimension + 1)) :
    fold algebra (compV first second) =
    algebra.interpretCompV (fold algebra first) (fold algebra second) := rfl

/-- The fold of a compH is the algebra's interpretCompH. -/
theorem PolyTerm.fold_compH {profile : PolyProfile} {dimension : CellDim}
    {target : CellDim → Type u}
    (algebra : PolyTermAlgebra profile target)
    (left right : PolyTerm profile (dimension + 1)) :
    fold algebra (compH left right) =
    algebra.interpretCompH (fold algebra left) (fold algebra right) := rfl

/-- The fold of an identity is the algebra's interpretIdentity. -/
theorem PolyTerm.fold_identity_cell {profile : PolyProfile} {dimension : CellDim}
    {target : CellDim → Type u}
    (algebra : PolyTermAlgebra profile target)
    (base : PolyTerm profile dimension) :
    fold algebra (identity base) = algebra.interpretIdentity (fold algebra base) := rfl

end LeanFX2.Foundation.PolyCell.Core
