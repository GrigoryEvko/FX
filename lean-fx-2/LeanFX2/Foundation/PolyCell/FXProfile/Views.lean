import LeanFX2.Foundation.PolyCell.Core.CompositionLaws
/-!
# FX View Types — Current PolyTerm Wrappers

Carve out familiar FX kernel names as wrappers around `PolyTerm fxProfile`.
The present file provides raw subtype views and simple constructors.  It does
not contain a legacy round-trip bridge, a typed equivalence to the existing
kernel, or a proof that conversions are exactly thin cells.

Reference target: polycell.md §5.
Zero external dependencies.
-/

namespace LeanFX2.Foundation.PolyCell.FXProfile

open Core

/-- Construction milestones for the FX view layer.
This records exactly how much of the planned bridge has been mechanized. -/
inductive FXViewConstructionLevel where
  /-- Raw aliases/subtypes over `PolyTerm fxProfile` exist. -/
  | rawSubtypeViews : FXViewConstructionLevel
  /-- Basic constructors and projections for those raw views exist. -/
  | rawSubtypeConstructors : FXViewConstructionLevel
  /-- Step and conversion views enforce boundary and thinness conditions. -/
  | boundaryAndThinnessCheckedViews : FXViewConstructionLevel
  /-- Legacy raw/typed syntax round-trips through the views. -/
  | legacyRoundtripBridge : FXViewConstructionLevel
  /-- Existing typed kernel objects are equivalent to the views. -/
  | typedKernelEquivalence : FXViewConstructionLevel
  deriving DecidableEq, Repr

/-- Do raw aliases/subtypes over `PolyTerm fxProfile` exist? -/
def FXViewConstructionLevel.hasRawSubtypeViews :
    FXViewConstructionLevel → Bool
  | .rawSubtypeViews => true
  | .rawSubtypeConstructors => true
  | .boundaryAndThinnessCheckedViews => true
  | .legacyRoundtripBridge => true
  | .typedKernelEquivalence => true

/-- Do basic constructors and projections for the raw views exist? -/
def FXViewConstructionLevel.hasRawSubtypeConstructors :
    FXViewConstructionLevel → Bool
  | .rawSubtypeViews => false
  | .rawSubtypeConstructors => true
  | .boundaryAndThinnessCheckedViews => true
  | .legacyRoundtripBridge => true
  | .typedKernelEquivalence => true

/-- Do step/conversion views enforce boundary and thinness conditions? -/
def FXViewConstructionLevel.hasBoundaryAndThinnessCheckedViews :
    FXViewConstructionLevel → Bool
  | .rawSubtypeViews => false
  | .rawSubtypeConstructors => false
  | .boundaryAndThinnessCheckedViews => true
  | .legacyRoundtripBridge => true
  | .typedKernelEquivalence => true

/-- Is there a legacy raw/typed round-trip bridge through the views? -/
def FXViewConstructionLevel.hasLegacyRoundtripBridge :
    FXViewConstructionLevel → Bool
  | .rawSubtypeViews => false
  | .rawSubtypeConstructors => false
  | .boundaryAndThinnessCheckedViews => false
  | .legacyRoundtripBridge => true
  | .typedKernelEquivalence => true

/-- Are existing typed kernel objects equivalent to the view types? -/
def FXViewConstructionLevel.hasTypedKernelEquivalence :
    FXViewConstructionLevel → Bool
  | .rawSubtypeViews => false
  | .rawSubtypeConstructors => false
  | .boundaryAndThinnessCheckedViews => false
  | .legacyRoundtripBridge => false
  | .typedKernelEquivalence => true

/-- Current FX view status: raw wrappers plus constructors/projections only. -/
def fxViewConstructionLevel : FXViewConstructionLevel :=
  .rawSubtypeConstructors

theorem fxViewConstructionLevel_eq :
    fxViewConstructionLevel = FXViewConstructionLevel.rawSubtypeConstructors := rfl

theorem fxView_hasRawSubtypeViews :
    fxViewConstructionLevel.hasRawSubtypeViews = true := rfl

theorem fxView_hasRawSubtypeConstructors :
    fxViewConstructionLevel.hasRawSubtypeConstructors = true := rfl

theorem fxView_hasNoBoundaryAndThinnessCheckedViews :
    fxViewConstructionLevel.hasBoundaryAndThinnessCheckedViews = false := rfl

theorem fxView_hasNoLegacyRoundtripBridge :
    fxViewConstructionLevel.hasLegacyRoundtripBridge = false := rfl

theorem fxView_hasNoTypedKernelEquivalence :
    fxViewConstructionLevel.hasTypedKernelEquivalence = false := rfl

/-- All FX cells at any dimension. -/
abbrev FXCell := PolyTerm fxProfile

/-- FX cells at a specific dimension. -/
abbrev FXCellAt (dimension : CellDim) := PolyTerm fxProfile dimension

/-- FX type cells: dim-0 atoms with cellId in the provisional type range
`[78, 103)`. -/
def FXType := { cell : FXCellAt 0 // cell.isTypeCell = true }

/-- FX term cells: dim-0 atoms with cellId in the provisional term range
`[0, 78)`. -/
def FXTerm := { cell : FXCellAt 0 // cell.isTermCell = true }

/-- Provisional FX step view: non-identity dim-1 cells.
This is not yet a boundary-checked reduction semantics. -/
def FXStep := { cell : FXCellAt 1 // cell.isStepCell = true }

/-- Provisional conversion view.  Thinness is not enforced yet. -/
def FXConv := FXCellAt 1

/-- Provisional cd_lemma filler view.  Confluence is not enforced here. -/
def FXCdLemma := FXCellAt 2

/-- Provisional Squier-coherence view. -/
def FXSquier := FXCellAt 3

/-- Construct an FX term cell. -/
def FXTerm.ofAtom (cellId : CellId) (payload : Nat)
    (hRange : (PolyTerm.atom (profile := fxProfile) cellId payload).isTermCell = true) :
    FXTerm := ⟨.atom cellId payload, hRange⟩

/-- Construct an FX type cell. -/
def FXType.ofAtom (cellId : CellId) (payload : Nat)
    (hRange : (PolyTerm.atom (profile := fxProfile) cellId payload).isTypeCell = true) :
    FXType := ⟨.atom cellId payload, hRange⟩

/-- Construct a raw FX step from a rule id plus source and target cells.
Boundary compatibility is not checked by this constructor. -/
def FXStep.mk (ruleId : CellId) (source target : FXCellAt 0) : FXStep :=
  ⟨.cell ruleId source target, rfl⟩

/-- Extract the underlying PolyTerm from a view type. -/
def FXTerm.toCell (term : FXTerm) : FXCellAt 0 := term.val
def FXType.toCell (typeCell : FXType) : FXCellAt 0 := typeCell.val
def FXStep.toCell (step : FXStep) : FXCellAt 1 := step.val

/-- Known source endpoint of a provisional FX step, when the structural
boundary projection can compute it. -/
def FXStep.source? (step : FXStep) : Option (FXCellAt 0) :=
  PolyTerm.source? (profile := fxProfile) (dimension := 0) step.val

/-- Known target endpoint of a provisional FX step, when the structural
boundary projection can compute it. -/
def FXStep.target? (step : FXStep) : Option (FXCellAt 0) :=
  PolyTerm.target? (profile := fxProfile) (dimension := 0) step.val

theorem FXStep.source?_mk (ruleId : CellId) (source target : FXCellAt 0) :
    (FXStep.mk ruleId source target).source? = some source := by
  rw [FXStep.source?, FXStep.mk, PolyTerm.source?_cell]

theorem FXStep.target?_mk (ruleId : CellId) (source target : FXCellAt 0) :
    (FXStep.mk ruleId source target).target? = some target := by
  rw [FXStep.target?, FXStep.mk, PolyTerm.target?_cell]

/-- Proof-relevant endpoint data for a provisional FX step.
This records structural endpoints only; it does not prove that the step is a
valid operational reduction rule. -/
structure FXStep.EndpointEvidence (step : FXStep) where
  /-- The source dim-0 cell exposed by the structural boundary projection. -/
  sourceCell : FXCellAt 0
  /-- The target dim-0 cell exposed by the structural boundary projection. -/
  targetCell : FXCellAt 0
  /-- The source projection computes to `sourceCell`. -/
  source_eq : step.source? = some sourceCell
  /-- The target projection computes to `targetCell`. -/
  target_eq : step.target? = some targetCell

/-- Forget FX-step naming and view endpoint evidence as generic Core evidence. -/
def FXStep.EndpointEvidence.toCore {step : FXStep}
    (endpointEvidence : FXStep.EndpointEvidence step) :
    PolyTerm.EndpointEvidence (profile := fxProfile) (dimension := 0)
      step.val where
  sourceCell := endpointEvidence.sourceCell
  targetCell := endpointEvidence.targetCell
  source_eq := endpointEvidence.source_eq
  target_eq := endpointEvidence.target_eq

/-- Specialize generic Core endpoint evidence to the FX-step view. -/
def FXStep.EndpointEvidence.ofCore {step : FXStep}
    (endpointEvidence :
      PolyTerm.EndpointEvidence (profile := fxProfile) (dimension := 0)
        step.val) :
    FXStep.EndpointEvidence step where
  sourceCell := endpointEvidence.sourceCell
  targetCell := endpointEvidence.targetCell
  source_eq := endpointEvidence.source_eq
  target_eq := endpointEvidence.target_eq

/-- Endpoint evidence for a constructor-level FX step. -/
def FXStep.endpointEvidence_mk (ruleId : CellId)
    (source target : FXCellAt 0) :
    FXStep.EndpointEvidence (FXStep.mk ruleId source target) :=
  FXStep.EndpointEvidence.ofCore
    (PolyTerm.EndpointEvidence.cell ruleId source target)

/-- Any checked pair of FX steps has matching target/source endpoints. -/
theorem FXStep.target?_eq_source?_of_boundaryEvidence
    (step1 step2 : FXStep)
    (boundaryEvidence : PolyTerm.VerticalBoundaryEvidence step1.val step2.val) :
    step1.target? = step2.source? := by
  rw [FXStep.target?, FXStep.source?]
  exact PolyTerm.VerticalBoundaryEvidence.firstTarget?_eq_secondSource?
    boundaryEvidence

/-- FX term cell id extraction. -/
def FXTerm.cellId : FXTerm → CellId
  | ⟨.atom cellId _, _⟩ => cellId

/-- FX type cell id extraction. -/
def FXType.cellId : FXType → CellId
  | ⟨.atom cellId _, _⟩ => cellId

/-- Raw vertical composition of steps.  Intermediate boundaries are not checked. -/
def FXStep.seq (step1 step2 : FXStep) : FXCellAt 1 :=
  .compV step1.val step2.val

/-- Checked vertical composition of steps.  The caller supplies concrete
evidence that `step1` targets the same dim-0 cell that `step2` starts from. -/
def FXStep.seqChecked (step1 step2 : FXStep)
    (boundaryEvidence : PolyTerm.VerticalBoundaryEvidence step1.val step2.val) :
    FXStep :=
  ⟨PolyTerm.compVChecked step1.val step2.val boundaryEvidence, rfl⟩

/-- Endpoint evidence for checked sequential composition of FX steps. -/
def FXStep.endpointEvidence_seqChecked (first second : FXStep)
    (boundaryEvidence : PolyTerm.VerticalBoundaryEvidence first.val second.val)
    (firstEndpointEvidence : FXStep.EndpointEvidence first)
    (secondEndpointEvidence : FXStep.EndpointEvidence second) :
    FXStep.EndpointEvidence
      (FXStep.seqChecked first second boundaryEvidence) :=
  FXStep.EndpointEvidence.ofCore
    (PolyTerm.EndpointEvidence.compVChecked
      boundaryEvidence
      firstEndpointEvidence.toCore
      secondEndpointEvidence.toCore)

/-- Boundary evidence for composing two freshly constructed FX steps through
the stated middle endpoint. -/
def FXStep.boundaryEvidence_mk_mk (firstRuleId secondRuleId : CellId)
    (source middle target : FXCellAt 0) :
    PolyTerm.VerticalBoundaryEvidence
      (FXStep.mk firstRuleId source middle).val
      (FXStep.mk secondRuleId middle target).val :=
  PolyTerm.VerticalBoundaryEvidence.cellCell firstRuleId secondRuleId
    source middle target

/-- Checked composition specialized to two constructor-level step cells sharing
the stated middle endpoint. -/
def FXStep.seqMkChecked (firstRuleId secondRuleId : CellId)
    (source middle target : FXCellAt 0) : FXStep :=
  FXStep.seqChecked
    (FXStep.mk firstRuleId source middle)
    (FXStep.mk secondRuleId middle target)
    (FXStep.boundaryEvidence_mk_mk firstRuleId secondRuleId
      source middle target)

/-- Endpoint evidence for checked composition of two constructor-level steps. -/
def FXStep.endpointEvidence_seqMkChecked
    (firstRuleId secondRuleId : CellId)
    (source middle target : FXCellAt 0) :
    FXStep.EndpointEvidence
      (FXStep.seqMkChecked firstRuleId secondRuleId source middle target) :=
  FXStep.endpointEvidence_seqChecked
    (FXStep.mk firstRuleId source middle)
    (FXStep.mk secondRuleId middle target)
    (FXStep.boundaryEvidence_mk_mk firstRuleId secondRuleId
      source middle target)
    (FXStep.endpointEvidence_mk firstRuleId source middle)
    (FXStep.endpointEvidence_mk secondRuleId middle target)

/-- Boundary evidence for composing `(first ; second)` with `third`, transported
from the two adjacent checked boundaries. -/
def FXStep.boundaryEvidence_seqCheckedLeft
    (first second third : FXStep)
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first.val second.val)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second.val third.val) :
    PolyTerm.VerticalBoundaryEvidence
      (FXStep.seqChecked first second firstSecondEvidence).val
      third.val :=
  PolyTerm.VerticalBoundaryEvidence.compVLeft
    first.val second.val third.val firstSecondEvidence secondThirdEvidence

/-- Boundary evidence for composing `first` with `(second ; third)`, transported
from the two adjacent checked boundaries. -/
def FXStep.boundaryEvidence_seqCheckedRight
    (first second third : FXStep)
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first.val second.val)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second.val third.val) :
    PolyTerm.VerticalBoundaryEvidence
      first.val
      (FXStep.seqChecked second third secondThirdEvidence).val :=
  PolyTerm.VerticalBoundaryEvidence.compVRight
    first.val second.val third.val firstSecondEvidence secondThirdEvidence

/-- Checked left-associated composition of three FX steps. -/
def FXStep.seqCheckedLeftAssociated
    (first second third : FXStep)
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first.val second.val)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second.val third.val) :
    FXStep :=
  ⟨PolyTerm.compVCheckedLeftAssociated
    first.val second.val third.val firstSecondEvidence secondThirdEvidence, rfl⟩

/-- Checked right-associated composition of three FX steps. -/
def FXStep.seqCheckedRightAssociated
    (first second third : FXStep)
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first.val second.val)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second.val third.val) :
    FXStep :=
  ⟨PolyTerm.compVCheckedRightAssociated
    first.val second.val third.val firstSecondEvidence secondThirdEvidence, rfl⟩

/-- Raw horizontal composition of steps.  Independence/disjointness is not checked. -/
def FXStep.par (step1 step2 : FXStep) : FXCellAt 1 :=
  .compH step1.val step2.val

theorem FXStep.source?_seq (step1 step2 : FXStep) :
    PolyTerm.source? (profile := fxProfile) (dimension := 0) (FXStep.seq step1 step2) =
      step1.source? :=
  PolyTerm.source?_compV step1.val step2.val

theorem FXStep.target?_seq (step1 step2 : FXStep) :
    PolyTerm.target? (profile := fxProfile) (dimension := 0) (FXStep.seq step1 step2) =
      step2.target? :=
  PolyTerm.target?_compV step1.val step2.val

theorem FXStep.source?_seqChecked (step1 step2 : FXStep)
    (boundaryEvidence : PolyTerm.VerticalBoundaryEvidence step1.val step2.val) :
    (FXStep.seqChecked step1 step2 boundaryEvidence).source? =
      step1.source? :=
  PolyTerm.source?_compV step1.val step2.val

theorem FXStep.target?_seqChecked (step1 step2 : FXStep)
    (boundaryEvidence : PolyTerm.VerticalBoundaryEvidence step1.val step2.val) :
    (FXStep.seqChecked step1 step2 boundaryEvidence).target? =
      step2.target? :=
  PolyTerm.target?_compV step1.val step2.val

theorem FXStep.source?_seqMkChecked (firstRuleId secondRuleId : CellId)
    (source middle target : FXCellAt 0) :
    (FXStep.seqMkChecked firstRuleId secondRuleId source middle target).source? =
      some source := by
  rw [FXStep.seqMkChecked, FXStep.source?_seqChecked, FXStep.source?_mk]

theorem FXStep.target?_seqMkChecked (firstRuleId secondRuleId : CellId)
    (source middle target : FXCellAt 0) :
    (FXStep.seqMkChecked firstRuleId secondRuleId source middle target).target? =
      some target := by
  rw [FXStep.seqMkChecked, FXStep.target?_seqChecked, FXStep.target?_mk]

theorem FXStep.source?_seqCheckedLeftAssociated
    (first second third : FXStep)
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first.val second.val)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second.val third.val) :
    (FXStep.seqCheckedLeftAssociated
      first second third firstSecondEvidence secondThirdEvidence).source? =
      first.source? := by
  rw [FXStep.seqCheckedLeftAssociated, FXStep.source?,
    PolyTerm.source?_compVCheckedLeftAssociated, FXStep.source?]

theorem FXStep.target?_seqCheckedLeftAssociated
    (first second third : FXStep)
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first.val second.val)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second.val third.val) :
    (FXStep.seqCheckedLeftAssociated
      first second third firstSecondEvidence secondThirdEvidence).target? =
      third.target? := by
  rw [FXStep.seqCheckedLeftAssociated, FXStep.target?,
    PolyTerm.target?_compVCheckedLeftAssociated, FXStep.target?]

theorem FXStep.source?_seqCheckedRightAssociated
    (first second third : FXStep)
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first.val second.val)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second.val third.val) :
    (FXStep.seqCheckedRightAssociated
      first second third firstSecondEvidence secondThirdEvidence).source? =
      first.source? := by
  rw [FXStep.seqCheckedRightAssociated, FXStep.source?,
    PolyTerm.source?_compVCheckedRightAssociated, FXStep.source?]

theorem FXStep.target?_seqCheckedRightAssociated
    (first second third : FXStep)
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first.val second.val)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second.val third.val) :
    (FXStep.seqCheckedRightAssociated
      first second third firstSecondEvidence secondThirdEvidence).target? =
      third.target? := by
  rw [FXStep.seqCheckedRightAssociated, FXStep.target?,
    PolyTerm.target?_compVCheckedRightAssociated, FXStep.target?]

/-- Endpoint evidence for checked left-associated composition of three FX steps.
This records the outer endpoints only; it is not associativity. -/
def FXStep.endpointEvidence_seqCheckedLeftAssociated
    (first second third : FXStep)
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first.val second.val)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second.val third.val)
    (firstEndpointEvidence : FXStep.EndpointEvidence first)
    (thirdEndpointEvidence : FXStep.EndpointEvidence third) :
    FXStep.EndpointEvidence
      (FXStep.seqCheckedLeftAssociated
        first second third firstSecondEvidence secondThirdEvidence) where
  sourceCell := firstEndpointEvidence.sourceCell
  targetCell := thirdEndpointEvidence.targetCell
  source_eq := by
    rw [FXStep.source?_seqCheckedLeftAssociated]
    exact firstEndpointEvidence.source_eq
  target_eq := by
    rw [FXStep.target?_seqCheckedLeftAssociated]
    exact thirdEndpointEvidence.target_eq

/-- Endpoint evidence for checked right-associated composition of three FX
steps.  This records the outer endpoints only; it is not associativity. -/
def FXStep.endpointEvidence_seqCheckedRightAssociated
    (first second third : FXStep)
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first.val second.val)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second.val third.val)
    (firstEndpointEvidence : FXStep.EndpointEvidence first)
    (thirdEndpointEvidence : FXStep.EndpointEvidence third) :
    FXStep.EndpointEvidence
      (FXStep.seqCheckedRightAssociated
        first second third firstSecondEvidence secondThirdEvidence) where
  sourceCell := firstEndpointEvidence.sourceCell
  targetCell := thirdEndpointEvidence.targetCell
  source_eq := by
    rw [FXStep.source?_seqCheckedRightAssociated]
    exact firstEndpointEvidence.source_eq
  target_eq := by
    rw [FXStep.target?_seqCheckedRightAssociated]
    exact thirdEndpointEvidence.target_eq

/-- Checked left-associated composition specialized to three constructor-level
step cells with two explicit shared endpoints.  This packages the common
`source -> firstMiddle -> secondMiddle -> target` case without asserting
associativity of the resulting syntax tree. -/
def FXStep.seqThreeMkCheckedLeftAssociated
    (firstRuleId secondRuleId thirdRuleId : CellId)
    (source firstMiddle secondMiddle target : FXCellAt 0) : FXStep :=
  ⟨PolyTerm.compVThreeCellsCheckedLeftAssociated
    firstRuleId secondRuleId thirdRuleId
    source firstMiddle secondMiddle target, rfl⟩

/-- Checked right-associated composition specialized to three constructor-level
step cells with two explicit shared endpoints.  It is a separate syntax tree
from `seqThreeMkCheckedLeftAssociated`; only endpoints are recorded here. -/
def FXStep.seqThreeMkCheckedRightAssociated
    (firstRuleId secondRuleId thirdRuleId : CellId)
    (source firstMiddle secondMiddle target : FXCellAt 0) : FXStep :=
  ⟨PolyTerm.compVThreeCellsCheckedRightAssociated
    firstRuleId secondRuleId thirdRuleId
    source firstMiddle secondMiddle target, rfl⟩

theorem FXStep.source?_seqThreeMkCheckedLeftAssociated
    (firstRuleId secondRuleId thirdRuleId : CellId)
    (source firstMiddle secondMiddle target : FXCellAt 0) :
    (FXStep.seqThreeMkCheckedLeftAssociated
      firstRuleId secondRuleId thirdRuleId
      source firstMiddle secondMiddle target).source? =
      some source := by
  rw [FXStep.seqThreeMkCheckedLeftAssociated,
    FXStep.source?, PolyTerm.source?_compVThreeCellsCheckedLeftAssociated]

theorem FXStep.target?_seqThreeMkCheckedLeftAssociated
    (firstRuleId secondRuleId thirdRuleId : CellId)
    (source firstMiddle secondMiddle target : FXCellAt 0) :
    (FXStep.seqThreeMkCheckedLeftAssociated
      firstRuleId secondRuleId thirdRuleId
      source firstMiddle secondMiddle target).target? =
      some target := by
  rw [FXStep.seqThreeMkCheckedLeftAssociated,
    FXStep.target?, PolyTerm.target?_compVThreeCellsCheckedLeftAssociated]

theorem FXStep.source?_seqThreeMkCheckedRightAssociated
    (firstRuleId secondRuleId thirdRuleId : CellId)
    (source firstMiddle secondMiddle target : FXCellAt 0) :
    (FXStep.seqThreeMkCheckedRightAssociated
      firstRuleId secondRuleId thirdRuleId
      source firstMiddle secondMiddle target).source? =
      some source := by
  rw [FXStep.seqThreeMkCheckedRightAssociated,
    FXStep.source?, PolyTerm.source?_compVThreeCellsCheckedRightAssociated]

theorem FXStep.target?_seqThreeMkCheckedRightAssociated
    (firstRuleId secondRuleId thirdRuleId : CellId)
    (source firstMiddle secondMiddle target : FXCellAt 0) :
    (FXStep.seqThreeMkCheckedRightAssociated
      firstRuleId secondRuleId thirdRuleId
      source firstMiddle secondMiddle target).target? =
      some target := by
  rw [FXStep.seqThreeMkCheckedRightAssociated,
    FXStep.target?, PolyTerm.target?_compVThreeCellsCheckedRightAssociated]

/-- Endpoint evidence for the constructor-level checked left-associated chain. -/
def FXStep.endpointEvidence_seqThreeMkCheckedLeftAssociated
    (firstRuleId secondRuleId thirdRuleId : CellId)
    (source firstMiddle secondMiddle target : FXCellAt 0) :
    FXStep.EndpointEvidence
      (FXStep.seqThreeMkCheckedLeftAssociated
        firstRuleId secondRuleId thirdRuleId
        source firstMiddle secondMiddle target) where
  sourceCell := source
  targetCell := target
  source_eq :=
    FXStep.source?_seqThreeMkCheckedLeftAssociated
      firstRuleId secondRuleId thirdRuleId
      source firstMiddle secondMiddle target
  target_eq :=
    FXStep.target?_seqThreeMkCheckedLeftAssociated
      firstRuleId secondRuleId thirdRuleId
      source firstMiddle secondMiddle target

/-- Endpoint evidence for the constructor-level checked right-associated chain. -/
def FXStep.endpointEvidence_seqThreeMkCheckedRightAssociated
    (firstRuleId secondRuleId thirdRuleId : CellId)
    (source firstMiddle secondMiddle target : FXCellAt 0) :
    FXStep.EndpointEvidence
      (FXStep.seqThreeMkCheckedRightAssociated
        firstRuleId secondRuleId thirdRuleId
        source firstMiddle secondMiddle target) where
  sourceCell := source
  targetCell := target
  source_eq :=
    FXStep.source?_seqThreeMkCheckedRightAssociated
      firstRuleId secondRuleId thirdRuleId
      source firstMiddle secondMiddle target
  target_eq :=
    FXStep.target?_seqThreeMkCheckedRightAssociated
      firstRuleId secondRuleId thirdRuleId
      source firstMiddle secondMiddle target

theorem FXStep.source?_par (step1 step2 : FXStep) :
    PolyTerm.source? (profile := fxProfile) (dimension := 0) (FXStep.par step1 step2) =
      none :=
  PolyTerm.source?_compH step1.val step2.val

theorem FXStep.target?_par (step1 step2 : FXStep) :
    PolyTerm.target? (profile := fxProfile) (dimension := 0) (FXStep.par step1 step2) =
      none :=
  PolyTerm.target?_compH step1.val step2.val

/-- Known source endpoint of a provisional dim-2 FX coherence cell. -/
def FXCdLemma.source? (coherenceCell : FXCdLemma) : Option (FXCellAt 1) :=
  PolyTerm.source? (profile := fxProfile) (dimension := 1) coherenceCell

/-- Known target endpoint of a provisional dim-2 FX coherence cell. -/
def FXCdLemma.target? (coherenceCell : FXCdLemma) : Option (FXCellAt 1) :=
  PolyTerm.target? (profile := fxProfile) (dimension := 1) coherenceCell

/-- Proof-relevant endpoint data for a provisional dim-2 FX coherence cell.
This records actual source and target dim-1 cells; it does not assert
confluence, associativity, or any equality between those endpoints. -/
structure FXCdLemma.EndpointEvidence (coherenceCell : FXCdLemma) where
  /-- The source dim-1 cell exposed by the structural boundary projection. -/
  sourceCell : FXCellAt 1
  /-- The target dim-1 cell exposed by the structural boundary projection. -/
  targetCell : FXCellAt 1
  /-- The source projection computes to `sourceCell`. -/
  source_eq : coherenceCell.source? = some sourceCell
  /-- The target projection computes to `targetCell`. -/
  target_eq : coherenceCell.target? = some targetCell

/-- Forget FX naming and view dim-2 endpoint evidence as generic Core evidence. -/
def FXCdLemma.EndpointEvidence.toCore {coherenceCell : FXCdLemma}
    (endpointEvidence : FXCdLemma.EndpointEvidence coherenceCell) :
    PolyTerm.EndpointEvidence coherenceCell where
  sourceCell := endpointEvidence.sourceCell
  targetCell := endpointEvidence.targetCell
  source_eq := endpointEvidence.source_eq
  target_eq := endpointEvidence.target_eq

/-- Specialize generic Core endpoint evidence to the dim-2 FX coherence view. -/
def FXCdLemma.EndpointEvidence.ofCore {coherenceCell : FXCdLemma}
    (endpointEvidence : PolyTerm.EndpointEvidence coherenceCell) :
    FXCdLemma.EndpointEvidence coherenceCell where
  sourceCell := endpointEvidence.sourceCell
  targetCell := endpointEvidence.targetCell
  source_eq := endpointEvidence.source_eq
  target_eq := endpointEvidence.target_eq

/-- Endpoint evidence for a raw dim-2 generator cell. -/
def FXCdLemma.EndpointEvidence.cell (ruleId : CellId)
    (source target : FXCellAt 1) :
    FXCdLemma.EndpointEvidence (.cell ruleId source target) :=
  FXCdLemma.EndpointEvidence.ofCore
    (PolyTerm.EndpointEvidence.cell ruleId source target)

/-- Checked associator coherence cell for three composable dim-1 FX cells.
This packages the dim-2 scaffold; it is not an associativity equation. -/
def FXCdLemma.associatorVChecked
    (first second third : FXCellAt 1)
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first second)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second third) :
    FXCdLemma :=
  PolyTerm.associatorVChecked
    first second third firstSecondEvidence secondThirdEvidence

theorem FXCdLemma.source?_associatorVChecked
    (first second third : FXCellAt 1)
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first second)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second third) :
    (FXCdLemma.associatorVChecked
      first second third firstSecondEvidence secondThirdEvidence).source? =
      some (PolyTerm.compVCheckedLeftAssociated
        first second third firstSecondEvidence secondThirdEvidence) := by
  rw [FXCdLemma.associatorVChecked, FXCdLemma.source?,
    PolyTerm.source?_associatorVChecked]

theorem FXCdLemma.target?_associatorVChecked
    (first second third : FXCellAt 1)
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first second)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second third) :
    (FXCdLemma.associatorVChecked
      first second third firstSecondEvidence secondThirdEvidence).target? =
      some (PolyTerm.compVCheckedRightAssociated
        first second third firstSecondEvidence secondThirdEvidence) := by
  rw [FXCdLemma.associatorVChecked, FXCdLemma.target?,
    PolyTerm.target?_associatorVChecked]

/-- Endpoint evidence for the generic checked associator scaffold. -/
def FXCdLemma.endpointEvidence_associatorVChecked
    (first second third : FXCellAt 1)
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first second)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second third) :
    FXCdLemma.EndpointEvidence
      (FXCdLemma.associatorVChecked
        first second third firstSecondEvidence secondThirdEvidence) :=
  FXCdLemma.EndpointEvidence.ofCore
    (PolyTerm.EndpointEvidence.associatorVChecked
      first second third firstSecondEvidence secondThirdEvidence)

/-- Checked associator coherence cell specialized to three FX steps.  This is
still only a dim-2 scaffold cell; it does not assert associativity. -/
def FXCdLemma.associatorVCheckedOfSteps
    (first second third : FXStep)
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first.val second.val)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second.val third.val) :
    FXCdLemma :=
  .cell verticalAssociatorRuleId
    (FXStep.seqCheckedLeftAssociated
      first second third firstSecondEvidence secondThirdEvidence).toCell
    (FXStep.seqCheckedRightAssociated
      first second third firstSecondEvidence secondThirdEvidence).toCell

theorem FXCdLemma.source?_associatorVCheckedOfSteps
    (first second third : FXStep)
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first.val second.val)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second.val third.val) :
    (FXCdLemma.associatorVCheckedOfSteps
      first second third firstSecondEvidence secondThirdEvidence).source? =
      some (FXStep.seqCheckedLeftAssociated
        first second third firstSecondEvidence secondThirdEvidence).toCell := by
  rw [FXCdLemma.associatorVCheckedOfSteps, FXCdLemma.source?,
    PolyTerm.source?_cell]

theorem FXCdLemma.target?_associatorVCheckedOfSteps
    (first second third : FXStep)
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first.val second.val)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second.val third.val) :
    (FXCdLemma.associatorVCheckedOfSteps
      first second third firstSecondEvidence secondThirdEvidence).target? =
      some (FXStep.seqCheckedRightAssociated
        first second third firstSecondEvidence secondThirdEvidence).toCell := by
  rw [FXCdLemma.associatorVCheckedOfSteps, FXCdLemma.target?,
    PolyTerm.target?_cell]

/-- Endpoint evidence for the FX-step checked associator scaffold. -/
def FXCdLemma.endpointEvidence_associatorVCheckedOfSteps
    (first second third : FXStep)
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first.val second.val)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second.val third.val) :
    FXCdLemma.EndpointEvidence
      (FXCdLemma.associatorVCheckedOfSteps
        first second third firstSecondEvidence secondThirdEvidence) :=
  FXCdLemma.EndpointEvidence.cell verticalAssociatorRuleId
    (FXStep.seqCheckedLeftAssociated
      first second third firstSecondEvidence secondThirdEvidence).toCell
    (FXStep.seqCheckedRightAssociated
      first second third firstSecondEvidence secondThirdEvidence).toCell

/-- Checked associator coherence cell specialized to three freshly constructed
FX steps sharing two explicit middle endpoints. -/
def FXCdLemma.associatorVCheckedOfStepMks
    (firstRuleId secondRuleId thirdRuleId : CellId)
    (source firstMiddle secondMiddle target : FXCellAt 0) :
    FXCdLemma :=
  .cell verticalAssociatorRuleId
    (FXStep.seqThreeMkCheckedLeftAssociated
      firstRuleId secondRuleId thirdRuleId
      source firstMiddle secondMiddle target).toCell
    (FXStep.seqThreeMkCheckedRightAssociated
      firstRuleId secondRuleId thirdRuleId
      source firstMiddle secondMiddle target).toCell

theorem FXCdLemma.source?_associatorVCheckedOfStepMks
    (firstRuleId secondRuleId thirdRuleId : CellId)
    (source firstMiddle secondMiddle target : FXCellAt 0) :
    (FXCdLemma.associatorVCheckedOfStepMks
      firstRuleId secondRuleId thirdRuleId
      source firstMiddle secondMiddle target).source? =
      some (FXStep.seqThreeMkCheckedLeftAssociated
        firstRuleId secondRuleId thirdRuleId
        source firstMiddle secondMiddle target).toCell := by
  rw [FXCdLemma.associatorVCheckedOfStepMks, FXCdLemma.source?,
    PolyTerm.source?_cell]

theorem FXCdLemma.target?_associatorVCheckedOfStepMks
    (firstRuleId secondRuleId thirdRuleId : CellId)
    (source firstMiddle secondMiddle target : FXCellAt 0) :
    (FXCdLemma.associatorVCheckedOfStepMks
      firstRuleId secondRuleId thirdRuleId
      source firstMiddle secondMiddle target).target? =
      some (FXStep.seqThreeMkCheckedRightAssociated
        firstRuleId secondRuleId thirdRuleId
        source firstMiddle secondMiddle target).toCell := by
  rw [FXCdLemma.associatorVCheckedOfStepMks, FXCdLemma.target?,
    PolyTerm.target?_cell]

/-- Endpoint evidence for the constructor-level FX-step associator scaffold. -/
def FXCdLemma.endpointEvidence_associatorVCheckedOfStepMks
    (firstRuleId secondRuleId thirdRuleId : CellId)
    (source firstMiddle secondMiddle target : FXCellAt 0) :
    FXCdLemma.EndpointEvidence
      (FXCdLemma.associatorVCheckedOfStepMks
        firstRuleId secondRuleId thirdRuleId
        source firstMiddle secondMiddle target) :=
  FXCdLemma.EndpointEvidence.cell verticalAssociatorRuleId
    (FXStep.seqThreeMkCheckedLeftAssociated
      firstRuleId secondRuleId thirdRuleId
      source firstMiddle secondMiddle target).toCell
    (FXStep.seqThreeMkCheckedRightAssociated
      firstRuleId secondRuleId thirdRuleId
      source firstMiddle secondMiddle target).toCell

/-- Checked left-unitor coherence cell for a dim-1 FX cell with a known source.
This records the dim-2 scaffold only, not a unit law. -/
def FXCdLemma.leftUnitorVChecked
    (sourceCell : FXCellAt 0)
    (cell : FXCellAt 1)
    (cellSource_eq : cell.source? = some sourceCell) :
    FXCdLemma :=
  PolyTerm.leftUnitorVChecked sourceCell cell cellSource_eq

theorem FXCdLemma.source?_leftUnitorVChecked
    (sourceCell : FXCellAt 0)
    (cell : FXCellAt 1)
    (cellSource_eq : cell.source? = some sourceCell) :
    (FXCdLemma.leftUnitorVChecked sourceCell cell cellSource_eq).source? =
      some (PolyTerm.compVChecked (.identity sourceCell) cell
        (PolyTerm.VerticalBoundaryEvidence.identityLeft
          sourceCell cell cellSource_eq)) := by
  rw [FXCdLemma.leftUnitorVChecked, FXCdLemma.source?,
    PolyTerm.source?_leftUnitorVChecked]

theorem FXCdLemma.target?_leftUnitorVChecked
    (sourceCell : FXCellAt 0)
    (cell : FXCellAt 1)
    (cellSource_eq : cell.source? = some sourceCell) :
    (FXCdLemma.leftUnitorVChecked sourceCell cell cellSource_eq).target? =
      some cell := by
  rw [FXCdLemma.leftUnitorVChecked, FXCdLemma.target?,
    PolyTerm.target?_leftUnitorVChecked]

/-- Endpoint evidence for the generic checked left-unitor scaffold. -/
def FXCdLemma.endpointEvidence_leftUnitorVChecked
    (sourceCell : FXCellAt 0)
    (cell : FXCellAt 1)
    (cellSource_eq : cell.source? = some sourceCell) :
    FXCdLemma.EndpointEvidence
      (FXCdLemma.leftUnitorVChecked sourceCell cell cellSource_eq) :=
  FXCdLemma.EndpointEvidence.ofCore
    (PolyTerm.EndpointEvidence.leftUnitorVChecked
      sourceCell cell cellSource_eq)

/-- Checked left-unitor coherence cell specialized to an FX step.  The identity
cell is not itself an `FXStep`; only the non-identity endpoint is packaged as a
step view. -/
def FXCdLemma.leftUnitorVCheckedOfStep
    (sourceCell : FXCellAt 0)
    (step : FXStep)
    (stepSource_eq : step.source? = some sourceCell) :
    FXCdLemma :=
  FXCdLemma.leftUnitorVChecked sourceCell step.toCell stepSource_eq

theorem FXCdLemma.source?_leftUnitorVCheckedOfStep
    (sourceCell : FXCellAt 0)
    (step : FXStep)
    (stepSource_eq : step.source? = some sourceCell) :
    (FXCdLemma.leftUnitorVCheckedOfStep
      sourceCell step stepSource_eq).source? =
      some (PolyTerm.compVChecked (.identity sourceCell) step.toCell
        (PolyTerm.VerticalBoundaryEvidence.identityLeft
          sourceCell step.toCell stepSource_eq)) := by
  rw [FXCdLemma.leftUnitorVCheckedOfStep,
    FXCdLemma.source?_leftUnitorVChecked]

theorem FXCdLemma.target?_leftUnitorVCheckedOfStep
    (sourceCell : FXCellAt 0)
    (step : FXStep)
    (stepSource_eq : step.source? = some sourceCell) :
    (FXCdLemma.leftUnitorVCheckedOfStep
      sourceCell step stepSource_eq).target? =
      some step.toCell := by
  rw [FXCdLemma.leftUnitorVCheckedOfStep,
    FXCdLemma.target?_leftUnitorVChecked]

/-- Endpoint evidence for the FX-step checked left-unitor scaffold. -/
def FXCdLemma.endpointEvidence_leftUnitorVCheckedOfStep
    (sourceCell : FXCellAt 0)
    (step : FXStep)
    (stepSource_eq : step.source? = some sourceCell) :
    FXCdLemma.EndpointEvidence
      (FXCdLemma.leftUnitorVCheckedOfStep sourceCell step stepSource_eq) :=
  FXCdLemma.endpointEvidence_leftUnitorVChecked
    sourceCell step.toCell stepSource_eq

/-- Checked right-unitor coherence cell for a dim-1 FX cell with a known target.
This records the dim-2 scaffold only, not a unit law. -/
def FXCdLemma.rightUnitorVChecked
    (targetCell : FXCellAt 0)
    (cell : FXCellAt 1)
    (cellTarget_eq : cell.target? = some targetCell) :
    FXCdLemma :=
  PolyTerm.rightUnitorVChecked targetCell cell cellTarget_eq

theorem FXCdLemma.source?_rightUnitorVChecked
    (targetCell : FXCellAt 0)
    (cell : FXCellAt 1)
    (cellTarget_eq : cell.target? = some targetCell) :
    (FXCdLemma.rightUnitorVChecked targetCell cell cellTarget_eq).source? =
      some (PolyTerm.compVChecked cell (.identity targetCell)
        (PolyTerm.VerticalBoundaryEvidence.identityRight
          cell targetCell cellTarget_eq)) := by
  rw [FXCdLemma.rightUnitorVChecked, FXCdLemma.source?,
    PolyTerm.source?_rightUnitorVChecked]

theorem FXCdLemma.target?_rightUnitorVChecked
    (targetCell : FXCellAt 0)
    (cell : FXCellAt 1)
    (cellTarget_eq : cell.target? = some targetCell) :
    (FXCdLemma.rightUnitorVChecked targetCell cell cellTarget_eq).target? =
      some cell := by
  rw [FXCdLemma.rightUnitorVChecked, FXCdLemma.target?,
    PolyTerm.target?_rightUnitorVChecked]

/-- Endpoint evidence for the generic checked right-unitor scaffold. -/
def FXCdLemma.endpointEvidence_rightUnitorVChecked
    (targetCell : FXCellAt 0)
    (cell : FXCellAt 1)
    (cellTarget_eq : cell.target? = some targetCell) :
    FXCdLemma.EndpointEvidence
      (FXCdLemma.rightUnitorVChecked targetCell cell cellTarget_eq) :=
  FXCdLemma.EndpointEvidence.ofCore
    (PolyTerm.EndpointEvidence.rightUnitorVChecked
      targetCell cell cellTarget_eq)

/-- Checked right-unitor coherence cell specialized to an FX step.  The identity
cell remains raw because the current `FXStep` view excludes identities. -/
def FXCdLemma.rightUnitorVCheckedOfStep
    (targetCell : FXCellAt 0)
    (step : FXStep)
    (stepTarget_eq : step.target? = some targetCell) :
    FXCdLemma :=
  FXCdLemma.rightUnitorVChecked targetCell step.toCell stepTarget_eq

theorem FXCdLemma.source?_rightUnitorVCheckedOfStep
    (targetCell : FXCellAt 0)
    (step : FXStep)
    (stepTarget_eq : step.target? = some targetCell) :
    (FXCdLemma.rightUnitorVCheckedOfStep
      targetCell step stepTarget_eq).source? =
      some (PolyTerm.compVChecked step.toCell (.identity targetCell)
        (PolyTerm.VerticalBoundaryEvidence.identityRight
          step.toCell targetCell stepTarget_eq)) := by
  rw [FXCdLemma.rightUnitorVCheckedOfStep,
    FXCdLemma.source?_rightUnitorVChecked]

theorem FXCdLemma.target?_rightUnitorVCheckedOfStep
    (targetCell : FXCellAt 0)
    (step : FXStep)
    (stepTarget_eq : step.target? = some targetCell) :
    (FXCdLemma.rightUnitorVCheckedOfStep
      targetCell step stepTarget_eq).target? =
      some step.toCell := by
  rw [FXCdLemma.rightUnitorVCheckedOfStep,
    FXCdLemma.target?_rightUnitorVChecked]

/-- Endpoint evidence for the FX-step checked right-unitor scaffold. -/
def FXCdLemma.endpointEvidence_rightUnitorVCheckedOfStep
    (targetCell : FXCellAt 0)
    (step : FXStep)
    (stepTarget_eq : step.target? = some targetCell) :
    FXCdLemma.EndpointEvidence
      (FXCdLemma.rightUnitorVCheckedOfStep targetCell step stepTarget_eq) :=
  FXCdLemma.endpointEvidence_rightUnitorVChecked
    targetCell step.toCell stepTarget_eq

/-- Identity dim-1 cell on a term. -/
def FXConv.refl (term : FXCellAt 0) : FXConv :=
  .identity term

/-- Raw vertical composition of provisional conversion cells. -/
def FXConv.trans (firstConversion secondConversion : FXConv) : FXConv :=
  .compV firstConversion secondConversion

/-- Checked vertical composition of provisional conversion cells.  The caller
supplies concrete evidence that the target of the first conversion matches
the source of the second conversion. -/
def FXConv.transChecked (firstConversion secondConversion : FXConv)
    (boundaryEvidence :
      PolyTerm.VerticalBoundaryEvidence firstConversion secondConversion) :
    FXConv :=
  PolyTerm.compVChecked firstConversion secondConversion boundaryEvidence

/-- Checked conversion composition with a reflexive conversion on the left. -/
def FXConv.transReflLeftChecked (base : FXCellAt 0)
    (conversion : FXConv)
    (conversionSource_eq : conversion.source? = some base) : FXConv :=
  FXConv.transChecked (FXConv.refl base) conversion
    (PolyTerm.VerticalBoundaryEvidence.identityLeft
      base conversion conversionSource_eq)

/-- Checked conversion composition with a reflexive conversion on the right. -/
def FXConv.transReflRightChecked (conversion : FXConv)
    (base : FXCellAt 0)
    (conversionTarget_eq : conversion.target? = some base) : FXConv :=
  FXConv.transChecked conversion (FXConv.refl base)
    (PolyTerm.VerticalBoundaryEvidence.identityRight
      conversion base conversionTarget_eq)

/-- Boundary evidence for composing `(first ; second)` with `third`, transported
from the two adjacent checked conversion boundaries.  This is a chain helper,
not a thinness or conversion-completeness theorem. -/
def FXConv.boundaryEvidence_transCheckedLeft
    (first second third : FXConv)
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first second)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second third) :
    PolyTerm.VerticalBoundaryEvidence
      (FXConv.transChecked first second firstSecondEvidence)
      third :=
  PolyTerm.VerticalBoundaryEvidence.compVLeft
    first second third firstSecondEvidence secondThirdEvidence

/-- Boundary evidence for composing `first` with `(second ; third)`, transported
from the two adjacent checked conversion boundaries. -/
def FXConv.boundaryEvidence_transCheckedRight
    (first second third : FXConv)
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first second)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second third) :
    PolyTerm.VerticalBoundaryEvidence
      first
      (FXConv.transChecked second third secondThirdEvidence) :=
  PolyTerm.VerticalBoundaryEvidence.compVRight
    first second third firstSecondEvidence secondThirdEvidence

/-- Checked left-associated composition of three provisional conversion cells. -/
def FXConv.transCheckedLeftAssociated
    (first second third : FXConv)
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first second)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second third) :
    FXConv :=
  PolyTerm.compVCheckedLeftAssociated
    first second third firstSecondEvidence secondThirdEvidence

/-- Checked right-associated composition of three provisional conversion cells. -/
def FXConv.transCheckedRightAssociated
    (first second third : FXConv)
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first second)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second third) :
    FXConv :=
  PolyTerm.compVCheckedRightAssociated
    first second third firstSecondEvidence secondThirdEvidence

/-- Known source endpoint of a provisional conversion cell, when available. -/
def FXConv.source? (conversion : FXConv) : Option (FXCellAt 0) :=
  PolyTerm.source? (profile := fxProfile) (dimension := 0) conversion

/-- Known target endpoint of a provisional conversion cell, when available. -/
def FXConv.target? (conversion : FXConv) : Option (FXCellAt 0) :=
  PolyTerm.target? (profile := fxProfile) (dimension := 0) conversion

/-- Proof-relevant endpoint data for a provisional conversion cell.
This records source and target projections only; it does not assert thinness. -/
structure FXConv.EndpointEvidence (conversion : FXConv) where
  /-- The source dim-0 cell exposed by the structural boundary projection. -/
  sourceCell : FXCellAt 0
  /-- The target dim-0 cell exposed by the structural boundary projection. -/
  targetCell : FXCellAt 0
  /-- The source projection computes to `sourceCell`. -/
  source_eq : conversion.source? = some sourceCell
  /-- The target projection computes to `targetCell`. -/
  target_eq : conversion.target? = some targetCell

/-- Forget FX conversion naming and view endpoint evidence as generic Core
evidence. -/
def FXConv.EndpointEvidence.toCore {conversion : FXConv}
    (endpointEvidence : FXConv.EndpointEvidence conversion) :
    PolyTerm.EndpointEvidence (profile := fxProfile) (dimension := 0)
      conversion where
  sourceCell := endpointEvidence.sourceCell
  targetCell := endpointEvidence.targetCell
  source_eq := endpointEvidence.source_eq
  target_eq := endpointEvidence.target_eq

/-- Specialize generic Core endpoint evidence to provisional FX conversions. -/
def FXConv.EndpointEvidence.ofCore {conversion : FXConv}
    (endpointEvidence :
      PolyTerm.EndpointEvidence (profile := fxProfile) (dimension := 0)
        conversion) :
    FXConv.EndpointEvidence conversion where
  sourceCell := endpointEvidence.sourceCell
  targetCell := endpointEvidence.targetCell
  source_eq := endpointEvidence.source_eq
  target_eq := endpointEvidence.target_eq

/-- Endpoint evidence for a reflexive provisional conversion. -/
def FXConv.endpointEvidence_refl (term : FXCellAt 0) :
    FXConv.EndpointEvidence (FXConv.refl term) :=
  FXConv.EndpointEvidence.ofCore
    (PolyTerm.EndpointEvidence.identity term)

/-- Endpoint evidence for raw conversion composition.
This records only the outer endpoints; it does not assert boundary matching or
thinness preservation. -/
def FXConv.endpointEvidence_trans
    (firstConversion secondConversion : FXConv)
    (firstEndpointEvidence : FXConv.EndpointEvidence firstConversion)
    (secondEndpointEvidence : FXConv.EndpointEvidence secondConversion) :
    FXConv.EndpointEvidence
      (FXConv.trans firstConversion secondConversion) :=
  FXConv.EndpointEvidence.ofCore
    (PolyTerm.EndpointEvidence.compV
      firstEndpointEvidence.toCore
      secondEndpointEvidence.toCore)

/-- Endpoint evidence for checked conversion composition.  The boundary
evidence validates the middle endpoint; thinness is still not asserted. -/
def FXConv.endpointEvidence_transChecked
    (firstConversion secondConversion : FXConv)
    (boundaryEvidence :
      PolyTerm.VerticalBoundaryEvidence firstConversion secondConversion)
    (firstEndpointEvidence : FXConv.EndpointEvidence firstConversion)
    (secondEndpointEvidence : FXConv.EndpointEvidence secondConversion) :
    FXConv.EndpointEvidence
      (FXConv.transChecked
        firstConversion secondConversion boundaryEvidence) :=
  FXConv.EndpointEvidence.ofCore
    (PolyTerm.EndpointEvidence.compVChecked
      boundaryEvidence
      firstEndpointEvidence.toCore
      secondEndpointEvidence.toCore)

/-- Endpoint evidence for checked composition with a reflexive conversion on the
left. -/
def FXConv.endpointEvidence_transReflLeftChecked (base : FXCellAt 0)
    (conversion : FXConv)
    (conversionSource_eq : conversion.source? = some base)
    (conversionEndpointEvidence : FXConv.EndpointEvidence conversion) :
    FXConv.EndpointEvidence
      (FXConv.transReflLeftChecked base conversion conversionSource_eq) :=
  FXConv.endpointEvidence_transChecked
    (FXConv.refl base)
    conversion
    (PolyTerm.VerticalBoundaryEvidence.identityLeft
      base conversion conversionSource_eq)
    (FXConv.endpointEvidence_refl base)
    conversionEndpointEvidence

/-- Endpoint evidence for checked composition with a reflexive conversion on the
right. -/
def FXConv.endpointEvidence_transReflRightChecked (conversion : FXConv)
    (base : FXCellAt 0)
    (conversionTarget_eq : conversion.target? = some base)
    (conversionEndpointEvidence : FXConv.EndpointEvidence conversion) :
    FXConv.EndpointEvidence
      (FXConv.transReflRightChecked conversion base conversionTarget_eq) :=
  FXConv.endpointEvidence_transChecked
    conversion
    (FXConv.refl base)
    (PolyTerm.VerticalBoundaryEvidence.identityRight
      conversion base conversionTarget_eq)
    conversionEndpointEvidence
    (FXConv.endpointEvidence_refl base)

/-- Any checked pair of provisional conversion cells has matching
target/source endpoints.  This does not assert thinness. -/
theorem FXConv.target?_eq_source?_of_boundaryEvidence
    (firstConversion secondConversion : FXConv)
    (boundaryEvidence :
      PolyTerm.VerticalBoundaryEvidence firstConversion secondConversion) :
    firstConversion.target? = secondConversion.source? := by
  rw [FXConv.target?, FXConv.source?]
  exact PolyTerm.VerticalBoundaryEvidence.firstTarget?_eq_secondSource?
    boundaryEvidence

theorem FXConv.source?_refl (term : FXCellAt 0) :
    (FXConv.refl term).source? = some term := by
  rw [FXConv.source?, FXConv.refl, PolyTerm.source?_identity]

theorem FXConv.target?_refl (term : FXCellAt 0) :
    (FXConv.refl term).target? = some term := by
  rw [FXConv.target?, FXConv.refl, PolyTerm.target?_identity]

theorem FXConv.source?_trans
    (firstConversion secondConversion : FXConv) :
    (FXConv.trans firstConversion secondConversion).source? =
      firstConversion.source? :=
  PolyTerm.source?_compV firstConversion secondConversion

theorem FXConv.target?_trans
    (firstConversion secondConversion : FXConv) :
    (FXConv.trans firstConversion secondConversion).target? =
      secondConversion.target? :=
  PolyTerm.target?_compV firstConversion secondConversion

theorem FXConv.source?_transChecked
    (firstConversion secondConversion : FXConv)
    (boundaryEvidence :
      PolyTerm.VerticalBoundaryEvidence firstConversion secondConversion) :
    (FXConv.transChecked firstConversion secondConversion boundaryEvidence).source? =
      firstConversion.source? :=
  PolyTerm.source?_compVChecked firstConversion secondConversion boundaryEvidence

theorem FXConv.target?_transChecked
    (firstConversion secondConversion : FXConv)
    (boundaryEvidence :
      PolyTerm.VerticalBoundaryEvidence firstConversion secondConversion) :
    (FXConv.transChecked firstConversion secondConversion boundaryEvidence).target? =
      secondConversion.target? :=
  PolyTerm.target?_compVChecked firstConversion secondConversion boundaryEvidence

theorem FXConv.source?_transCheckedLeftAssociated
    (first second third : FXConv)
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first second)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second third) :
    (FXConv.transCheckedLeftAssociated
      first second third firstSecondEvidence secondThirdEvidence).source? =
      first.source? := by
  rw [FXConv.transCheckedLeftAssociated, FXConv.source?,
    PolyTerm.source?_compVCheckedLeftAssociated, FXConv.source?]

theorem FXConv.target?_transCheckedLeftAssociated
    (first second third : FXConv)
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first second)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second third) :
    (FXConv.transCheckedLeftAssociated
      first second third firstSecondEvidence secondThirdEvidence).target? =
      third.target? := by
  rw [FXConv.transCheckedLeftAssociated, FXConv.target?,
    PolyTerm.target?_compVCheckedLeftAssociated, FXConv.target?]

theorem FXConv.source?_transCheckedRightAssociated
    (first second third : FXConv)
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first second)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second third) :
    (FXConv.transCheckedRightAssociated
      first second third firstSecondEvidence secondThirdEvidence).source? =
      first.source? := by
  rw [FXConv.transCheckedRightAssociated, FXConv.source?,
    PolyTerm.source?_compVCheckedRightAssociated, FXConv.source?]

theorem FXConv.target?_transCheckedRightAssociated
    (first second third : FXConv)
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first second)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second third) :
    (FXConv.transCheckedRightAssociated
      first second third firstSecondEvidence secondThirdEvidence).target? =
      third.target? := by
  rw [FXConv.transCheckedRightAssociated, FXConv.target?,
    PolyTerm.target?_compVCheckedRightAssociated, FXConv.target?]

theorem FXConv.source?_transReflLeftChecked (base : FXCellAt 0)
    (conversion : FXConv)
    (conversionSource_eq : conversion.source? = some base) :
    (FXConv.transReflLeftChecked base conversion conversionSource_eq).source? =
      some base := by
  rw [FXConv.transReflLeftChecked, FXConv.source?_transChecked,
    FXConv.source?_refl]

theorem FXConv.target?_transReflLeftChecked (base : FXCellAt 0)
    (conversion : FXConv)
    (conversionSource_eq : conversion.source? = some base) :
    (FXConv.transReflLeftChecked base conversion conversionSource_eq).target? =
      conversion.target? := by
  rw [FXConv.transReflLeftChecked, FXConv.target?_transChecked]

theorem FXConv.source?_transReflRightChecked (conversion : FXConv)
    (base : FXCellAt 0)
    (conversionTarget_eq : conversion.target? = some base) :
    (FXConv.transReflRightChecked conversion base conversionTarget_eq).source? =
      conversion.source? := by
  rw [FXConv.transReflRightChecked, FXConv.source?_transChecked]

theorem FXConv.target?_transReflRightChecked (conversion : FXConv)
    (base : FXCellAt 0)
    (conversionTarget_eq : conversion.target? = some base) :
    (FXConv.transReflRightChecked conversion base conversionTarget_eq).target? =
      some base := by
  rw [FXConv.transReflRightChecked, FXConv.target?_transChecked,
    FXConv.target?_refl]

/-- Endpoint evidence for checked left-associated composition of three
provisional conversion cells.  This records the outer endpoints only. -/
def FXConv.endpointEvidence_transCheckedLeftAssociated
    (first second third : FXConv)
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first second)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second third)
    (firstEndpointEvidence : FXConv.EndpointEvidence first)
    (thirdEndpointEvidence : FXConv.EndpointEvidence third) :
    FXConv.EndpointEvidence
      (FXConv.transCheckedLeftAssociated
        first second third firstSecondEvidence secondThirdEvidence) where
  sourceCell := firstEndpointEvidence.sourceCell
  targetCell := thirdEndpointEvidence.targetCell
  source_eq := by
    rw [FXConv.source?_transCheckedLeftAssociated]
    exact firstEndpointEvidence.source_eq
  target_eq := by
    rw [FXConv.target?_transCheckedLeftAssociated]
    exact thirdEndpointEvidence.target_eq

/-- Endpoint evidence for checked right-associated composition of three
provisional conversion cells.  This records the outer endpoints only. -/
def FXConv.endpointEvidence_transCheckedRightAssociated
    (first second third : FXConv)
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first second)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second third)
    (firstEndpointEvidence : FXConv.EndpointEvidence first)
    (thirdEndpointEvidence : FXConv.EndpointEvidence third) :
    FXConv.EndpointEvidence
      (FXConv.transCheckedRightAssociated
        first second third firstSecondEvidence secondThirdEvidence) where
  sourceCell := firstEndpointEvidence.sourceCell
  targetCell := thirdEndpointEvidence.targetCell
  source_eq := by
    rw [FXConv.source?_transCheckedRightAssociated]
    exact firstEndpointEvidence.source_eq
  target_eq := by
    rw [FXConv.target?_transCheckedRightAssociated]
    exact thirdEndpointEvidence.target_eq

/-- Apply fold to an FX cell using a specific algebra. -/
def FXCell.applyFold {target : CellDim → Type}
    (algebra : PolyTermAlgebra fxProfile target)
    {dimension : CellDim}
    (cell : FXCellAt dimension) : target dimension :=
  PolyTerm.fold algebra cell

/-- Number of dim-0 ids currently reserved for typed terms. -/
def termGeneratorCount : Nat := PolyTerm.termCellIdLimit

/-- Number of dim-0 ids currently reserved for types. -/
def typeGeneratorCount : Nat := PolyTerm.typeCellIdCount

/-- Total number of current dim-0 term-or-type ids. -/
def totalGeneratorCount : Nat := PolyTerm.typeCellIdLimit

theorem generatorPartition :
    termGeneratorCount + typeGeneratorCount = totalGeneratorCount := rfl

theorem termGeneratorCount_eq_currentTermConstructorCount :
    termGeneratorCount = 78 := rfl

theorem typeGeneratorCount_eq_currentTypeConstructorCount :
    typeGeneratorCount = 25 := rfl

theorem totalGeneratorCount_eq_currentTermAndTypeConstructors :
    totalGeneratorCount = 103 := rfl

theorem firstTypeCellId_eq_termGeneratorCount :
    PolyTerm.firstTypeCellId = termGeneratorCount := rfl

theorem typeCellIdLimit_eq_totalGeneratorCount :
    PolyTerm.typeCellIdLimit = totalGeneratorCount := rfl

end LeanFX2.Foundation.PolyCell.FXProfile
