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

theorem FXTerm.toCell_isTermCell (term : FXTerm) :
    term.toCell.isTermCell = true := by
  exact term.property

theorem FXType.toCell_isTypeCell (typeCell : FXType) :
    typeCell.toCell.isTypeCell = true := by
  exact typeCell.property

theorem FXTerm.toCell_isTypeCell_false (term : FXTerm) :
    term.toCell.isTypeCell = false := by
  cases term with
  | mk cell hRange =>
      cases cell with
      | atom cellId payload =>
          change
            (decide (PolyTerm.firstTypeCellId ≤ cellId) &&
              decide (cellId < PolyTerm.typeCellIdLimit)) = false
          have hasTermRange : cellId < PolyTerm.firstTypeCellId := by
            change cellId < PolyTerm.termCellIdLimit
            exact of_decide_eq_true hRange
          cases hasLowerBool :
              decide (PolyTerm.firstTypeCellId ≤ cellId) with
          | false =>
              rfl
          | true =>
              have hasLowerBound : PolyTerm.firstTypeCellId ≤ cellId :=
                of_decide_eq_true hasLowerBool
              exact False.elim
                (Nat.not_lt_of_ge hasLowerBound hasTermRange)

theorem FXType.toCell_isTermCell_false (typeCell : FXType) :
    typeCell.toCell.isTermCell = false := by
  cases typeCell with
  | mk cell hRange =>
      cases cell with
      | atom cellId payload =>
          change decide (cellId < PolyTerm.termCellIdLimit) = false
          change
            (decide (PolyTerm.firstTypeCellId ≤ cellId) &&
              decide (cellId < PolyTerm.typeCellIdLimit)) = true at hRange
          cases hasTermBool : decide (cellId < PolyTerm.termCellIdLimit) with
          | false =>
              rfl
          | true =>
              have hasTermRange : cellId < PolyTerm.firstTypeCellId := by
                change cellId < PolyTerm.termCellIdLimit
                exact of_decide_eq_true hasTermBool
              cases hasLowerBool :
                  decide (PolyTerm.firstTypeCellId ≤ cellId) with
              | false =>
                  rw [hasLowerBool] at hRange
                  cases hRange
              | true =>
                  have hasLowerBound :
                      PolyTerm.firstTypeCellId ≤ cellId :=
                    of_decide_eq_true hasLowerBool
                  exact False.elim
                    (Nat.not_lt_of_ge hasLowerBound hasTermRange)

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

theorem FXStep.endpointEvidence_mk_sourceCell (ruleId : CellId)
    (source target : FXCellAt 0) :
    (FXStep.endpointEvidence_mk ruleId source target).sourceCell =
      source := rfl

theorem FXStep.endpointEvidence_mk_targetCell (ruleId : CellId)
    (source target : FXCellAt 0) :
    (FXStep.endpointEvidence_mk ruleId source target).targetCell =
      target := rfl

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

/-- FX term payload extraction from the provisional Nat-coded atom. -/
def FXTerm.payload : FXTerm → Nat
  | ⟨.atom _ payload, _⟩ => payload

/-- FX type cell id extraction. -/
def FXType.cellId : FXType → CellId
  | ⟨.atom cellId _, _⟩ => cellId

/-- FX type payload extraction from the provisional Nat-coded atom. -/
def FXType.payload : FXType → Nat
  | ⟨.atom _ payload, _⟩ => payload

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

theorem FXStep.endpointEvidence_seqChecked_sourceCell
    (first second : FXStep)
    (boundaryEvidence : PolyTerm.VerticalBoundaryEvidence first.val second.val)
    (firstEndpointEvidence : FXStep.EndpointEvidence first)
    (secondEndpointEvidence : FXStep.EndpointEvidence second) :
    (FXStep.endpointEvidence_seqChecked
      first second boundaryEvidence
      firstEndpointEvidence secondEndpointEvidence).sourceCell =
      firstEndpointEvidence.sourceCell := rfl

theorem FXStep.endpointEvidence_seqChecked_targetCell
    (first second : FXStep)
    (boundaryEvidence : PolyTerm.VerticalBoundaryEvidence first.val second.val)
    (firstEndpointEvidence : FXStep.EndpointEvidence first)
    (secondEndpointEvidence : FXStep.EndpointEvidence second) :
    (FXStep.endpointEvidence_seqChecked
      first second boundaryEvidence
      firstEndpointEvidence secondEndpointEvidence).targetCell =
      secondEndpointEvidence.targetCell := rfl

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

theorem FXStep.endpointEvidence_seqMkChecked_sourceCell
    (firstRuleId secondRuleId : CellId)
    (source middle target : FXCellAt 0) :
    (FXStep.endpointEvidence_seqMkChecked
      firstRuleId secondRuleId source middle target).sourceCell =
      source := rfl

theorem FXStep.endpointEvidence_seqMkChecked_targetCell
    (firstRuleId secondRuleId : CellId)
    (source middle target : FXCellAt 0) :
    (FXStep.endpointEvidence_seqMkChecked
      firstRuleId secondRuleId source middle target).targetCell =
      target := rfl

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

theorem FXStep.endpointEvidence_seqCheckedLeftAssociated_sourceCell
    (first second third : FXStep)
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first.val second.val)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second.val third.val)
    (firstEndpointEvidence : FXStep.EndpointEvidence first)
    (thirdEndpointEvidence : FXStep.EndpointEvidence third) :
    (FXStep.endpointEvidence_seqCheckedLeftAssociated
      first second third firstSecondEvidence secondThirdEvidence
      firstEndpointEvidence thirdEndpointEvidence).sourceCell =
      firstEndpointEvidence.sourceCell := rfl

theorem FXStep.endpointEvidence_seqCheckedLeftAssociated_targetCell
    (first second third : FXStep)
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first.val second.val)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second.val third.val)
    (firstEndpointEvidence : FXStep.EndpointEvidence first)
    (thirdEndpointEvidence : FXStep.EndpointEvidence third) :
    (FXStep.endpointEvidence_seqCheckedLeftAssociated
      first second third firstSecondEvidence secondThirdEvidence
      firstEndpointEvidence thirdEndpointEvidence).targetCell =
      thirdEndpointEvidence.targetCell := rfl

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

theorem FXStep.endpointEvidence_seqCheckedRightAssociated_sourceCell
    (first second third : FXStep)
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first.val second.val)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second.val third.val)
    (firstEndpointEvidence : FXStep.EndpointEvidence first)
    (thirdEndpointEvidence : FXStep.EndpointEvidence third) :
    (FXStep.endpointEvidence_seqCheckedRightAssociated
      first second third firstSecondEvidence secondThirdEvidence
      firstEndpointEvidence thirdEndpointEvidence).sourceCell =
      firstEndpointEvidence.sourceCell := rfl

theorem FXStep.endpointEvidence_seqCheckedRightAssociated_targetCell
    (first second third : FXStep)
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first.val second.val)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second.val third.val)
    (firstEndpointEvidence : FXStep.EndpointEvidence first)
    (thirdEndpointEvidence : FXStep.EndpointEvidence third) :
    (FXStep.endpointEvidence_seqCheckedRightAssociated
      first second third firstSecondEvidence secondThirdEvidence
      firstEndpointEvidence thirdEndpointEvidence).targetCell =
      thirdEndpointEvidence.targetCell := rfl

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

theorem FXStep.endpointEvidence_seqThreeMkCheckedLeftAssociated_sourceCell
    (firstRuleId secondRuleId thirdRuleId : CellId)
    (source firstMiddle secondMiddle target : FXCellAt 0) :
    (FXStep.endpointEvidence_seqThreeMkCheckedLeftAssociated
      firstRuleId secondRuleId thirdRuleId
      source firstMiddle secondMiddle target).sourceCell =
      source := rfl

theorem FXStep.endpointEvidence_seqThreeMkCheckedLeftAssociated_targetCell
    (firstRuleId secondRuleId thirdRuleId : CellId)
    (source firstMiddle secondMiddle target : FXCellAt 0) :
    (FXStep.endpointEvidence_seqThreeMkCheckedLeftAssociated
      firstRuleId secondRuleId thirdRuleId
      source firstMiddle secondMiddle target).targetCell =
      target := rfl

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

theorem FXStep.endpointEvidence_seqThreeMkCheckedRightAssociated_sourceCell
    (firstRuleId secondRuleId thirdRuleId : CellId)
    (source firstMiddle secondMiddle target : FXCellAt 0) :
    (FXStep.endpointEvidence_seqThreeMkCheckedRightAssociated
      firstRuleId secondRuleId thirdRuleId
      source firstMiddle secondMiddle target).sourceCell =
      source := rfl

theorem FXStep.endpointEvidence_seqThreeMkCheckedRightAssociated_targetCell
    (firstRuleId secondRuleId thirdRuleId : CellId)
    (source firstMiddle secondMiddle target : FXCellAt 0) :
    (FXStep.endpointEvidence_seqThreeMkCheckedRightAssociated
      firstRuleId secondRuleId thirdRuleId
      source firstMiddle secondMiddle target).targetCell =
      target := rfl

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

theorem FXCdLemma.endpointEvidence_cell_sourceCell (ruleId : CellId)
    (source target : FXCellAt 1) :
    (FXCdLemma.EndpointEvidence.cell ruleId source target).sourceCell =
      source := rfl

theorem FXCdLemma.endpointEvidence_cell_targetCell (ruleId : CellId)
    (source target : FXCellAt 1) :
    (FXCdLemma.EndpointEvidence.cell ruleId source target).targetCell =
      target := rfl

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

theorem FXCdLemma.endpointEvidence_associatorVChecked_sourceCell
    (first second third : FXCellAt 1)
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first second)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second third) :
    (FXCdLemma.endpointEvidence_associatorVChecked
      first second third firstSecondEvidence secondThirdEvidence).sourceCell =
      PolyTerm.compVCheckedLeftAssociated
        first second third firstSecondEvidence secondThirdEvidence := rfl

theorem FXCdLemma.endpointEvidence_associatorVChecked_targetCell
    (first second third : FXCellAt 1)
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first second)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second third) :
    (FXCdLemma.endpointEvidence_associatorVChecked
      first second third firstSecondEvidence secondThirdEvidence).targetCell =
      PolyTerm.compVCheckedRightAssociated
        first second third firstSecondEvidence secondThirdEvidence := rfl

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

theorem FXCdLemma.endpointEvidence_associatorVCheckedOfSteps_sourceCell
    (first second third : FXStep)
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first.val second.val)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second.val third.val) :
    (FXCdLemma.endpointEvidence_associatorVCheckedOfSteps
      first second third firstSecondEvidence secondThirdEvidence).sourceCell =
      (FXStep.seqCheckedLeftAssociated
        first second third firstSecondEvidence secondThirdEvidence).toCell := rfl

theorem FXCdLemma.endpointEvidence_associatorVCheckedOfSteps_targetCell
    (first second third : FXStep)
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first.val second.val)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second.val third.val) :
    (FXCdLemma.endpointEvidence_associatorVCheckedOfSteps
      first second third firstSecondEvidence secondThirdEvidence).targetCell =
      (FXStep.seqCheckedRightAssociated
        first second third firstSecondEvidence secondThirdEvidence).toCell := rfl

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

theorem FXCdLemma.endpointEvidence_associatorVCheckedOfStepMks_sourceCell
    (firstRuleId secondRuleId thirdRuleId : CellId)
    (source firstMiddle secondMiddle target : FXCellAt 0) :
    (FXCdLemma.endpointEvidence_associatorVCheckedOfStepMks
      firstRuleId secondRuleId thirdRuleId
      source firstMiddle secondMiddle target).sourceCell =
      (FXStep.seqThreeMkCheckedLeftAssociated
        firstRuleId secondRuleId thirdRuleId
        source firstMiddle secondMiddle target).toCell := rfl

theorem FXCdLemma.endpointEvidence_associatorVCheckedOfStepMks_targetCell
    (firstRuleId secondRuleId thirdRuleId : CellId)
    (source firstMiddle secondMiddle target : FXCellAt 0) :
    (FXCdLemma.endpointEvidence_associatorVCheckedOfStepMks
      firstRuleId secondRuleId thirdRuleId
      source firstMiddle secondMiddle target).targetCell =
      (FXStep.seqThreeMkCheckedRightAssociated
        firstRuleId secondRuleId thirdRuleId
        source firstMiddle secondMiddle target).toCell := rfl

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

theorem FXCdLemma.endpointEvidence_leftUnitorVChecked_sourceCell
    (sourceCell : FXCellAt 0)
    (cell : FXCellAt 1)
    (cellSource_eq : cell.source? = some sourceCell) :
    (FXCdLemma.endpointEvidence_leftUnitorVChecked
      sourceCell cell cellSource_eq).sourceCell =
      PolyTerm.compVChecked (.identity sourceCell) cell
        (PolyTerm.VerticalBoundaryEvidence.identityLeft
          sourceCell cell cellSource_eq) := rfl

theorem FXCdLemma.endpointEvidence_leftUnitorVChecked_targetCell
    (sourceCell : FXCellAt 0)
    (cell : FXCellAt 1)
    (cellSource_eq : cell.source? = some sourceCell) :
    (FXCdLemma.endpointEvidence_leftUnitorVChecked
      sourceCell cell cellSource_eq).targetCell =
      cell := rfl

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

theorem FXCdLemma.endpointEvidence_leftUnitorVCheckedOfStep_sourceCell
    (sourceCell : FXCellAt 0)
    (step : FXStep)
    (stepSource_eq : step.source? = some sourceCell) :
    (FXCdLemma.endpointEvidence_leftUnitorVCheckedOfStep
      sourceCell step stepSource_eq).sourceCell =
      PolyTerm.compVChecked (.identity sourceCell) step.toCell
        (PolyTerm.VerticalBoundaryEvidence.identityLeft
          sourceCell step.toCell stepSource_eq) := rfl

theorem FXCdLemma.endpointEvidence_leftUnitorVCheckedOfStep_targetCell
    (sourceCell : FXCellAt 0)
    (step : FXStep)
    (stepSource_eq : step.source? = some sourceCell) :
    (FXCdLemma.endpointEvidence_leftUnitorVCheckedOfStep
      sourceCell step stepSource_eq).targetCell =
      step.toCell := rfl

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

theorem FXCdLemma.endpointEvidence_rightUnitorVChecked_sourceCell
    (targetCell : FXCellAt 0)
    (cell : FXCellAt 1)
    (cellTarget_eq : cell.target? = some targetCell) :
    (FXCdLemma.endpointEvidence_rightUnitorVChecked
      targetCell cell cellTarget_eq).sourceCell =
      PolyTerm.compVChecked cell (.identity targetCell)
        (PolyTerm.VerticalBoundaryEvidence.identityRight
          cell targetCell cellTarget_eq) := rfl

theorem FXCdLemma.endpointEvidence_rightUnitorVChecked_targetCell
    (targetCell : FXCellAt 0)
    (cell : FXCellAt 1)
    (cellTarget_eq : cell.target? = some targetCell) :
    (FXCdLemma.endpointEvidence_rightUnitorVChecked
      targetCell cell cellTarget_eq).targetCell =
      cell := rfl

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

theorem FXCdLemma.endpointEvidence_rightUnitorVCheckedOfStep_sourceCell
    (targetCell : FXCellAt 0)
    (step : FXStep)
    (stepTarget_eq : step.target? = some targetCell) :
    (FXCdLemma.endpointEvidence_rightUnitorVCheckedOfStep
      targetCell step stepTarget_eq).sourceCell =
      PolyTerm.compVChecked step.toCell (.identity targetCell)
        (PolyTerm.VerticalBoundaryEvidence.identityRight
          step.toCell targetCell stepTarget_eq) := rfl

theorem FXCdLemma.endpointEvidence_rightUnitorVCheckedOfStep_targetCell
    (targetCell : FXCellAt 0)
    (step : FXStep)
    (stepTarget_eq : step.target? = some targetCell) :
    (FXCdLemma.endpointEvidence_rightUnitorVCheckedOfStep
      targetCell step stepTarget_eq).targetCell =
      step.toCell := rfl

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

theorem FXConv.endpointEvidence_refl_sourceCell (term : FXCellAt 0) :
    (FXConv.endpointEvidence_refl term).sourceCell = term := rfl

theorem FXConv.endpointEvidence_refl_targetCell (term : FXCellAt 0) :
    (FXConv.endpointEvidence_refl term).targetCell = term := rfl

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

theorem FXConv.endpointEvidence_trans_sourceCell
    (firstConversion secondConversion : FXConv)
    (firstEndpointEvidence : FXConv.EndpointEvidence firstConversion)
    (secondEndpointEvidence : FXConv.EndpointEvidence secondConversion) :
    (FXConv.endpointEvidence_trans
      firstConversion secondConversion
      firstEndpointEvidence secondEndpointEvidence).sourceCell =
      firstEndpointEvidence.sourceCell := rfl

theorem FXConv.endpointEvidence_trans_targetCell
    (firstConversion secondConversion : FXConv)
    (firstEndpointEvidence : FXConv.EndpointEvidence firstConversion)
    (secondEndpointEvidence : FXConv.EndpointEvidence secondConversion) :
    (FXConv.endpointEvidence_trans
      firstConversion secondConversion
      firstEndpointEvidence secondEndpointEvidence).targetCell =
      secondEndpointEvidence.targetCell := rfl

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

theorem FXConv.endpointEvidence_transChecked_sourceCell
    (firstConversion secondConversion : FXConv)
    (boundaryEvidence :
      PolyTerm.VerticalBoundaryEvidence firstConversion secondConversion)
    (firstEndpointEvidence : FXConv.EndpointEvidence firstConversion)
    (secondEndpointEvidence : FXConv.EndpointEvidence secondConversion) :
    (FXConv.endpointEvidence_transChecked
      firstConversion secondConversion boundaryEvidence
      firstEndpointEvidence secondEndpointEvidence).sourceCell =
      firstEndpointEvidence.sourceCell := rfl

theorem FXConv.endpointEvidence_transChecked_targetCell
    (firstConversion secondConversion : FXConv)
    (boundaryEvidence :
      PolyTerm.VerticalBoundaryEvidence firstConversion secondConversion)
    (firstEndpointEvidence : FXConv.EndpointEvidence firstConversion)
    (secondEndpointEvidence : FXConv.EndpointEvidence secondConversion) :
    (FXConv.endpointEvidence_transChecked
      firstConversion secondConversion boundaryEvidence
      firstEndpointEvidence secondEndpointEvidence).targetCell =
      secondEndpointEvidence.targetCell := rfl

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

theorem FXConv.endpointEvidence_transReflLeftChecked_sourceCell
    (base : FXCellAt 0)
    (conversion : FXConv)
    (conversionSource_eq : conversion.source? = some base)
    (conversionEndpointEvidence : FXConv.EndpointEvidence conversion) :
    (FXConv.endpointEvidence_transReflLeftChecked
      base conversion conversionSource_eq
      conversionEndpointEvidence).sourceCell =
      base := rfl

theorem FXConv.endpointEvidence_transReflLeftChecked_targetCell
    (base : FXCellAt 0)
    (conversion : FXConv)
    (conversionSource_eq : conversion.source? = some base)
    (conversionEndpointEvidence : FXConv.EndpointEvidence conversion) :
    (FXConv.endpointEvidence_transReflLeftChecked
      base conversion conversionSource_eq
      conversionEndpointEvidence).targetCell =
      conversionEndpointEvidence.targetCell := rfl

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

theorem FXConv.endpointEvidence_transReflRightChecked_sourceCell
    (conversion : FXConv)
    (base : FXCellAt 0)
    (conversionTarget_eq : conversion.target? = some base)
    (conversionEndpointEvidence : FXConv.EndpointEvidence conversion) :
    (FXConv.endpointEvidence_transReflRightChecked
      conversion base conversionTarget_eq
      conversionEndpointEvidence).sourceCell =
      conversionEndpointEvidence.sourceCell := rfl

theorem FXConv.endpointEvidence_transReflRightChecked_targetCell
    (conversion : FXConv)
    (base : FXCellAt 0)
    (conversionTarget_eq : conversion.target? = some base)
    (conversionEndpointEvidence : FXConv.EndpointEvidence conversion) :
    (FXConv.endpointEvidence_transReflRightChecked
      conversion base conversionTarget_eq
      conversionEndpointEvidence).targetCell =
      base := rfl

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

theorem FXConv.endpointEvidence_transCheckedLeftAssociated_sourceCell
    (first second third : FXConv)
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first second)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second third)
    (firstEndpointEvidence : FXConv.EndpointEvidence first)
    (thirdEndpointEvidence : FXConv.EndpointEvidence third) :
    (FXConv.endpointEvidence_transCheckedLeftAssociated
      first second third firstSecondEvidence secondThirdEvidence
      firstEndpointEvidence thirdEndpointEvidence).sourceCell =
      firstEndpointEvidence.sourceCell := rfl

theorem FXConv.endpointEvidence_transCheckedLeftAssociated_targetCell
    (first second third : FXConv)
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first second)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second third)
    (firstEndpointEvidence : FXConv.EndpointEvidence first)
    (thirdEndpointEvidence : FXConv.EndpointEvidence third) :
    (FXConv.endpointEvidence_transCheckedLeftAssociated
      first second third firstSecondEvidence secondThirdEvidence
      firstEndpointEvidence thirdEndpointEvidence).targetCell =
      thirdEndpointEvidence.targetCell := rfl

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

theorem FXConv.endpointEvidence_transCheckedRightAssociated_sourceCell
    (first second third : FXConv)
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first second)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second third)
    (firstEndpointEvidence : FXConv.EndpointEvidence first)
    (thirdEndpointEvidence : FXConv.EndpointEvidence third) :
    (FXConv.endpointEvidence_transCheckedRightAssociated
      first second third firstSecondEvidence secondThirdEvidence
      firstEndpointEvidence thirdEndpointEvidence).sourceCell =
      firstEndpointEvidence.sourceCell := rfl

theorem FXConv.endpointEvidence_transCheckedRightAssociated_targetCell
    (first second third : FXConv)
    (firstSecondEvidence : PolyTerm.VerticalBoundaryEvidence first second)
    (secondThirdEvidence : PolyTerm.VerticalBoundaryEvidence second third)
    (firstEndpointEvidence : FXConv.EndpointEvidence first)
    (thirdEndpointEvidence : FXConv.EndpointEvidence third) :
    (FXConv.endpointEvidence_transCheckedRightAssociated
      first second third firstSecondEvidence secondThirdEvidence
      firstEndpointEvidence thirdEndpointEvidence).targetCell =
      thirdEndpointEvidence.targetCell := rfl

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

theorem firstTypeCellId_le_typeCellIdLimit :
    PolyTerm.firstTypeCellId ≤ PolyTerm.typeCellIdLimit := by
  change
    PolyTerm.firstTypeCellId ≤
      PolyTerm.firstTypeCellId + PolyTerm.typeCellIdCount
  exact Nat.le_add_right _ _

theorem termGeneratorCount_le_totalGeneratorCount :
    termGeneratorCount ≤ totalGeneratorCount := by
  rw [← firstTypeCellId_eq_termGeneratorCount]
  rw [← typeCellIdLimit_eq_totalGeneratorCount]
  exact firstTypeCellId_le_typeCellIdLimit

/-- Names for the current typed `Term` constructor-id block.

This is a checked inventory of the provisional dim-0 term ids only.  It does
not decode payloads and does not assert any equivalence with typed kernel
terms. -/
inductive FXTermConstructorName where
  | var
  | unit
  | lam
  | app
  | lamPi
  | appPi
  | pair
  | fst
  | snd
  | boolTrue
  | boolFalse
  | boolElim
  | natZero
  | natSucc
  | natElim
  | natRec
  | listNil
  | listCons
  | listElim
  | optionNone
  | optionSome
  | optionMatch
  | eitherInl
  | eitherInr
  | eitherMatch
  | refl
  | idJ
  | oeqRefl
  | oeqJ
  | oeqFunext
  | idStrictRefl
  | idStrictRec
  | modIntro
  | modElim
  | subsume
  | interval0
  | interval1
  | intervalOpp
  | intervalMeet
  | intervalJoin
  | pathLam
  | pathApp
  | glueIntro
  | glueElim
  | transp
  | hcomp
  | hcompPath
  | recordIntro
  | recordProj
  | refineIntro
  | refineElim
  | codataUnfold
  | codataDest
  | sessionSend
  | sessionRecv
  | effectPerform
  | universeCode
  | cumulUp
  | equivReflId
  | funextRefl
  | equivReflIdAtId
  | funextReflAtId
  | equivIntroHet
  | equivApp
  | uaIntroHet
  | funextIntroHet
  | arrowCode
  | piTyCode
  | sigmaTyCode
  | productCode
  | sumCode
  | listCode
  | optionCode
  | eitherCode
  | idCode
  | equivCode
  | uaToEquiv
  | equivApply
  deriving DecidableEq, Repr

/-- Global dim-0 cell id assigned to a named typed-term constructor. -/
def FXTermConstructorName.cellId : FXTermConstructorName → CellId
  | .var => 0
  | .unit => 1
  | .lam => 2
  | .app => 3
  | .lamPi => 4
  | .appPi => 5
  | .pair => 6
  | .fst => 7
  | .snd => 8
  | .boolTrue => 9
  | .boolFalse => 10
  | .boolElim => 11
  | .natZero => 12
  | .natSucc => 13
  | .natElim => 14
  | .natRec => 15
  | .listNil => 16
  | .listCons => 17
  | .listElim => 18
  | .optionNone => 19
  | .optionSome => 20
  | .optionMatch => 21
  | .eitherInl => 22
  | .eitherInr => 23
  | .eitherMatch => 24
  | .refl => 25
  | .idJ => 26
  | .oeqRefl => 27
  | .oeqJ => 28
  | .oeqFunext => 29
  | .idStrictRefl => 30
  | .idStrictRec => 31
  | .modIntro => 32
  | .modElim => 33
  | .subsume => 34
  | .interval0 => 35
  | .interval1 => 36
  | .intervalOpp => 37
  | .intervalMeet => 38
  | .intervalJoin => 39
  | .pathLam => 40
  | .pathApp => 41
  | .glueIntro => 42
  | .glueElim => 43
  | .transp => 44
  | .hcomp => 45
  | .hcompPath => 46
  | .recordIntro => 47
  | .recordProj => 48
  | .refineIntro => 49
  | .refineElim => 50
  | .codataUnfold => 51
  | .codataDest => 52
  | .sessionSend => 53
  | .sessionRecv => 54
  | .effectPerform => 55
  | .universeCode => 56
  | .cumulUp => 57
  | .equivReflId => 58
  | .funextRefl => 59
  | .equivReflIdAtId => 60
  | .funextReflAtId => 61
  | .equivIntroHet => 62
  | .equivApp => 63
  | .uaIntroHet => 64
  | .funextIntroHet => 65
  | .arrowCode => 66
  | .piTyCode => 67
  | .sigmaTyCode => 68
  | .productCode => 69
  | .sumCode => 70
  | .listCode => 71
  | .optionCode => 72
  | .eitherCode => 73
  | .idCode => 74
  | .equivCode => 75
  | .uaToEquiv => 76
  | .equivApply => 77

theorem FXTermConstructorName.cellId_lt_termGeneratorCount
    (constructorName : FXTermConstructorName) :
    constructorName.cellId < termGeneratorCount := by
  cases constructorName <;> decide

theorem FXTermConstructorName.cellId_lt_firstTypeCellId
    (constructorName : FXTermConstructorName) :
    constructorName.cellId < PolyTerm.firstTypeCellId := by
  change constructorName.cellId < termGeneratorCount
  exact FXTermConstructorName.cellId_lt_termGeneratorCount constructorName

theorem FXTermConstructorName.cellId_lt_totalGeneratorCount
    (constructorName : FXTermConstructorName) :
    constructorName.cellId < totalGeneratorCount := by
  exact Nat.lt_of_lt_of_le
    (FXTermConstructorName.cellId_lt_termGeneratorCount constructorName)
    termGeneratorCount_le_totalGeneratorCount

/-- Checked constructor index for a named typed-term constructor. -/
def FXTermConstructorName.constructorIndex
    (constructorName : FXTermConstructorName) : Fin termGeneratorCount :=
  ⟨constructorName.cellId,
    FXTermConstructorName.cellId_lt_termGeneratorCount constructorName⟩

/-- Decode a global dim-0 term cell id into a named typed-term constructor. -/
def FXTermConstructorName.ofCellId? : CellId → Option FXTermConstructorName
  | 0 => some .var
  | 1 => some .unit
  | 2 => some .lam
  | 3 => some .app
  | 4 => some .lamPi
  | 5 => some .appPi
  | 6 => some .pair
  | 7 => some .fst
  | 8 => some .snd
  | 9 => some .boolTrue
  | 10 => some .boolFalse
  | 11 => some .boolElim
  | 12 => some .natZero
  | 13 => some .natSucc
  | 14 => some .natElim
  | 15 => some .natRec
  | 16 => some .listNil
  | 17 => some .listCons
  | 18 => some .listElim
  | 19 => some .optionNone
  | 20 => some .optionSome
  | 21 => some .optionMatch
  | 22 => some .eitherInl
  | 23 => some .eitherInr
  | 24 => some .eitherMatch
  | 25 => some .refl
  | 26 => some .idJ
  | 27 => some .oeqRefl
  | 28 => some .oeqJ
  | 29 => some .oeqFunext
  | 30 => some .idStrictRefl
  | 31 => some .idStrictRec
  | 32 => some .modIntro
  | 33 => some .modElim
  | 34 => some .subsume
  | 35 => some .interval0
  | 36 => some .interval1
  | 37 => some .intervalOpp
  | 38 => some .intervalMeet
  | 39 => some .intervalJoin
  | 40 => some .pathLam
  | 41 => some .pathApp
  | 42 => some .glueIntro
  | 43 => some .glueElim
  | 44 => some .transp
  | 45 => some .hcomp
  | 46 => some .hcompPath
  | 47 => some .recordIntro
  | 48 => some .recordProj
  | 49 => some .refineIntro
  | 50 => some .refineElim
  | 51 => some .codataUnfold
  | 52 => some .codataDest
  | 53 => some .sessionSend
  | 54 => some .sessionRecv
  | 55 => some .effectPerform
  | 56 => some .universeCode
  | 57 => some .cumulUp
  | 58 => some .equivReflId
  | 59 => some .funextRefl
  | 60 => some .equivReflIdAtId
  | 61 => some .funextReflAtId
  | 62 => some .equivIntroHet
  | 63 => some .equivApp
  | 64 => some .uaIntroHet
  | 65 => some .funextIntroHet
  | 66 => some .arrowCode
  | 67 => some .piTyCode
  | 68 => some .sigmaTyCode
  | 69 => some .productCode
  | 70 => some .sumCode
  | 71 => some .listCode
  | 72 => some .optionCode
  | 73 => some .eitherCode
  | 74 => some .idCode
  | 75 => some .equivCode
  | 76 => some .uaToEquiv
  | 77 => some .equivApply
  | _ => none

theorem FXTermConstructorName.ofCellId?_cellId
    (constructorName : FXTermConstructorName) :
    FXTermConstructorName.ofCellId? constructorName.cellId =
      some constructorName := by
  cases constructorName <;> rfl

theorem FXTermConstructorName.constructorIndex_val
    (constructorName : FXTermConstructorName) :
    constructorName.constructorIndex.val = constructorName.cellId := rfl

theorem FXTermConstructorName.cellId_injective
    {leftName rightName : FXTermConstructorName}
    (hasSameCellId : leftName.cellId = rightName.cellId) :
    leftName = rightName := by
  have hasSameDecode : some leftName = some rightName := by
    rw [← FXTermConstructorName.ofCellId?_cellId leftName]
    rw [← FXTermConstructorName.ofCellId?_cellId rightName]
    rw [hasSameCellId]
  cases hasSameDecode
  rfl

theorem FXTermConstructorName.constructorIndex_injective
    {leftName rightName : FXTermConstructorName}
    (hasSameConstructorIndex :
      leftName.constructorIndex = rightName.constructorIndex) :
    leftName = rightName := by
  apply FXTermConstructorName.cellId_injective
  rw [← FXTermConstructorName.constructorIndex_val leftName]
  rw [← FXTermConstructorName.constructorIndex_val rightName]
  exact congrArg Fin.val hasSameConstructorIndex

/-- Names for the current `Ty` constructor-id block.

This names the provisional dim-0 type ids only.  It does not decode payloads
and does not claim a bridge to the indexed `Ty` family. -/
inductive FXTypeConstructorName where
  | unit
  | bool
  | nat
  | arrow
  | piTy
  | sigmaTy
  | typeVar
  | identity
  | listType
  | optionType
  | eitherType
  | universe
  | empty
  | interval
  | path
  | glue
  | observationalEquality
  | strictIdentity
  | equivalence
  | refinement
  | record
  | codata
  | session
  | effect
  | modal
  deriving DecidableEq, Repr

/-- Local offset within the current type-constructor block. -/
def FXTypeConstructorName.localCellId : FXTypeConstructorName → CellId
  | .unit => 0
  | .bool => 1
  | .nat => 2
  | .arrow => 3
  | .piTy => 4
  | .sigmaTy => 5
  | .typeVar => 6
  | .identity => 7
  | .listType => 8
  | .optionType => 9
  | .eitherType => 10
  | .universe => 11
  | .empty => 12
  | .interval => 13
  | .path => 14
  | .glue => 15
  | .observationalEquality => 16
  | .strictIdentity => 17
  | .equivalence => 18
  | .refinement => 19
  | .record => 20
  | .codata => 21
  | .session => 22
  | .effect => 23
  | .modal => 24

/-- Global dim-0 cell id assigned to a named type constructor. -/
def FXTypeConstructorName.cellId
    (constructorName : FXTypeConstructorName) : CellId :=
  PolyTerm.firstTypeCellId + constructorName.localCellId

theorem FXTypeConstructorName.localCellId_lt_typeGeneratorCount
    (constructorName : FXTypeConstructorName) :
    constructorName.localCellId < typeGeneratorCount := by
  cases constructorName <;> decide

theorem FXTypeConstructorName.firstTypeCellId_le_cellId
    (constructorName : FXTypeConstructorName) :
    PolyTerm.firstTypeCellId ≤ constructorName.cellId := by
  change
    PolyTerm.firstTypeCellId ≤
      PolyTerm.firstTypeCellId + constructorName.localCellId
  exact Nat.le_add_right _ _

theorem FXTypeConstructorName.termGeneratorCount_le_cellId
    (constructorName : FXTypeConstructorName) :
    termGeneratorCount ≤ constructorName.cellId := by
  rw [← firstTypeCellId_eq_termGeneratorCount]
  exact FXTypeConstructorName.firstTypeCellId_le_cellId constructorName

theorem FXTypeConstructorName.cellId_lt_typeCellIdLimit
    (constructorName : FXTypeConstructorName) :
    constructorName.cellId < PolyTerm.typeCellIdLimit := by
  change
    PolyTerm.firstTypeCellId + constructorName.localCellId <
      PolyTerm.firstTypeCellId + PolyTerm.typeCellIdCount
  exact Nat.add_lt_add_left
    (FXTypeConstructorName.localCellId_lt_typeGeneratorCount constructorName)
    PolyTerm.firstTypeCellId

theorem FXTypeConstructorName.cellId_lt_totalGeneratorCount
    (constructorName : FXTypeConstructorName) :
    constructorName.cellId < totalGeneratorCount := by
  rw [← typeCellIdLimit_eq_totalGeneratorCount]
  exact FXTypeConstructorName.cellId_lt_typeCellIdLimit constructorName

/-- Checked constructor index for a named type constructor. -/
def FXTypeConstructorName.constructorIndex
    (constructorName : FXTypeConstructorName) : Fin typeGeneratorCount :=
  ⟨constructorName.localCellId,
    FXTypeConstructorName.localCellId_lt_typeGeneratorCount constructorName⟩

/-- Decode a local type-constructor offset into its name. -/
def FXTypeConstructorName.ofLocalCellId? :
    CellId → Option FXTypeConstructorName
  | 0 => some .unit
  | 1 => some .bool
  | 2 => some .nat
  | 3 => some .arrow
  | 4 => some .piTy
  | 5 => some .sigmaTy
  | 6 => some .typeVar
  | 7 => some .identity
  | 8 => some .listType
  | 9 => some .optionType
  | 10 => some .eitherType
  | 11 => some .universe
  | 12 => some .empty
  | 13 => some .interval
  | 14 => some .path
  | 15 => some .glue
  | 16 => some .observationalEquality
  | 17 => some .strictIdentity
  | 18 => some .equivalence
  | 19 => some .refinement
  | 20 => some .record
  | 21 => some .codata
  | 22 => some .session
  | 23 => some .effect
  | 24 => some .modal
  | _ => none

/-- Decode a global dim-0 type cell id into a named type constructor. -/
def FXTypeConstructorName.ofCellId? :
    CellId → Option FXTypeConstructorName
  | 78 => some .unit
  | 79 => some .bool
  | 80 => some .nat
  | 81 => some .arrow
  | 82 => some .piTy
  | 83 => some .sigmaTy
  | 84 => some .typeVar
  | 85 => some .identity
  | 86 => some .listType
  | 87 => some .optionType
  | 88 => some .eitherType
  | 89 => some .universe
  | 90 => some .empty
  | 91 => some .interval
  | 92 => some .path
  | 93 => some .glue
  | 94 => some .observationalEquality
  | 95 => some .strictIdentity
  | 96 => some .equivalence
  | 97 => some .refinement
  | 98 => some .record
  | 99 => some .codata
  | 100 => some .session
  | 101 => some .effect
  | 102 => some .modal
  | _ => none

theorem FXTypeConstructorName.ofLocalCellId?_localCellId
    (constructorName : FXTypeConstructorName) :
    FXTypeConstructorName.ofLocalCellId? constructorName.localCellId =
      some constructorName := by
  cases constructorName <;> rfl

theorem FXTypeConstructorName.ofCellId?_cellId
    (constructorName : FXTypeConstructorName) :
    FXTypeConstructorName.ofCellId? constructorName.cellId =
      some constructorName := by
  cases constructorName <;> rfl

theorem FXTypeConstructorName.constructorIndex_val
    (constructorName : FXTypeConstructorName) :
    constructorName.constructorIndex.val =
      constructorName.localCellId := rfl

theorem FXTypeConstructorName.cellId_eq_firstTypeCellId_add_localCellId
    (constructorName : FXTypeConstructorName) :
    constructorName.cellId =
      PolyTerm.firstTypeCellId + constructorName.localCellId := rfl

theorem FXTypeConstructorName.localCellId_injective
    {leftName rightName : FXTypeConstructorName}
    (hasSameLocalCellId : leftName.localCellId = rightName.localCellId) :
    leftName = rightName := by
  have hasSameDecode : some leftName = some rightName := by
    rw [← FXTypeConstructorName.ofLocalCellId?_localCellId leftName]
    rw [← FXTypeConstructorName.ofLocalCellId?_localCellId rightName]
    rw [hasSameLocalCellId]
  cases hasSameDecode
  rfl

theorem FXTypeConstructorName.cellId_injective
    {leftName rightName : FXTypeConstructorName}
    (hasSameCellId : leftName.cellId = rightName.cellId) :
    leftName = rightName := by
  have hasSameDecode : some leftName = some rightName := by
    rw [← FXTypeConstructorName.ofCellId?_cellId leftName]
    rw [← FXTypeConstructorName.ofCellId?_cellId rightName]
    rw [hasSameCellId]
  cases hasSameDecode
  rfl

theorem FXTypeConstructorName.constructorIndex_injective
    {leftName rightName : FXTypeConstructorName}
    (hasSameConstructorIndex :
      leftName.constructorIndex = rightName.constructorIndex) :
    leftName = rightName := by
  apply FXTypeConstructorName.localCellId_injective
  rw [← FXTypeConstructorName.constructorIndex_val leftName]
  rw [← FXTypeConstructorName.constructorIndex_val rightName]
  exact congrArg Fin.val hasSameConstructorIndex

theorem FXTypeConstructorName.ofCellId?_termConstructorCellId
    (constructorName : FXTermConstructorName) :
    FXTypeConstructorName.ofCellId? constructorName.cellId = none := by
  cases constructorName <;> rfl

theorem FXTermConstructorName.ofCellId?_typeConstructorCellId
    (constructorName : FXTypeConstructorName) :
    FXTermConstructorName.ofCellId? constructorName.cellId = none := by
  cases constructorName <;> rfl

private theorem nat_sub_lt_left_of_lt_add_structural {offset value count : Nat}
    (hasLowerBound : offset ≤ value)
    (hasUpperBound : value < offset + count) :
    value - offset < count := by
  induction offset generalizing value with
  | zero =>
      rw [Nat.sub_zero]
      rw [Nat.zero_add] at hasUpperBound
      exact hasUpperBound
  | succ previousOffset offsetInduction =>
      cases value with
      | zero =>
          cases hasLowerBound
      | succ previousValue =>
          rw [Nat.succ_sub_succ_eq_sub]
          apply offsetInduction
          · exact Nat.le_of_succ_le_succ hasLowerBound
          · rw [Nat.succ_add] at hasUpperBound
            exact Nat.lt_of_succ_lt_succ hasUpperBound

private theorem nat_add_sub_cancel_left_structural (offset value : Nat) :
    offset + value - offset = value := by
  induction offset with
  | zero =>
      rw [Nat.zero_add, Nat.sub_zero]
  | succ previousOffset offsetInduction =>
      rw [Nat.succ_add, Nat.succ_sub_succ_eq_sub]
      exact offsetInduction

private theorem nat_add_sub_cancel_of_le_structural {offset value : Nat}
    (hasLowerBound : offset ≤ value) :
    offset + (value - offset) = value := by
  induction offset generalizing value with
  | zero =>
      rw [Nat.zero_add, Nat.sub_zero]
  | succ previousOffset offsetInduction =>
      cases value with
      | zero =>
          cases hasLowerBound
      | succ previousValue =>
          rw [Nat.succ_sub_succ_eq_sub]
          rw [Nat.succ_add]
          rw [offsetInduction (Nat.le_of_succ_le_succ hasLowerBound)]

/-- Proof-carrying classification of current dim-0 generator ids.

This is only the provisional Nat-coded profile partition.  It does not decode
payloads and does not claim a legacy syntax bridge. -/
inductive FXDimZeroCellIdClass where
  /-- The id names one of the current term constructors. -/
  | termConstructor (constructorIndex : Fin termGeneratorCount)
  /-- The id names one of the current type constructors. -/
  | typeConstructor (constructorIndex : Fin typeGeneratorCount)
  /-- The id is outside the current term/type generator block. -/
  | outsideCurrentGeneratorRange
      (cellId : CellId) (hasOutsideRange : totalGeneratorCount ≤ cellId)

/-- Recover the global cell id represented by a dim-0 id classification. -/
def FXDimZeroCellIdClass.cellId :
    FXDimZeroCellIdClass → CellId
  | .termConstructor constructorIndex => constructorIndex.val
  | .typeConstructor constructorIndex =>
      PolyTerm.firstTypeCellId + constructorIndex.val
  | .outsideCurrentGeneratorRange cellId _ => cellId

/-- Does the classification identify a current term constructor? -/
def FXDimZeroCellIdClass.isTermConstructor :
    FXDimZeroCellIdClass → Bool
  | .termConstructor _ => true
  | .typeConstructor _ => false
  | .outsideCurrentGeneratorRange _ _ => false

/-- Does the classification identify a current type constructor? -/
def FXDimZeroCellIdClass.isTypeConstructor :
    FXDimZeroCellIdClass → Bool
  | .termConstructor _ => false
  | .typeConstructor _ => true
  | .outsideCurrentGeneratorRange _ _ => false

/-- Is the id outside the current term/type generator block? -/
def FXDimZeroCellIdClass.isOutsideCurrentGeneratorRange :
    FXDimZeroCellIdClass → Bool
  | .termConstructor _ => false
  | .typeConstructor _ => false
  | .outsideCurrentGeneratorRange _ _ => true

/-- Classify a raw dim-0 cell id against the current term/type generator block. -/
def classifyDimZeroCellId (cellId : CellId) : FXDimZeroCellIdClass :=
  if hasTermRange : cellId < termGeneratorCount then
    .termConstructor ⟨cellId, hasTermRange⟩
  else if hasCurrentRange : cellId < totalGeneratorCount then
    .typeConstructor ⟨cellId - PolyTerm.firstTypeCellId, by
      have hasLowerBound : PolyTerm.firstTypeCellId ≤ cellId := by
        change termGeneratorCount ≤ cellId
        exact Nat.le_of_not_gt hasTermRange
      have hasUpperBound :
          cellId < PolyTerm.firstTypeCellId + PolyTerm.typeCellIdCount := by
        change cellId < totalGeneratorCount at hasCurrentRange
        exact hasCurrentRange
      exact nat_sub_lt_left_of_lt_add_structural
        hasLowerBound hasUpperBound⟩
  else
    .outsideCurrentGeneratorRange cellId
      (Nat.le_of_not_gt hasCurrentRange)

theorem FXDimZeroCellIdClass.cellId_termConstructor
    (constructorIndex : Fin termGeneratorCount) :
    (FXDimZeroCellIdClass.termConstructor constructorIndex).cellId =
      constructorIndex.val := rfl

theorem FXDimZeroCellIdClass.cellId_typeConstructor
    (constructorIndex : Fin typeGeneratorCount) :
    (FXDimZeroCellIdClass.typeConstructor constructorIndex).cellId =
      PolyTerm.firstTypeCellId + constructorIndex.val := rfl

theorem FXDimZeroCellIdClass.cellId_outsideCurrentGeneratorRange
    (cellId : CellId) (hasOutsideRange : totalGeneratorCount ≤ cellId) :
    (FXDimZeroCellIdClass.outsideCurrentGeneratorRange
      cellId hasOutsideRange).cellId = cellId := rfl

theorem cellId_classifyDimZeroCellId (cellId : CellId) :
    (classifyDimZeroCellId cellId).cellId = cellId := by
  unfold classifyDimZeroCellId
  by_cases hasTermRange : cellId < termGeneratorCount
  · rw [dif_pos hasTermRange]
    rfl
  · rw [dif_neg hasTermRange]
    by_cases hasCurrentRange : cellId < totalGeneratorCount
    · rw [dif_pos hasCurrentRange]
      have hasLowerBound : PolyTerm.firstTypeCellId ≤ cellId := by
        change termGeneratorCount ≤ cellId
        exact Nat.le_of_not_gt hasTermRange
      change
        PolyTerm.firstTypeCellId +
          (cellId - PolyTerm.firstTypeCellId) = cellId
      rw [nat_add_sub_cancel_of_le_structural hasLowerBound]
    · rw [dif_neg hasCurrentRange]
      rfl

theorem classifyDimZeroCellId_ofTermConstructorName
    (constructorName : FXTermConstructorName) :
    classifyDimZeroCellId constructorName.cellId =
      FXDimZeroCellIdClass.termConstructor constructorName.constructorIndex := by
  cases constructorName <;> rfl

theorem classifyDimZeroCellId_ofTypeConstructorName
    (constructorName : FXTypeConstructorName) :
    classifyDimZeroCellId constructorName.cellId =
      FXDimZeroCellIdClass.typeConstructor constructorName.constructorIndex := by
  cases constructorName <;> rfl

theorem FXDimZeroCellIdClass.isTermConstructor_classifyTermConstructorName
    (constructorName : FXTermConstructorName) :
    (classifyDimZeroCellId constructorName.cellId).isTermConstructor =
      true := by
  cases constructorName <;> rfl

theorem FXDimZeroCellIdClass.isTypeConstructor_classifyTermConstructorName
    (constructorName : FXTermConstructorName) :
    (classifyDimZeroCellId constructorName.cellId).isTypeConstructor =
      false := by
  cases constructorName <;> rfl

theorem FXDimZeroCellIdClass.isOutsideCurrentGeneratorRange_classifyTermConstructorName
    (constructorName : FXTermConstructorName) :
    (classifyDimZeroCellId constructorName.cellId).isOutsideCurrentGeneratorRange =
      false := by
  cases constructorName <;> rfl

theorem FXDimZeroCellIdClass.isTermConstructor_classifyTypeConstructorName
    (constructorName : FXTypeConstructorName) :
    (classifyDimZeroCellId constructorName.cellId).isTermConstructor =
      false := by
  cases constructorName <;> rfl

theorem FXDimZeroCellIdClass.isTypeConstructor_classifyTypeConstructorName
    (constructorName : FXTypeConstructorName) :
    (classifyDimZeroCellId constructorName.cellId).isTypeConstructor =
      true := by
  cases constructorName <;> rfl

theorem FXDimZeroCellIdClass.isOutsideCurrentGeneratorRange_classifyTypeConstructorName
    (constructorName : FXTypeConstructorName) :
    (classifyDimZeroCellId constructorName.cellId).isOutsideCurrentGeneratorRange =
      false := by
  cases constructorName <;> rfl

/-- The checked local constructor index of an FX term atom. -/
def FXTerm.constructorIndex (term : FXTerm) : Fin termGeneratorCount :=
  match term with
  | ⟨.atom cellId _, hRange⟩ =>
      ⟨cellId, by
        change cellId < PolyTerm.termCellIdLimit
        exact of_decide_eq_true hRange⟩

/-- The checked local constructor index of an FX type atom.

Type ids occupy the provisional global block `[78, 103)`, so the local index
subtracts the first type id after extracting the range proof from the view. -/
def FXType.constructorIndex (typeCell : FXType) : Fin typeGeneratorCount :=
  match typeCell with
  | ⟨.atom cellId _, hRange⟩ =>
      ⟨cellId - PolyTerm.firstTypeCellId, by
        change cellId - PolyTerm.firstTypeCellId < PolyTerm.typeCellIdCount
        change
          (decide (PolyTerm.firstTypeCellId ≤ cellId) &&
            decide (cellId < PolyTerm.typeCellIdLimit)) = true at hRange
        have hasLowerBoundDecide :
            decide (PolyTerm.firstTypeCellId ≤ cellId) = true := by
          cases hasLowerBool :
              decide (PolyTerm.firstTypeCellId ≤ cellId) with
          | false =>
              rw [hasLowerBool] at hRange
              cases hRange
          | true =>
              rfl
        have hasUpperBoundDecide :
            decide (cellId < PolyTerm.typeCellIdLimit) = true := by
          cases hasLowerBool :
              decide (PolyTerm.firstTypeCellId ≤ cellId) with
          | false =>
              rw [hasLowerBool] at hRange
              cases hRange
          | true =>
              cases hasUpperBool :
                  decide (cellId < PolyTerm.typeCellIdLimit) with
              | false =>
                  rw [hasLowerBool, hasUpperBool] at hRange
                  cases hRange
              | true =>
                  rfl
        have hasLowerBound : PolyTerm.firstTypeCellId ≤ cellId :=
          of_decide_eq_true hasLowerBoundDecide
        have hasUpperBound :
            cellId < PolyTerm.firstTypeCellId + PolyTerm.typeCellIdCount := by
          change cellId < PolyTerm.firstTypeCellId + PolyTerm.typeCellIdCount
          exact of_decide_eq_true hasUpperBoundDecide
        exact nat_sub_lt_left_of_lt_add_structural
          hasLowerBound hasUpperBound⟩

/-- Construct an FX term from a checked index into the current term-id block. -/
def FXTerm.ofConstructorIndex (constructorIndex : Fin termGeneratorCount)
    (payload : Nat) : FXTerm :=
  ⟨.atom constructorIndex.val payload, by
    change decide (constructorIndex.val < PolyTerm.termCellIdLimit) = true
    exact decide_eq_true constructorIndex.isLt⟩

/-- Construct an FX term from a named current typed-term constructor id. -/
def FXTerm.ofConstructorName
    (constructorName : FXTermConstructorName) (payload : Nat) : FXTerm :=
  FXTerm.ofConstructorIndex constructorName.constructorIndex payload

/-- Construct an FX type from a checked index into the current type-id block. -/
def FXType.ofConstructorIndex (constructorIndex : Fin typeGeneratorCount)
    (payload : Nat) : FXType :=
  ⟨.atom (PolyTerm.firstTypeCellId + constructorIndex.val) payload, by
    change
      (decide
          (PolyTerm.firstTypeCellId ≤
            PolyTerm.firstTypeCellId + constructorIndex.val) &&
        decide
          (PolyTerm.firstTypeCellId + constructorIndex.val <
            PolyTerm.typeCellIdLimit)) = true
    have hasLowerBound :
        decide
          (PolyTerm.firstTypeCellId ≤
            PolyTerm.firstTypeCellId + constructorIndex.val) = true :=
      decide_eq_true (Nat.le_add_right _ _)
    have hasUpperBound :
        decide
          (PolyTerm.firstTypeCellId + constructorIndex.val <
            PolyTerm.typeCellIdLimit) = true :=
      decide_eq_true (Nat.add_lt_add_left constructorIndex.isLt
        PolyTerm.firstTypeCellId)
    rw [hasLowerBound, hasUpperBound]
    rfl⟩

/-- Construct an FX type from a named current `Ty` constructor id. -/
def FXType.ofConstructorName
    (constructorName : FXTypeConstructorName) (payload : Nat) : FXType :=
  FXType.ofConstructorIndex constructorName.constructorIndex payload

/-- Try to recover the named current typed-term constructor id from an FX term. -/
def FXTerm.constructorName? (term : FXTerm) :
    Option FXTermConstructorName :=
  FXTermConstructorName.ofCellId? term.cellId

/-- Try to recover the named current `Ty` constructor id from an FX type. -/
def FXType.constructorName? (typeCell : FXType) :
    Option FXTypeConstructorName :=
  FXTypeConstructorName.ofCellId? typeCell.cellId

theorem FXTerm.cellId_ofConstructorIndex
    (constructorIndex : Fin termGeneratorCount) (payload : Nat) :
    (FXTerm.ofConstructorIndex constructorIndex payload).cellId =
      constructorIndex.val := rfl

theorem FXTerm.payload_ofConstructorIndex
    (constructorIndex : Fin termGeneratorCount) (payload : Nat) :
    (FXTerm.ofConstructorIndex constructorIndex payload).payload =
      payload := rfl

theorem FXTerm.cellId_ofConstructorName
    (constructorName : FXTermConstructorName) (payload : Nat) :
    (FXTerm.ofConstructorName constructorName payload).cellId =
      constructorName.cellId := rfl

theorem FXTerm.payload_ofConstructorName
    (constructorName : FXTermConstructorName) (payload : Nat) :
    (FXTerm.ofConstructorName constructorName payload).payload =
      payload := rfl

theorem FXTerm.constructorIndex_val_ofConstructorIndex
    (constructorIndex : Fin termGeneratorCount) (payload : Nat) :
    (FXTerm.ofConstructorIndex constructorIndex payload).constructorIndex.val =
      constructorIndex.val := rfl

theorem FXTerm.constructorIndex_val_ofConstructorName
    (constructorName : FXTermConstructorName) (payload : Nat) :
    (FXTerm.ofConstructorName constructorName payload).constructorIndex.val =
      constructorName.cellId := rfl

theorem FXTerm.constructorName?_ofConstructorName
    (constructorName : FXTermConstructorName) (payload : Nat) :
    (FXTerm.ofConstructorName constructorName payload).constructorName? =
      some constructorName := by
  cases constructorName <;> rfl

theorem FXTerm.cellId_eq_constructorIndex_val (term : FXTerm) :
    term.cellId = term.constructorIndex.val := by
  cases term with
  | mk cell hRange =>
      cases cell with
      | atom cellId payload =>
          rfl

theorem FXTerm.toCell_ofConstructorIndex_constructorIndex_payload
    (term : FXTerm) :
    (FXTerm.ofConstructorIndex term.constructorIndex term.payload).toCell =
      term.toCell := by
  cases term with
  | mk cell hRange =>
      cases cell with
      | atom cellId payload =>
          rfl

theorem FXTerm.toCell_eq_atom_cellId_payload (term : FXTerm) :
    term.toCell = .atom term.cellId term.payload := by
  cases term with
  | mk cell hRange =>
      cases cell with
      | atom cellId payload =>
          rfl

theorem FXTerm.cellId_eq_of_toCell_eq
    {leftTerm rightTerm : FXTerm}
    (hasSameCell : leftTerm.toCell = rightTerm.toCell) :
    leftTerm.cellId = rightTerm.cellId := by
  cases leftTerm with
  | mk leftCell leftRange =>
      cases rightTerm with
      | mk rightCell rightRange =>
          cases leftCell with
          | atom leftCellId leftPayload =>
              cases rightCell with
              | atom rightCellId rightPayload =>
                  cases hasSameCell
                  rfl

theorem FXTerm.payload_eq_of_toCell_eq
    {leftTerm rightTerm : FXTerm}
    (hasSameCell : leftTerm.toCell = rightTerm.toCell) :
    leftTerm.payload = rightTerm.payload := by
  cases leftTerm with
  | mk leftCell leftRange =>
      cases rightTerm with
      | mk rightCell rightRange =>
          cases leftCell with
          | atom leftCellId leftPayload =>
              cases rightCell with
              | atom rightCellId rightPayload =>
                  cases hasSameCell
                  rfl

theorem FXType.cellId_ofConstructorIndex
    (constructorIndex : Fin typeGeneratorCount) (payload : Nat) :
    (FXType.ofConstructorIndex constructorIndex payload).cellId =
      PolyTerm.firstTypeCellId + constructorIndex.val := rfl

theorem FXType.payload_ofConstructorIndex
    (constructorIndex : Fin typeGeneratorCount) (payload : Nat) :
    (FXType.ofConstructorIndex constructorIndex payload).payload =
      payload := rfl

theorem FXType.cellId_ofConstructorName
    (constructorName : FXTypeConstructorName) (payload : Nat) :
    (FXType.ofConstructorName constructorName payload).cellId =
      constructorName.cellId := rfl

theorem FXType.payload_ofConstructorName
    (constructorName : FXTypeConstructorName) (payload : Nat) :
    (FXType.ofConstructorName constructorName payload).payload =
      payload := rfl

theorem FXType.constructorIndex_val_ofConstructorIndex
    (constructorIndex : Fin typeGeneratorCount) (payload : Nat) :
    (FXType.ofConstructorIndex constructorIndex payload).constructorIndex.val =
      constructorIndex.val := by
  change
    (PolyTerm.firstTypeCellId + constructorIndex.val) -
      PolyTerm.firstTypeCellId = constructorIndex.val
  exact nat_add_sub_cancel_left_structural
    PolyTerm.firstTypeCellId constructorIndex.val

theorem FXType.constructorIndex_val_ofConstructorName
    (constructorName : FXTypeConstructorName) (payload : Nat) :
    (FXType.ofConstructorName constructorName payload).constructorIndex.val =
      constructorName.localCellId := by
  exact FXType.constructorIndex_val_ofConstructorIndex
    constructorName.constructorIndex payload

theorem FXType.constructorName?_ofConstructorName
    (constructorName : FXTypeConstructorName) (payload : Nat) :
    (FXType.ofConstructorName constructorName payload).constructorName? =
      some constructorName := by
  cases constructorName <;> rfl

theorem FXType.cellId_eq_firstTypeCellId_add_constructorIndex_val
    (typeCell : FXType) :
    typeCell.cellId =
      PolyTerm.firstTypeCellId + typeCell.constructorIndex.val := by
  cases typeCell with
  | mk cell hRange =>
      cases cell with
      | atom cellId payload =>
          change
            cellId =
              PolyTerm.firstTypeCellId +
                (cellId - PolyTerm.firstTypeCellId)
          change
            (decide (PolyTerm.firstTypeCellId ≤ cellId) &&
              decide (cellId < PolyTerm.typeCellIdLimit)) = true at hRange
          have hasLowerBoundDecide :
              decide (PolyTerm.firstTypeCellId ≤ cellId) = true := by
            cases hasLowerBool :
                decide (PolyTerm.firstTypeCellId ≤ cellId) with
            | false =>
                rw [hasLowerBool] at hRange
                cases hRange
            | true =>
                rfl
          have hasLowerBound : PolyTerm.firstTypeCellId ≤ cellId :=
            of_decide_eq_true hasLowerBoundDecide
          rw [nat_add_sub_cancel_of_le_structural hasLowerBound]

theorem FXType.toCell_ofConstructorIndex_constructorIndex_payload
    (typeCell : FXType) :
    (FXType.ofConstructorIndex
        typeCell.constructorIndex typeCell.payload).toCell =
      typeCell.toCell := by
  cases typeCell with
  | mk cell hRange =>
      cases cell with
      | atom cellId payload =>
          change
            (PolyTerm.atom
                (PolyTerm.firstTypeCellId +
                  (cellId - PolyTerm.firstTypeCellId))
                payload :
              FXCellAt 0) =
              .atom cellId payload
          change
            (decide (PolyTerm.firstTypeCellId ≤ cellId) &&
              decide (cellId < PolyTerm.typeCellIdLimit)) = true at hRange
          have hasLowerBoundDecide :
              decide (PolyTerm.firstTypeCellId ≤ cellId) = true := by
            cases hasLowerBool :
                decide (PolyTerm.firstTypeCellId ≤ cellId) with
            | false =>
                rw [hasLowerBool] at hRange
                cases hRange
            | true =>
                rfl
          have hasLowerBound : PolyTerm.firstTypeCellId ≤ cellId :=
            of_decide_eq_true hasLowerBoundDecide
          rw [nat_add_sub_cancel_of_le_structural hasLowerBound]

theorem FXType.toCell_eq_atom_cellId_payload (typeCell : FXType) :
    typeCell.toCell = .atom typeCell.cellId typeCell.payload := by
  cases typeCell with
  | mk cell hRange =>
      cases cell with
      | atom cellId payload =>
          rfl

theorem FXType.cellId_eq_of_toCell_eq
    {leftType rightType : FXType}
    (hasSameCell : leftType.toCell = rightType.toCell) :
    leftType.cellId = rightType.cellId := by
  cases leftType with
  | mk leftCell leftRange =>
      cases rightType with
      | mk rightCell rightRange =>
          cases leftCell with
          | atom leftCellId leftPayload =>
              cases rightCell with
              | atom rightCellId rightPayload =>
                  cases hasSameCell
                  rfl

theorem FXType.payload_eq_of_toCell_eq
    {leftType rightType : FXType}
    (hasSameCell : leftType.toCell = rightType.toCell) :
    leftType.payload = rightType.payload := by
  cases leftType with
  | mk leftCell leftRange =>
      cases rightType with
      | mk rightCell rightRange =>
          cases leftCell with
          | atom leftCellId leftPayload =>
              cases rightCell with
              | atom rightCellId rightPayload =>
                  cases hasSameCell
                  rfl

theorem FXTerm.constructorName_eq_ofConstructorName_toCell_eq
    {leftName rightName : FXTermConstructorName}
    {leftPayload rightPayload : Nat}
    (hasSameCell :
      (FXTerm.ofConstructorName leftName leftPayload).toCell =
        (FXTerm.ofConstructorName rightName rightPayload).toCell) :
    leftName = rightName := by
  apply FXTermConstructorName.cellId_injective
  have hasSameCellId :=
    FXTerm.cellId_eq_of_toCell_eq hasSameCell
  rw [FXTerm.cellId_ofConstructorName] at hasSameCellId
  rw [FXTerm.cellId_ofConstructorName] at hasSameCellId
  exact hasSameCellId

theorem FXTerm.payload_eq_ofConstructorName_toCell_eq
    {leftName rightName : FXTermConstructorName}
    {leftPayload rightPayload : Nat}
    (hasSameCell :
      (FXTerm.ofConstructorName leftName leftPayload).toCell =
        (FXTerm.ofConstructorName rightName rightPayload).toCell) :
    leftPayload = rightPayload := by
  have hasSamePayload :=
    FXTerm.payload_eq_of_toCell_eq hasSameCell
  rw [FXTerm.payload_ofConstructorName] at hasSamePayload
  rw [FXTerm.payload_ofConstructorName] at hasSamePayload
  exact hasSamePayload

theorem FXType.constructorName_eq_ofConstructorName_toCell_eq
    {leftName rightName : FXTypeConstructorName}
    {leftPayload rightPayload : Nat}
    (hasSameCell :
      (FXType.ofConstructorName leftName leftPayload).toCell =
        (FXType.ofConstructorName rightName rightPayload).toCell) :
    leftName = rightName := by
  apply FXTypeConstructorName.cellId_injective
  have hasSameCellId :=
    FXType.cellId_eq_of_toCell_eq hasSameCell
  rw [FXType.cellId_ofConstructorName] at hasSameCellId
  rw [FXType.cellId_ofConstructorName] at hasSameCellId
  exact hasSameCellId

theorem FXType.payload_eq_ofConstructorName_toCell_eq
    {leftName rightName : FXTypeConstructorName}
    {leftPayload rightPayload : Nat}
    (hasSameCell :
      (FXType.ofConstructorName leftName leftPayload).toCell =
        (FXType.ofConstructorName rightName rightPayload).toCell) :
    leftPayload = rightPayload := by
  have hasSamePayload :=
    FXType.payload_eq_of_toCell_eq hasSameCell
  rw [FXType.payload_ofConstructorName] at hasSamePayload
  rw [FXType.payload_ofConstructorName] at hasSamePayload
  exact hasSamePayload

/-- Decode a current term constructor id and payload into an FX term view. -/
def FXTerm.ofCellId? (cellId : CellId) (payload : Nat) : Option FXTerm :=
  match classifyDimZeroCellId cellId with
  | .termConstructor constructorIndex =>
      some (FXTerm.ofConstructorIndex constructorIndex payload)
  | .typeConstructor _ => none
  | .outsideCurrentGeneratorRange _ _ => none

/-- Decode a current type constructor id and payload into an FX type view. -/
def FXType.ofCellId? (cellId : CellId) (payload : Nat) : Option FXType :=
  match classifyDimZeroCellId cellId with
  | .termConstructor _ => none
  | .typeConstructor constructorIndex =>
      some (FXType.ofConstructorIndex constructorIndex payload)
  | .outsideCurrentGeneratorRange _ _ => none

theorem FXTerm.ofCellId?_ofConstructorIndex
    (constructorIndex : Fin termGeneratorCount) (payload : Nat) :
    FXTerm.ofCellId? constructorIndex.val payload =
      some (FXTerm.ofConstructorIndex constructorIndex payload) := by
  unfold FXTerm.ofCellId?
  unfold classifyDimZeroCellId
  rw [dif_pos constructorIndex.isLt]

theorem FXTerm.toCell?_ofCellId?_ofConstructorIndex
    (constructorIndex : Fin termGeneratorCount) (payload : Nat) :
    Option.map FXTerm.toCell
        (FXTerm.ofCellId? constructorIndex.val payload) =
      some (FXTerm.ofConstructorIndex constructorIndex payload).toCell := by
  rw [FXTerm.ofCellId?_ofConstructorIndex]
  rfl

theorem FXTerm.ofCellId?_ofConstructorName
    (constructorName : FXTermConstructorName) (payload : Nat) :
    FXTerm.ofCellId? constructorName.cellId payload =
      some (FXTerm.ofConstructorName constructorName payload) := by
  exact FXTerm.ofCellId?_ofConstructorIndex
    constructorName.constructorIndex payload

theorem FXType.toCell?_ofCellId?_ofConstructorIndex
    (constructorIndex : Fin typeGeneratorCount) (payload : Nat) :
    Option.map FXType.toCell
        (FXType.ofCellId?
          (PolyTerm.firstTypeCellId + constructorIndex.val) payload) =
      some (FXType.ofConstructorIndex constructorIndex payload).toCell := by
  unfold FXType.ofCellId?
  unfold classifyDimZeroCellId
  have hasNoTermRange :
      ¬PolyTerm.firstTypeCellId + constructorIndex.val <
        termGeneratorCount := by
    change
      ¬PolyTerm.firstTypeCellId + constructorIndex.val <
        PolyTerm.firstTypeCellId
    exact Nat.not_lt_of_ge (Nat.le_add_right _ _)
  have hasCurrentRange :
      PolyTerm.firstTypeCellId + constructorIndex.val <
        totalGeneratorCount := by
    change
      PolyTerm.firstTypeCellId + constructorIndex.val <
        PolyTerm.typeCellIdLimit
    exact Nat.add_lt_add_left constructorIndex.isLt
      PolyTerm.firstTypeCellId
  rw [dif_neg hasNoTermRange, dif_pos hasCurrentRange]
  change
    some
      ((PolyTerm.atom
          (PolyTerm.firstTypeCellId +
            ((PolyTerm.firstTypeCellId + constructorIndex.val) -
              PolyTerm.firstTypeCellId))
          payload :
        FXCellAt 0)) =
      some
        (PolyTerm.atom
          (PolyTerm.firstTypeCellId + constructorIndex.val)
          payload)
  rw [nat_add_sub_cancel_left_structural]

theorem FXType.ofCellId?_ofConstructorName
    (constructorName : FXTypeConstructorName) (payload : Nat) :
    FXType.ofCellId? constructorName.cellId payload =
      some (FXType.ofConstructorName constructorName payload) := by
  cases constructorName <;> rfl

theorem FXTerm.ofCellId?_ofTypeConstructorIndex
    (constructorIndex : Fin typeGeneratorCount) (payload : Nat) :
    FXTerm.ofCellId?
        (PolyTerm.firstTypeCellId + constructorIndex.val) payload =
      none := by
  unfold FXTerm.ofCellId?
  unfold classifyDimZeroCellId
  have hasNoTermRange :
      ¬PolyTerm.firstTypeCellId + constructorIndex.val <
        termGeneratorCount := by
    change
      ¬PolyTerm.firstTypeCellId + constructorIndex.val <
        PolyTerm.firstTypeCellId
    exact Nat.not_lt_of_ge (Nat.le_add_right _ _)
  have hasCurrentRange :
      PolyTerm.firstTypeCellId + constructorIndex.val <
        totalGeneratorCount := by
    change
      PolyTerm.firstTypeCellId + constructorIndex.val <
        PolyTerm.typeCellIdLimit
    exact Nat.add_lt_add_left constructorIndex.isLt
      PolyTerm.firstTypeCellId
  rw [dif_neg hasNoTermRange, dif_pos hasCurrentRange]

theorem FXType.ofCellId?_ofTermConstructorIndex
    (constructorIndex : Fin termGeneratorCount) (payload : Nat) :
    FXType.ofCellId? constructorIndex.val payload = none := by
  unfold FXType.ofCellId?
  unfold classifyDimZeroCellId
  rw [dif_pos constructorIndex.isLt]

theorem FXTerm.ofCellId?_ofOutsideCurrentGeneratorRange
    (cellId : CellId) (payload : Nat)
    (hasOutsideRange : totalGeneratorCount ≤ cellId) :
    FXTerm.ofCellId? cellId payload = none := by
  unfold FXTerm.ofCellId?
  unfold classifyDimZeroCellId
  have hasTermBelowTotal : termGeneratorCount ≤ totalGeneratorCount := by
    change termGeneratorCount ≤ termGeneratorCount + typeGeneratorCount
    exact Nat.le_add_right _ _
  have hasNoTermRange : ¬cellId < termGeneratorCount := by
    intro hasTermRange
    exact Nat.not_lt_of_ge hasOutsideRange
      (Nat.lt_of_lt_of_le hasTermRange hasTermBelowTotal)
  have hasNoCurrentRange : ¬cellId < totalGeneratorCount :=
    Nat.not_lt_of_ge hasOutsideRange
  rw [dif_neg hasNoTermRange, dif_neg hasNoCurrentRange]

theorem FXType.ofCellId?_ofOutsideCurrentGeneratorRange
    (cellId : CellId) (payload : Nat)
    (hasOutsideRange : totalGeneratorCount ≤ cellId) :
    FXType.ofCellId? cellId payload = none := by
  unfold FXType.ofCellId?
  unfold classifyDimZeroCellId
  have hasTermBelowTotal : termGeneratorCount ≤ totalGeneratorCount := by
    change termGeneratorCount ≤ termGeneratorCount + typeGeneratorCount
    exact Nat.le_add_right _ _
  have hasNoTermRange : ¬cellId < termGeneratorCount := by
    intro hasTermRange
    exact Nat.not_lt_of_ge hasOutsideRange
      (Nat.lt_of_lt_of_le hasTermRange hasTermBelowTotal)
  have hasNoCurrentRange : ¬cellId < totalGeneratorCount :=
    Nat.not_lt_of_ge hasOutsideRange
  rw [dif_neg hasNoTermRange, dif_neg hasNoCurrentRange]

/-- Decode a dim-0 FX cell into the term view when its id is in the current
term-constructor block. -/
def FXTerm.ofCell? (cell : FXCellAt 0) : Option FXTerm :=
  match cell with
  | .atom cellId payload => FXTerm.ofCellId? cellId payload

/-- Decode a dim-0 FX cell into the type view when its id is in the current
type-constructor block. -/
def FXType.ofCell? (cell : FXCellAt 0) : Option FXType :=
  match cell with
  | .atom cellId payload => FXType.ofCellId? cellId payload

theorem FXTerm.ofCell?_ofConstructorIndex_toCell
    (constructorIndex : Fin termGeneratorCount) (payload : Nat) :
    FXTerm.ofCell?
        (FXTerm.ofConstructorIndex constructorIndex payload).toCell =
      some (FXTerm.ofConstructorIndex constructorIndex payload) := by
  change FXTerm.ofCellId? constructorIndex.val payload =
    some (FXTerm.ofConstructorIndex constructorIndex payload)
  exact FXTerm.ofCellId?_ofConstructorIndex constructorIndex payload

theorem FXTerm.ofCell?_ofConstructorName_toCell
    (constructorName : FXTermConstructorName) (payload : Nat) :
    FXTerm.ofCell? (FXTerm.ofConstructorName constructorName payload).toCell =
      some (FXTerm.ofConstructorName constructorName payload) := by
  change FXTerm.ofCellId? constructorName.cellId payload =
    some (FXTerm.ofConstructorName constructorName payload)
  exact FXTerm.ofCellId?_ofConstructorName constructorName payload

theorem FXType.ofCell?_ofConstructorName_toCell
    (constructorName : FXTypeConstructorName) (payload : Nat) :
    FXType.ofCell? (FXType.ofConstructorName constructorName payload).toCell =
      some (FXType.ofConstructorName constructorName payload) := by
  change FXType.ofCellId? constructorName.cellId payload =
    some (FXType.ofConstructorName constructorName payload)
  exact FXType.ofCellId?_ofConstructorName constructorName payload

theorem FXTerm.constructorIndex_val_ofCell?_ofConstructorIndex_toCell
    (constructorIndex : Fin termGeneratorCount) (payload : Nat) :
    Option.map (fun decodedTerm => decodedTerm.constructorIndex.val)
        (FXTerm.ofCell?
          (FXTerm.ofConstructorIndex constructorIndex payload).toCell) =
      some constructorIndex.val := by
  rw [FXTerm.ofCell?_ofConstructorIndex_toCell]
  change
    some
      (FXTerm.ofConstructorIndex constructorIndex payload).constructorIndex.val =
        some constructorIndex.val
  rw [FXTerm.constructorIndex_val_ofConstructorIndex]

theorem FXTerm.constructorIndex_val_ofCell?_ofConstructorName_toCell
    (constructorName : FXTermConstructorName) (payload : Nat) :
    Option.map (fun decodedTerm => decodedTerm.constructorIndex.val)
        (FXTerm.ofCell?
          (FXTerm.ofConstructorName constructorName payload).toCell) =
      some constructorName.cellId := by
  rw [FXTerm.ofCell?_ofConstructorName_toCell]
  change
    some
      (FXTerm.ofConstructorName constructorName payload).constructorIndex.val =
        some constructorName.cellId
  rw [FXTerm.constructorIndex_val_ofConstructorName]

theorem FXType.constructorIndex_val_ofCell?_ofConstructorIndex_toCell
    (constructorIndex : Fin typeGeneratorCount) (payload : Nat) :
    Option.map (fun decodedType => decodedType.constructorIndex.val)
        (FXType.ofCell?
          (FXType.ofConstructorIndex constructorIndex payload).toCell) =
      some constructorIndex.val := by
  change
    Option.map (fun decodedType => decodedType.constructorIndex.val)
      (FXType.ofCellId?
        (PolyTerm.firstTypeCellId + constructorIndex.val) payload) =
      some constructorIndex.val
  unfold FXType.ofCellId?
  unfold classifyDimZeroCellId
  have hasNoTermRange :
      ¬PolyTerm.firstTypeCellId + constructorIndex.val <
        termGeneratorCount := by
    change
      ¬PolyTerm.firstTypeCellId + constructorIndex.val <
        PolyTerm.firstTypeCellId
    exact Nat.not_lt_of_ge (Nat.le_add_right _ _)
  have hasCurrentRange :
      PolyTerm.firstTypeCellId + constructorIndex.val <
        totalGeneratorCount := by
    change
      PolyTerm.firstTypeCellId + constructorIndex.val <
        PolyTerm.typeCellIdLimit
    exact Nat.add_lt_add_left constructorIndex.isLt
      PolyTerm.firstTypeCellId
  rw [dif_neg hasNoTermRange, dif_pos hasCurrentRange]
  change
    some
      ((PolyTerm.firstTypeCellId +
          ((PolyTerm.firstTypeCellId + constructorIndex.val) -
            PolyTerm.firstTypeCellId)) -
        PolyTerm.firstTypeCellId) =
      some constructorIndex.val
  rw [nat_add_sub_cancel_left_structural]
  rw [nat_add_sub_cancel_left_structural]

theorem FXType.constructorIndex_val_ofCell?_ofConstructorName_toCell
    (constructorName : FXTypeConstructorName) (payload : Nat) :
    Option.map (fun decodedType => decodedType.constructorIndex.val)
        (FXType.ofCell?
          (FXType.ofConstructorName constructorName payload).toCell) =
      some constructorName.localCellId := by
  rw [FXType.ofCell?_ofConstructorName_toCell]
  change
    some
      (FXType.ofConstructorName constructorName payload).constructorIndex.val =
        some constructorName.localCellId
  rw [FXType.constructorIndex_val_ofConstructorName]

theorem FXTerm.cellId_ofCell?_ofConstructorIndex_toCell
    (constructorIndex : Fin termGeneratorCount) (payload : Nat) :
    Option.map FXTerm.cellId
        (FXTerm.ofCell?
          (FXTerm.ofConstructorIndex constructorIndex payload).toCell) =
      some constructorIndex.val := by
  rw [FXTerm.ofCell?_ofConstructorIndex_toCell]
  rfl

theorem FXTerm.payload_ofCell?_ofConstructorIndex_toCell
    (constructorIndex : Fin termGeneratorCount) (payload : Nat) :
    Option.map FXTerm.payload
        (FXTerm.ofCell?
          (FXTerm.ofConstructorIndex constructorIndex payload).toCell) =
      some payload := by
  rw [FXTerm.ofCell?_ofConstructorIndex_toCell]
  rfl

theorem FXTerm.cellId_ofCell?_ofConstructorName_toCell
    (constructorName : FXTermConstructorName) (payload : Nat) :
    Option.map FXTerm.cellId
        (FXTerm.ofCell?
          (FXTerm.ofConstructorName constructorName payload).toCell) =
      some constructorName.cellId := by
  rw [FXTerm.ofCell?_ofConstructorName_toCell]
  rfl

theorem FXType.cellId_ofCell?_ofConstructorIndex_toCell
    (constructorIndex : Fin typeGeneratorCount) (payload : Nat) :
    Option.map FXType.cellId
        (FXType.ofCell?
          (FXType.ofConstructorIndex constructorIndex payload).toCell) =
      some (PolyTerm.firstTypeCellId + constructorIndex.val) := by
  change
    Option.map FXType.cellId
      (FXType.ofCellId?
        (PolyTerm.firstTypeCellId + constructorIndex.val) payload) =
      some (PolyTerm.firstTypeCellId + constructorIndex.val)
  unfold FXType.ofCellId?
  unfold classifyDimZeroCellId
  have hasNoTermRange :
      ¬PolyTerm.firstTypeCellId + constructorIndex.val <
        termGeneratorCount := by
    change
      ¬PolyTerm.firstTypeCellId + constructorIndex.val <
        PolyTerm.firstTypeCellId
    exact Nat.not_lt_of_ge (Nat.le_add_right _ _)
  have hasCurrentRange :
      PolyTerm.firstTypeCellId + constructorIndex.val <
        totalGeneratorCount := by
    change
      PolyTerm.firstTypeCellId + constructorIndex.val <
        PolyTerm.typeCellIdLimit
    exact Nat.add_lt_add_left constructorIndex.isLt
      PolyTerm.firstTypeCellId
  rw [dif_neg hasNoTermRange, dif_pos hasCurrentRange]
  change
    some
      (PolyTerm.firstTypeCellId +
        ((PolyTerm.firstTypeCellId + constructorIndex.val) -
          PolyTerm.firstTypeCellId)) =
      some (PolyTerm.firstTypeCellId + constructorIndex.val)
  rw [nat_add_sub_cancel_left_structural]

theorem FXType.payload_ofCell?_ofConstructorIndex_toCell
    (constructorIndex : Fin typeGeneratorCount) (payload : Nat) :
    Option.map FXType.payload
        (FXType.ofCell?
          (FXType.ofConstructorIndex constructorIndex payload).toCell) =
      some payload := by
  change
    Option.map FXType.payload
      (FXType.ofCellId?
        (PolyTerm.firstTypeCellId + constructorIndex.val) payload) =
      some payload
  unfold FXType.ofCellId?
  unfold classifyDimZeroCellId
  have hasNoTermRange :
      ¬PolyTerm.firstTypeCellId + constructorIndex.val <
        termGeneratorCount := by
    change
      ¬PolyTerm.firstTypeCellId + constructorIndex.val <
        PolyTerm.firstTypeCellId
    exact Nat.not_lt_of_ge (Nat.le_add_right _ _)
  have hasCurrentRange :
      PolyTerm.firstTypeCellId + constructorIndex.val <
        totalGeneratorCount := by
    change
      PolyTerm.firstTypeCellId + constructorIndex.val <
        PolyTerm.typeCellIdLimit
    exact Nat.add_lt_add_left constructorIndex.isLt
      PolyTerm.firstTypeCellId
  rw [dif_neg hasNoTermRange, dif_pos hasCurrentRange]
  rfl

theorem FXType.cellId_ofCell?_ofConstructorName_toCell
    (constructorName : FXTypeConstructorName) (payload : Nat) :
    Option.map FXType.cellId
        (FXType.ofCell?
          (FXType.ofConstructorName constructorName payload).toCell) =
      some constructorName.cellId := by
  rw [FXType.ofCell?_ofConstructorName_toCell]
  rfl

theorem FXTerm.constructorName?_ofCell?_ofConstructorName_toCell
    (constructorName : FXTermConstructorName) (payload : Nat) :
    (FXTerm.ofCell?
        (FXTerm.ofConstructorName constructorName payload).toCell).bind
        FXTerm.constructorName? =
      some constructorName := by
  rw [FXTerm.ofCell?_ofConstructorName_toCell]
  exact FXTerm.constructorName?_ofConstructorName constructorName payload

theorem FXTerm.payload?_ofCell?_ofConstructorName_toCell
    (constructorName : FXTermConstructorName) (payload : Nat) :
    Option.map FXTerm.payload
        (FXTerm.ofCell?
          (FXTerm.ofConstructorName constructorName payload).toCell) =
      some payload := by
  rw [FXTerm.ofCell?_ofConstructorName_toCell]
  change some (FXTerm.ofConstructorName constructorName payload).payload =
    some payload
  rw [FXTerm.payload_ofConstructorName]

theorem FXType.constructorName?_ofCell?_ofConstructorName_toCell
    (constructorName : FXTypeConstructorName) (payload : Nat) :
    (FXType.ofCell?
        (FXType.ofConstructorName constructorName payload).toCell).bind
        FXType.constructorName? =
      some constructorName := by
  rw [FXType.ofCell?_ofConstructorName_toCell]
  exact FXType.constructorName?_ofConstructorName constructorName payload

theorem FXType.payload?_ofCell?_ofConstructorName_toCell
    (constructorName : FXTypeConstructorName) (payload : Nat) :
    Option.map FXType.payload
        (FXType.ofCell?
          (FXType.ofConstructorName constructorName payload).toCell) =
      some payload := by
  rw [FXType.ofCell?_ofConstructorName_toCell]
  change some (FXType.ofConstructorName constructorName payload).payload =
    some payload
  rw [FXType.payload_ofConstructorName]

theorem FXTerm.toCell?_ofCell?_toCell (term : FXTerm) :
    Option.map FXTerm.toCell (FXTerm.ofCell? term.toCell) =
      some term.toCell := by
  cases term with
  | mk cell hRange =>
      cases cell with
      | atom cellId payload =>
          change
            Option.map FXTerm.toCell
              (FXTerm.ofCellId? cellId payload) =
                some (PolyTerm.atom cellId payload)
          unfold FXTerm.ofCellId?
          unfold classifyDimZeroCellId
          have hasTermRange : cellId < termGeneratorCount := by
            change cellId < PolyTerm.termCellIdLimit
            exact of_decide_eq_true hRange
          rw [dif_pos hasTermRange]
          rfl

theorem FXType.toCell?_ofCell?_toCell (typeCell : FXType) :
    Option.map FXType.toCell (FXType.ofCell? typeCell.toCell) =
      some typeCell.toCell := by
  cases typeCell with
  | mk cell hRange =>
      cases cell with
      | atom cellId payload =>
          change
            Option.map FXType.toCell
              (FXType.ofCellId? cellId payload) =
                some (PolyTerm.atom cellId payload)
          unfold FXType.ofCellId?
          unfold classifyDimZeroCellId
          change
            (decide (PolyTerm.firstTypeCellId ≤ cellId) &&
              decide (cellId < PolyTerm.typeCellIdLimit)) = true at hRange
          have hasLowerBoundDecide :
              decide (PolyTerm.firstTypeCellId ≤ cellId) = true := by
            cases hasLowerBool :
                decide (PolyTerm.firstTypeCellId ≤ cellId) with
            | false =>
                rw [hasLowerBool] at hRange
                cases hRange
            | true =>
                rfl
          have hasUpperBoundDecide :
              decide (cellId < PolyTerm.typeCellIdLimit) = true := by
            cases hasLowerBool :
                decide (PolyTerm.firstTypeCellId ≤ cellId) with
            | false =>
                rw [hasLowerBool] at hRange
                cases hRange
            | true =>
                cases hasUpperBool :
                    decide (cellId < PolyTerm.typeCellIdLimit) with
                | false =>
                    rw [hasLowerBool, hasUpperBool] at hRange
                    cases hRange
                | true =>
                    rfl
          have hasLowerBound : PolyTerm.firstTypeCellId ≤ cellId :=
            of_decide_eq_true hasLowerBoundDecide
          have hasCurrentRange : cellId < totalGeneratorCount := by
            change cellId < PolyTerm.typeCellIdLimit
            exact of_decide_eq_true hasUpperBoundDecide
          have hasNoTermRange : ¬cellId < termGeneratorCount := by
            change ¬cellId < PolyTerm.firstTypeCellId
            exact Nat.not_lt_of_ge hasLowerBound
          rw [dif_neg hasNoTermRange, dif_pos hasCurrentRange]
          change
            some
              ((PolyTerm.atom
                  (PolyTerm.firstTypeCellId +
                    (cellId - PolyTerm.firstTypeCellId))
                  payload :
                FXCellAt 0)) =
              some (PolyTerm.atom cellId payload)
          rw [nat_add_sub_cancel_of_le_structural hasLowerBound]

theorem FXTerm.cellId_ofCell?_toCell (term : FXTerm) :
    Option.map FXTerm.cellId (FXTerm.ofCell? term.toCell) =
      some term.cellId := by
  cases term with
  | mk cell hRange =>
      cases cell with
      | atom cellId payload =>
          change
            Option.map FXTerm.cellId
              (FXTerm.ofCellId? cellId payload) =
                some cellId
          unfold FXTerm.ofCellId?
          unfold classifyDimZeroCellId
          have hasTermRange : cellId < termGeneratorCount := by
            change cellId < PolyTerm.termCellIdLimit
            exact of_decide_eq_true hRange
          rw [dif_pos hasTermRange]
          rfl

theorem FXTerm.payload_ofCell?_toCell (term : FXTerm) :
    Option.map FXTerm.payload (FXTerm.ofCell? term.toCell) =
      some term.payload := by
  cases term with
  | mk cell hRange =>
      cases cell with
      | atom cellId payload =>
          change
            Option.map FXTerm.payload
              (FXTerm.ofCellId? cellId payload) =
                some payload
          unfold FXTerm.ofCellId?
          unfold classifyDimZeroCellId
          have hasTermRange : cellId < termGeneratorCount := by
            change cellId < PolyTerm.termCellIdLimit
            exact of_decide_eq_true hRange
          rw [dif_pos hasTermRange]
          rfl

theorem FXTerm.constructorIndex_val_ofCell?_toCell (term : FXTerm) :
    Option.map (fun decodedTerm => decodedTerm.constructorIndex.val)
        (FXTerm.ofCell? term.toCell) =
      some term.constructorIndex.val := by
  cases term with
  | mk cell hRange =>
      cases cell with
      | atom cellId payload =>
          change
            Option.map (fun decodedTerm => decodedTerm.constructorIndex.val)
              (FXTerm.ofCellId? cellId payload) =
                some cellId
          unfold FXTerm.ofCellId?
          unfold classifyDimZeroCellId
          have hasTermRange : cellId < termGeneratorCount := by
            change cellId < PolyTerm.termCellIdLimit
            exact of_decide_eq_true hRange
          rw [dif_pos hasTermRange]
          rfl

theorem FXType.cellId_ofCell?_toCell (typeCell : FXType) :
    Option.map FXType.cellId (FXType.ofCell? typeCell.toCell) =
      some typeCell.cellId := by
  cases typeCell with
  | mk cell hRange =>
      cases cell with
      | atom cellId payload =>
          change
            Option.map FXType.cellId
              (FXType.ofCellId? cellId payload) =
                some cellId
          unfold FXType.ofCellId?
          unfold classifyDimZeroCellId
          change
            (decide (PolyTerm.firstTypeCellId ≤ cellId) &&
              decide (cellId < PolyTerm.typeCellIdLimit)) = true at hRange
          have hasLowerBoundDecide :
              decide (PolyTerm.firstTypeCellId ≤ cellId) = true := by
            cases hasLowerBool :
                decide (PolyTerm.firstTypeCellId ≤ cellId) with
            | false =>
                rw [hasLowerBool] at hRange
                cases hRange
            | true =>
                rfl
          have hasUpperBoundDecide :
              decide (cellId < PolyTerm.typeCellIdLimit) = true := by
            cases hasLowerBool :
                decide (PolyTerm.firstTypeCellId ≤ cellId) with
            | false =>
                rw [hasLowerBool] at hRange
                cases hRange
            | true =>
                cases hasUpperBool :
                    decide (cellId < PolyTerm.typeCellIdLimit) with
                | false =>
                    rw [hasLowerBool, hasUpperBool] at hRange
                    cases hRange
                | true =>
                    rfl
          have hasLowerBound : PolyTerm.firstTypeCellId ≤ cellId :=
            of_decide_eq_true hasLowerBoundDecide
          have hasCurrentRange : cellId < totalGeneratorCount := by
            change cellId < PolyTerm.typeCellIdLimit
            exact of_decide_eq_true hasUpperBoundDecide
          have hasNoTermRange : ¬cellId < termGeneratorCount := by
            change ¬cellId < PolyTerm.firstTypeCellId
            exact Nat.not_lt_of_ge hasLowerBound
          rw [dif_neg hasNoTermRange, dif_pos hasCurrentRange]
          change
            some
              (PolyTerm.firstTypeCellId +
                (cellId - PolyTerm.firstTypeCellId)) =
              some cellId
          rw [nat_add_sub_cancel_of_le_structural hasLowerBound]

theorem FXType.payload_ofCell?_toCell (typeCell : FXType) :
    Option.map FXType.payload (FXType.ofCell? typeCell.toCell) =
      some typeCell.payload := by
  cases typeCell with
  | mk cell hRange =>
      cases cell with
      | atom cellId payload =>
          change
            Option.map FXType.payload
              (FXType.ofCellId? cellId payload) =
                some payload
          unfold FXType.ofCellId?
          unfold classifyDimZeroCellId
          change
            (decide (PolyTerm.firstTypeCellId ≤ cellId) &&
              decide (cellId < PolyTerm.typeCellIdLimit)) = true at hRange
          have hasLowerBoundDecide :
              decide (PolyTerm.firstTypeCellId ≤ cellId) = true := by
            cases hasLowerBool :
                decide (PolyTerm.firstTypeCellId ≤ cellId) with
            | false =>
                rw [hasLowerBool] at hRange
                cases hRange
            | true =>
                rfl
          have hasUpperBoundDecide :
              decide (cellId < PolyTerm.typeCellIdLimit) = true := by
            cases hasLowerBool :
                decide (PolyTerm.firstTypeCellId ≤ cellId) with
            | false =>
                rw [hasLowerBool] at hRange
                cases hRange
            | true =>
                cases hasUpperBool :
                    decide (cellId < PolyTerm.typeCellIdLimit) with
                | false =>
                    rw [hasLowerBool, hasUpperBool] at hRange
                    cases hRange
                | true =>
                    rfl
          have hasLowerBound : PolyTerm.firstTypeCellId ≤ cellId :=
            of_decide_eq_true hasLowerBoundDecide
          have hasCurrentRange : cellId < totalGeneratorCount := by
            change cellId < PolyTerm.typeCellIdLimit
            exact of_decide_eq_true hasUpperBoundDecide
          have hasNoTermRange : ¬cellId < termGeneratorCount := by
            change ¬cellId < PolyTerm.firstTypeCellId
            exact Nat.not_lt_of_ge hasLowerBound
          rw [dif_neg hasNoTermRange, dif_pos hasCurrentRange]
          rfl

theorem FXType.constructorIndex_val_ofCell?_toCell (typeCell : FXType) :
    Option.map (fun decodedType => decodedType.constructorIndex.val)
        (FXType.ofCell? typeCell.toCell) =
      some typeCell.constructorIndex.val := by
  cases typeCell with
  | mk cell hRange =>
      cases cell with
      | atom cellId payload =>
          change
            Option.map (fun decodedType => decodedType.constructorIndex.val)
              (FXType.ofCellId? cellId payload) =
                some (cellId - PolyTerm.firstTypeCellId)
          unfold FXType.ofCellId?
          unfold classifyDimZeroCellId
          change
            (decide (PolyTerm.firstTypeCellId ≤ cellId) &&
              decide (cellId < PolyTerm.typeCellIdLimit)) = true at hRange
          have hasLowerBoundDecide :
              decide (PolyTerm.firstTypeCellId ≤ cellId) = true := by
            cases hasLowerBool :
                decide (PolyTerm.firstTypeCellId ≤ cellId) with
            | false =>
                rw [hasLowerBool] at hRange
                cases hRange
            | true =>
                rfl
          have hasUpperBoundDecide :
              decide (cellId < PolyTerm.typeCellIdLimit) = true := by
            cases hasLowerBool :
                decide (PolyTerm.firstTypeCellId ≤ cellId) with
            | false =>
                rw [hasLowerBool] at hRange
                cases hRange
            | true =>
                cases hasUpperBool :
                    decide (cellId < PolyTerm.typeCellIdLimit) with
                | false =>
                    rw [hasLowerBool, hasUpperBool] at hRange
                    cases hRange
                | true =>
                    rfl
          have hasLowerBound : PolyTerm.firstTypeCellId ≤ cellId :=
            of_decide_eq_true hasLowerBoundDecide
          have hasCurrentRange : cellId < totalGeneratorCount := by
            change cellId < PolyTerm.typeCellIdLimit
            exact of_decide_eq_true hasUpperBoundDecide
          have hasNoTermRange : ¬cellId < termGeneratorCount := by
            change ¬cellId < PolyTerm.firstTypeCellId
            exact Nat.not_lt_of_ge hasLowerBound
          rw [dif_neg hasNoTermRange, dif_pos hasCurrentRange]
          change
            some
              ((PolyTerm.firstTypeCellId +
                  (cellId - PolyTerm.firstTypeCellId)) -
                PolyTerm.firstTypeCellId) =
              some (cellId - PolyTerm.firstTypeCellId)
          rw [nat_add_sub_cancel_left_structural]

theorem FXTerm.ofCell?_ofType_toCell (typeCell : FXType) :
    FXTerm.ofCell? typeCell.toCell = none := by
  cases typeCell with
  | mk cell hRange =>
      cases cell with
      | atom cellId payload =>
          change FXTerm.ofCellId? cellId payload = none
          unfold FXTerm.ofCellId?
          unfold classifyDimZeroCellId
          change
            (decide (PolyTerm.firstTypeCellId ≤ cellId) &&
              decide (cellId < PolyTerm.typeCellIdLimit)) = true at hRange
          have hasLowerBoundDecide :
              decide (PolyTerm.firstTypeCellId ≤ cellId) = true := by
            cases hasLowerBool :
                decide (PolyTerm.firstTypeCellId ≤ cellId) with
            | false =>
                rw [hasLowerBool] at hRange
                cases hRange
            | true =>
                rfl
          have hasUpperBoundDecide :
              decide (cellId < PolyTerm.typeCellIdLimit) = true := by
            cases hasLowerBool :
                decide (PolyTerm.firstTypeCellId ≤ cellId) with
            | false =>
                rw [hasLowerBool] at hRange
                cases hRange
            | true =>
                cases hasUpperBool :
                    decide (cellId < PolyTerm.typeCellIdLimit) with
                | false =>
                    rw [hasLowerBool, hasUpperBool] at hRange
                    cases hRange
                | true =>
                    rfl
          have hasLowerBound : PolyTerm.firstTypeCellId ≤ cellId :=
            of_decide_eq_true hasLowerBoundDecide
          have hasCurrentRange : cellId < totalGeneratorCount := by
            change cellId < PolyTerm.typeCellIdLimit
            exact of_decide_eq_true hasUpperBoundDecide
          have hasNoTermRange : ¬cellId < termGeneratorCount := by
            change ¬cellId < PolyTerm.firstTypeCellId
            exact Nat.not_lt_of_ge hasLowerBound
          rw [dif_neg hasNoTermRange, dif_pos hasCurrentRange]

theorem FXType.ofCell?_ofTerm_toCell (term : FXTerm) :
    FXType.ofCell? term.toCell = none := by
  cases term with
  | mk cell hRange =>
      cases cell with
      | atom cellId payload =>
          change FXType.ofCellId? cellId payload = none
          unfold FXType.ofCellId?
          unfold classifyDimZeroCellId
          have hasTermRange : cellId < termGeneratorCount := by
            change cellId < PolyTerm.termCellIdLimit
            exact of_decide_eq_true hRange
          rw [dif_pos hasTermRange]

theorem FXTerm.ofCell?_ofOutsideCurrentGeneratorRange
    (cellId : CellId) (payload : Nat)
    (hasOutsideRange : totalGeneratorCount ≤ cellId) :
    FXTerm.ofCell?
        (PolyTerm.atom (profile := fxProfile) cellId payload :
          FXCellAt 0) =
      none := by
  change FXTerm.ofCellId? cellId payload = none
  exact FXTerm.ofCellId?_ofOutsideCurrentGeneratorRange
    cellId payload hasOutsideRange

theorem FXType.ofCell?_ofOutsideCurrentGeneratorRange
    (cellId : CellId) (payload : Nat)
    (hasOutsideRange : totalGeneratorCount ≤ cellId) :
    FXType.ofCell?
        (PolyTerm.atom (profile := fxProfile) cellId payload :
          FXCellAt 0) =
      none := by
  change FXType.ofCellId? cellId payload = none
  exact FXType.ofCellId?_ofOutsideCurrentGeneratorRange
    cellId payload hasOutsideRange

end LeanFX2.Foundation.PolyCell.FXProfile
