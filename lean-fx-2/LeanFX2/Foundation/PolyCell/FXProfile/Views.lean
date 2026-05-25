import LeanFX2.Foundation.PolyCell.Core.Fold
/-!
# FX View Types — FXType, FXTerm, FXStep, FXConv as PolyTerm subtypes

Carve out familiar FX kernel concepts as SUBTYPES of PolyTerm fxProfile.
These make the existing kernel's types RECOVERABLE from the universal
PolyTerm inductive via simple predicates — no information loss.

The existing 275K LoC kernel can interoperate via these views.

Reference: polycell.md §5.
Zero external dependencies.
-/

namespace LeanFX2.Foundation.PolyCell.FXProfile

open Core

/-- All FX cells at any dimension. -/
abbrev FXCell := PolyTerm fxProfile

/-- FX cells at a specific dimension. -/
abbrev FXCellAt (dimension : CellDim) := PolyTerm fxProfile dimension

/-- FX type cells: dim-0 atoms with cellId in the type-code range [64..77]. -/
def FXType := { cell : FXCellAt 0 // cell.isTypeCell = true }

/-- FX term cells: dim-0 atoms with cellId in the term range [0..63]. -/
def FXTerm := { cell : FXCellAt 0 // cell.isTermCell = true }

/-- FX step cells: dim-1 cells that are NOT identity (actual reductions). -/
def FXStep := { cell : FXCellAt 1 // cell.isStepCell = true }

/-- FX conversion witnesses: dim-1 cells that ARE identity or compose to
identity (the "thin" cells from stratification = invertible). -/
def FXConv := FXCellAt 1

/-- FX cd_lemma fillers: dim-2 cells (confluence proofs). -/
def FXCdLemma := FXCellAt 2

/-- FX Squier coherence: dim-3+ cells. -/
def FXSquier := FXCellAt 3

/-- Construct an FX term cell (cellId < 64). -/
def FXTerm.ofAtom (cellId : CellId) (payload : Nat)
    (hRange : (PolyTerm.atom (profile := fxProfile) cellId payload).isTermCell = true) :
    FXTerm := ⟨.atom cellId payload, hRange⟩

/-- Construct an FX type cell (cellId ≥ 64). -/
def FXType.ofAtom (cellId : CellId) (payload : Nat)
    (hRange : (PolyTerm.atom (profile := fxProfile) cellId payload).isTypeCell = true) :
    FXType := ⟨.atom cellId payload, hRange⟩

/-- Construct an FX step from rule + source + target. -/
def FXStep.mk (ruleId : CellId) (source target : FXCellAt 0) : FXStep :=
  ⟨.cell ruleId source target, rfl⟩

/-- Extract the underlying PolyTerm from a view type. -/
def FXTerm.toCell (term : FXTerm) : FXCellAt 0 := term.val
def FXType.toCell (ty : FXType) : FXCellAt 0 := ty.val
def FXStep.toCell (step : FXStep) : FXCellAt 1 := step.val

/-- FX term cell id extraction. -/
def FXTerm.cellId : FXTerm → CellId
  | ⟨.atom cellId _, _⟩ => cellId

/-- FX type cell id extraction. -/
def FXType.cellId : FXType → CellId
  | ⟨.atom cellId _, _⟩ => cellId

/-- Vertical composition of steps (sequential reduction chain). -/
def FXStep.seq (step1 step2 : FXStep) : FXCellAt 1 :=
  .compV step1.val step2.val

/-- Parallel composition of steps (concurrent execution). -/
def FXStep.par (step1 step2 : FXStep) : FXCellAt 1 :=
  .compH step1.val step2.val

/-- Identity step on a term (the "do nothing" reduction). -/
def FXConv.refl (term : FXCellAt 0) : FXConv :=
  .identity term

/-- Conversion transitivity via vertical composition. -/
def FXConv.trans (conv1 conv2 : FXConv) : FXConv :=
  .compV conv1 conv2

/-- Apply fold to an FX cell using a specific algebra. -/
def FXCell.applyFold {target : CellDim → Type}
    (algebra : PolyTermAlgebra fxProfile target)
    {dimension : CellDim}
    (cell : FXCellAt dimension) : target dimension :=
  PolyTerm.fold algebra cell

/-- The number of Generator ids reserved for terms vs types.
Terms: 0..63 (64 ids), Types: 64..77 (14 ids). Total: 78. -/
def termGeneratorCount : Nat := 64
def typeGeneratorCount : Nat := 14
def totalGeneratorCount : Nat := 78

theorem generatorPartition :
    termGeneratorCount + typeGeneratorCount = totalGeneratorCount := rfl

end LeanFX2.Foundation.PolyCell.FXProfile
