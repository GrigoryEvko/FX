import LeanFX2.Foundation._deprecated_polygraph.StepLabel

namespace LeanFX2.Smoke

open LeanFX2.Foundation._deprecated_polygraph

/-! K11.14 Phase A — `StepLabel` inductive + index + dim-1 cell
embedding.  Each `#print axioms` below must report "does not depend on
any axioms"; the 110 labels collectively cover every `Step` ctor in
`Reduction/Step.lean`.

The single-sorted polygraph reading means every label maps to a
`PolyCell.arrow` at the trivial dim-0 vertex `0` with `idx` recording
the label's source-order index (0..109).  K11.15 ships the inverse
extraction; K11.16 ships the per-ctor `rfl` equivalence theorems. -/

/-- Smoke witness — first label (`appLeft`, index 0). -/
def stepLabelAppLeft_smoke : StepLabel := StepLabel.appLeft

/-- Smoke witness — last label (`eqArrowHet`, index 109). -/
def stepLabelEqArrowHet_smoke : StepLabel := StepLabel.eqArrowHet

/-- Index of the first label. -/
def stepLabelIndexFirst_smoke : Nat := StepLabel.appLeft.index

/-- Index of the last label. -/
def stepLabelIndexLast_smoke : Nat := StepLabel.eqArrowHet.index

/-- Dim-1 cell of the first label. -/
def stepLabelCellFirst_smoke : PolyCell 1 0 0 :=
  StepLabel.appLeft.toDim1Cell

/-- Dim-1 cell of a middle label (`betaApp`). -/
def stepLabelCellMid_smoke : PolyCell 1 0 0 :=
  StepLabel.betaApp.toDim1Cell

/-- Index equality on the first ctor (sanity at `rfl`). -/
example : StepLabel.appLeft.index = 0 := rfl

/-- Index equality on the last ctor (sanity at `rfl`). -/
example : StepLabel.eqArrowHet.index = 109 := rfl

/-- Dim-1 cell equality on a representative ctor (sanity at `rfl`). -/
example : StepLabel.betaApp.toDim1Cell
        = PolyCell.arrow (.atom 0) (.atom 0) 9 := rfl

#print axioms StepLabel
#print axioms StepLabel.index
#print axioms StepLabel.toDim1Cell
#print axioms stepLabelAppLeft_smoke
#print axioms stepLabelEqArrowHet_smoke
#print axioms stepLabelIndexFirst_smoke
#print axioms stepLabelIndexLast_smoke
#print axioms stepLabelCellFirst_smoke
#print axioms stepLabelCellMid_smoke

end LeanFX2.Smoke
