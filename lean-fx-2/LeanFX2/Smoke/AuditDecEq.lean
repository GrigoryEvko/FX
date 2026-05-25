import LeanFX2.Foundation._deprecated_polygraph.DecEq

namespace LeanFX2.Smoke

open LeanFX2.Foundation._deprecated_polygraph

/-! Two-atom equality at dim 0: forced isTrue by atom uniqueness. -/
def atomEq_smoke : Decidable (PolyCell.atom 5 = PolyCell.atom 5) :=
  decEqPolyCell _ _

/-! Two-arrow equality at dim 1: same idx → isTrue. -/
def arrowEq_same_smoke :
    Decidable (PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 7
             = PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 7) :=
  decEqPolyCell _ _

/-! Two-arrow inequality at dim 1: differing idx → isFalse. -/
def arrowEq_differingIdx_smoke :
    Decidable (PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 7
             = PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 9) :=
  decEqPolyCell _ _

/-! Two-cell equality at dim 2: structurally identical → isTrue. -/
def cellEq_same_smoke :
    Decidable
      (PolyCell.cell
        (PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 7)
        (PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 8) 42
      = PolyCell.cell
        (PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 7)
        (PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 8) 42) :=
  decEqPolyCell _ _

/-! Two-cell inequality at dim 2: differing sub-source idx → isFalse. -/
def cellEq_differingSubSource_smoke :
    Decidable
      (PolyCell.cell
        (PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 7)
        (PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 8) 42
      = PolyCell.cell
        (PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 99)
        (PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 8) 42) :=
  decEqPolyCell _ _

end LeanFX2.Smoke

#print axioms LeanFX2.Foundation._deprecated_polygraph.PolyCell.atom_unique_at_dim0
#print axioms LeanFX2.Foundation._deprecated_polygraph.PolyCell.arrow_unique_at_dim1
#print axioms LeanFX2.Foundation._deprecated_polygraph.PolyCell.cell_decompose_at_dimSucc
#print axioms LeanFX2.Foundation._deprecated_polygraph.decEqAtDim0
#print axioms LeanFX2.Foundation._deprecated_polygraph.decEqAtDim1
#print axioms LeanFX2.Foundation._deprecated_polygraph.decEqAtDimSucc
#print axioms LeanFX2.Foundation._deprecated_polygraph.polyCellDecEqAt
#print axioms LeanFX2.Foundation._deprecated_polygraph.decEqPolyCell
#print axioms LeanFX2.Smoke.atomEq_smoke
#print axioms LeanFX2.Smoke.arrowEq_same_smoke
#print axioms LeanFX2.Smoke.arrowEq_differingIdx_smoke
#print axioms LeanFX2.Smoke.cellEq_same_smoke
#print axioms LeanFX2.Smoke.cellEq_differingSubSource_smoke
