import LeanFX2.Foundation.Polygraph.Wellfounded

namespace LeanFX2.Smoke

open LeanFX2.Foundation.Polygraph

def dimensionMeasure_atom_smoke : Nat :=
  dimensionMeasure (PolyCell.atom 7)

def dimensionMeasure_arrow_smoke : Nat :=
  dimensionMeasure (PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 4)

def dimensionMeasure_cell_smoke : Nat :=
  dimensionMeasure
    (PolyCell.cell
      (PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 7)
      (PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 8)
      42)

theorem arrowSource_lt_smoke :
    dimensionMeasure (arrowSource
        (PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 7))
      < dimensionMeasure
        (PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 7) :=
  arrowSource_dimensionMeasure_lt _

theorem arrowTarget_lt_smoke :
    dimensionMeasure (arrowTarget
        (PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 7))
      < dimensionMeasure
        (PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 7) :=
  arrowTarget_dimensionMeasure_lt _

theorem cellSource_lt_smoke :
    dimensionMeasure (cellSource
        (PolyCell.cell
          (PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 7)
          (PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 8)
          42))
      < dimensionMeasure
        (PolyCell.cell
          (PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 7)
          (PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 8)
          42) :=
  cellSource_dimensionMeasure_lt _

theorem cellTarget_lt_smoke :
    dimensionMeasure (cellTarget
        (PolyCell.cell
          (PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 7)
          (PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 8)
          42))
      < dimensionMeasure
        (PolyCell.cell
          (PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 7)
          (PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 8)
          42) :=
  cellTarget_dimensionMeasure_lt _

end LeanFX2.Smoke

#print axioms LeanFX2.Smoke.dimensionMeasure_atom_smoke
#print axioms LeanFX2.Smoke.dimensionMeasure_arrow_smoke
#print axioms LeanFX2.Smoke.dimensionMeasure_cell_smoke
#print axioms LeanFX2.Smoke.arrowSource_lt_smoke
#print axioms LeanFX2.Smoke.arrowTarget_lt_smoke
#print axioms LeanFX2.Smoke.cellSource_lt_smoke
#print axioms LeanFX2.Smoke.cellTarget_lt_smoke
