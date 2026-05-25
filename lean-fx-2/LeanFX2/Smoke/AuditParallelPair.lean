import LeanFX2.Foundation._deprecated_polygraph.ParallelPair

namespace LeanFX2.Smoke

open LeanFX2.Foundation._deprecated_polygraph

-- Witness construction for `ParallelPair` over two atoms at the
-- same vertex.
def parallelPair11_atomPair_smoke :
    ParallelPair (PolyCell.atom 0) (PolyCell.atom 0) :=
  ParallelPair.introWitness (PolyCell.atom 0) (PolyCell.atom 0)

-- Witness construction for `ParallelPair` over two arrows sharing the
-- same boundary (0, 1).
def parallelPair11_arrowPair_smoke :
    ParallelPair
      (PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 7)
      (PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 8) :=
  ParallelPair.introWitness
    (PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 7)
    (PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 8)

-- Projection smokes.
def atomVertex_smoke : Nat :=
  atomVertex (PolyCell.atom 42)

def arrowSource_smoke : PolyCell 0 0 0 :=
  arrowSource (PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 7)

def arrowTarget_smoke : PolyCell 0 1 1 :=
  arrowTarget (PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 7)

def cellSource_smoke : PolyCell 1 0 1 :=
  cellSource
    (PolyCell.cell
      (PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 7)
      (PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 8)
      42)

def cellTarget_smoke : PolyCell 1 0 1 :=
  cellTarget
    (PolyCell.cell
      (PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 7)
      (PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 8)
      42)

def cellIdx_atom_smoke : Nat :=
  cellIdx (PolyCell.atom 42)

def cellIdx_arrow_smoke : Nat :=
  cellIdx (PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 7)

def cellIdx_cell_smoke : Nat :=
  cellIdx
    (PolyCell.cell
      (PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 7)
      (PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 8)
      42)

end LeanFX2.Smoke

#print axioms LeanFX2.Smoke.parallelPair11_atomPair_smoke
#print axioms LeanFX2.Smoke.parallelPair11_arrowPair_smoke
#print axioms LeanFX2.Smoke.atomVertex_smoke
#print axioms LeanFX2.Smoke.arrowSource_smoke
#print axioms LeanFX2.Smoke.arrowTarget_smoke
#print axioms LeanFX2.Smoke.cellSource_smoke
#print axioms LeanFX2.Smoke.cellTarget_smoke
#print axioms LeanFX2.Smoke.cellIdx_atom_smoke
#print axioms LeanFX2.Smoke.cellIdx_arrow_smoke
#print axioms LeanFX2.Smoke.cellIdx_cell_smoke
