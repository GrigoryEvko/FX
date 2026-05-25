import LeanFX2.Foundation._deprecated_polygraph.ParallelPair

/-! # Dimension measure + descent lemmas for `PolyCell`.

Every `PolyCell dim sv tv` carries `dim` as a Nat index.  This file
ships the projection of that index as a measure, plus the lemmas that
say the per-stratum source/target projections strictly decrease the
measure.  These together let downstream constructions (vertical
composition, free n-category, strategy 3-cells) recurse over cell
structure via well-founded recursion on `dim`.

`DecidableEq` for `PolyCell` is hand-rolled in `DecEq.lean`; auto-
derivation leaks `propext` through the partial-match equation lemmas
for the over-constrained per-ctor index shape.
-/

namespace LeanFX2.Foundation._deprecated_polygraph

/-- The dimension of a cell, exposed as a `Nat` measure. -/
def dimensionMeasure {dim sourceVtx targetVtx : Nat}
    (_someCell : PolyCell dim sourceVtx targetVtx) : Nat := dim

theorem cellSource_dimensionMeasure_lt {dim sourceVtx targetVtx : Nat}
    (highCell : PolyCell (dim + 2) sourceVtx targetVtx) :
    dimensionMeasure (cellSource highCell) < dimensionMeasure highCell :=
  Nat.lt_succ_self (dim + 1)

theorem cellTarget_dimensionMeasure_lt {dim sourceVtx targetVtx : Nat}
    (highCell : PolyCell (dim + 2) sourceVtx targetVtx) :
    dimensionMeasure (cellTarget highCell) < dimensionMeasure highCell :=
  Nat.lt_succ_self (dim + 1)

theorem arrowSource_dimensionMeasure_lt {sourceVtx targetVtx : Nat}
    (arrowCell : PolyCell 1 sourceVtx targetVtx) :
    dimensionMeasure (arrowSource arrowCell) < dimensionMeasure arrowCell :=
  Nat.lt_succ_self 0

theorem arrowTarget_dimensionMeasure_lt {sourceVtx targetVtx : Nat}
    (arrowCell : PolyCell 1 sourceVtx targetVtx) :
    dimensionMeasure (arrowTarget arrowCell) < dimensionMeasure arrowCell :=
  Nat.lt_succ_self 0

end LeanFX2.Foundation._deprecated_polygraph
