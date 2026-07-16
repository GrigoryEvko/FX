import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingDouble.DoubleTileDimension

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingDouble.DoubleTileDimension — zero-axiom gate (the (width, height) SOUNDNESS + non-vacuity + markers)

Per-declaration zero-axiom gate for the walking-square double-category tile invariant: the sample-tile fold
smokes, the two SOUNDNESS theorems `tileWidth_congr_of_conv` / `tileHeight_congr_of_conv`, the non-vacuity
witnesses (guarded laws fire positively; non-convertible pairs separate by width, by height, and by both), and
the markers.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.tileWidth_gridInterchangeLeft
#assert_no_axioms FX1Poly.Polygraph.tileWidth_gridInterchangeRight
#assert_no_axioms FX1Poly.Polygraph.tileHeight_gridInterchangeLeft
#assert_no_axioms FX1Poly.Polygraph.tileHeight_gridInterchangeRight
#assert_no_axioms FX1Poly.Polygraph.tileWidth_hAssocLeft
#assert_no_axioms FX1Poly.Polygraph.tileHeight_vAssocLeft
#assert_no_axioms FX1Poly.Polygraph.tileWidth_congr_of_conv
#assert_no_axioms FX1Poly.Polygraph.tileHeight_congr_of_conv
#assert_no_axioms FX1Poly.Polygraph.doubleConv_gridInterchange
#assert_no_axioms FX1Poly.Polygraph.tileWidth_hUnitLeftTile_eq_square_via_soundness
#assert_no_axioms FX1Poly.Polygraph.tileHeight_vUnitLeftTile_eq_square_via_soundness
#assert_no_axioms FX1Poly.Polygraph.doubleNotConv_square_hcompSquareSquare
#assert_no_axioms FX1Poly.Polygraph.doubleNotConv_square_vcompSquareSquare
#assert_no_axioms FX1Poly.Polygraph.doubleNotConv_hcompSquareSquare_vcompSquareSquare
#assert_no_axioms FX1Poly.Polygraph.fxDouble_hasSignatureAndTileInvariant
#assert_no_axioms FX1Poly.Polygraph.fxDouble_hasSignatureAndTileSoundness
#assert_no_axioms FX1Poly.Polygraph.fxDouble_hasWordProblemDecided

end FX1PolyAudit
