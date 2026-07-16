import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingDouble.DoubleTileSeed

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingDouble.DoubleTileSeed — zero-axiom gate (the walking-square double-category signature, the (width, height) folds, and the tile-pasting relation)

Per-declaration zero-axiom gate for the walking-square double-category seed: the `DoubleTile` carrier, the
`DoubleGenerator` generators + their `generatorDimension`, the `WalkingSquareSignature` orientation record +
`walkingSquareSignature` and its smokes, the `tileWidth` / `tileHeight` invariant folds + their definitional
smokes, the concrete sample tiles, and the tile-pasting `DoubleTileConv` convertibility with its interchange /
associativity / guarded-unit / whiskered witnesses.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.DoubleTile
#assert_no_axioms FX1Poly.Polygraph.DoubleGenerator
#assert_no_axioms FX1Poly.Polygraph.generatorDimension
#assert_no_axioms FX1Poly.Polygraph.generatorDimension_hGen
#assert_no_axioms FX1Poly.Polygraph.generatorDimension_vGen
#assert_no_axioms FX1Poly.Polygraph.generatorDimension_alpha
#assert_no_axioms FX1Poly.Polygraph.WalkingSquareSignature
#assert_no_axioms FX1Poly.Polygraph.walkingSquareSignature
#assert_no_axioms FX1Poly.Polygraph.walkingSquareSignature_topBoundaryWidth
#assert_no_axioms FX1Poly.Polygraph.walkingSquareSignature_leftBoundaryHeight
#assert_no_axioms FX1Poly.Polygraph.walkingSquareSignature_horizontalEndo
#assert_no_axioms FX1Poly.Polygraph.walkingSquareSignature_verticalEndo
#assert_no_axioms FX1Poly.Polygraph.tileWidth
#assert_no_axioms FX1Poly.Polygraph.tileHeight
#assert_no_axioms FX1Poly.Polygraph.tileWidth_square
#assert_no_axioms FX1Poly.Polygraph.tileWidth_hUnit
#assert_no_axioms FX1Poly.Polygraph.tileWidth_vUnit
#assert_no_axioms FX1Poly.Polygraph.tileWidth_hcomp
#assert_no_axioms FX1Poly.Polygraph.tileWidth_vcomp
#assert_no_axioms FX1Poly.Polygraph.tileHeight_square
#assert_no_axioms FX1Poly.Polygraph.tileHeight_hUnit
#assert_no_axioms FX1Poly.Polygraph.tileHeight_vUnit
#assert_no_axioms FX1Poly.Polygraph.tileHeight_hcomp
#assert_no_axioms FX1Poly.Polygraph.tileHeight_vcomp
#assert_no_axioms FX1Poly.Polygraph.doubleGridInterchangeLeft
#assert_no_axioms FX1Poly.Polygraph.doubleGridInterchangeRight
#assert_no_axioms FX1Poly.Polygraph.doubleHAssocLeft
#assert_no_axioms FX1Poly.Polygraph.doubleHAssocRight
#assert_no_axioms FX1Poly.Polygraph.doubleVAssocLeft
#assert_no_axioms FX1Poly.Polygraph.doubleVAssocRight
#assert_no_axioms FX1Poly.Polygraph.doubleHUnitLeftTile
#assert_no_axioms FX1Poly.Polygraph.doubleVUnitLeftTile
#assert_no_axioms FX1Poly.Polygraph.DoubleTileConv
#assert_no_axioms FX1Poly.Polygraph.doubleGridInterchangeHolds
#assert_no_axioms FX1Poly.Polygraph.doubleHAssocHolds
#assert_no_axioms FX1Poly.Polygraph.doubleVAssocHolds
#assert_no_axioms FX1Poly.Polygraph.doubleHUnitLeftHolds
#assert_no_axioms FX1Poly.Polygraph.doubleVUnitLeftHolds
#assert_no_axioms FX1Poly.Polygraph.doubleHUnitLeftWhiskeredHolds

end FX1PolyAudit
