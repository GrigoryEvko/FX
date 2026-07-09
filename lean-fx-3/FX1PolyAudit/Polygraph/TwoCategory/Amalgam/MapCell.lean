import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.MapCell

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.MapCell — zero-axiom gate for the free 2-cell functor
(WP-AMALG r4, residual A)

Per-declaration zero-axiom gate for: the induced 1-cell functor (`mapModality` / `mapPath` /
`mapPath_identityPath` / `mapPath_composePath`), the sanctioned interface extension `ComputadMorphismTwo`, the
free 2-cell functor `mapCellAlong` and its cast-commutation `mapCellAlong_castBoundary`, and the two locally-thin
coprojection lifts (`inclusionLeftTwo` / `inclusionRightTwo`).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.mapModality
#assert_no_axioms FX1Poly.Polygraph.Amalgam.mapPath
#assert_no_axioms FX1Poly.Polygraph.Amalgam.mapPath_identityPath
#assert_no_axioms FX1Poly.Polygraph.Amalgam.mapPath_composePath
#assert_no_axioms FX1Poly.Polygraph.Amalgam.mapCellAlong
#assert_no_axioms FX1Poly.Polygraph.Amalgam.mapCellAlong_castBoundary
#assert_no_axioms FX1Poly.Polygraph.Amalgam.inclusionLeftTwo
#assert_no_axioms FX1Poly.Polygraph.Amalgam.inclusionRightTwo
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasMapCellAlong
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasRealGeneratorCoprojection

end FX1PolyAudit
