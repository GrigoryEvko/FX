import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWallBlockScaffold

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutWallBlockScaffold — zero-axiom gate for the wall-block
read-off and the machine-checked refutation of dom-to-cod wall-block conservation (WP-AMALG-2 r8, B1)

Per-declaration zero-axiom gate for the boundary-word read-off, the wall-splitting witness cell and its
boundaries, the two `rfl` wall-block computations, the block-list-length refutation, the count-still-preserved
witness, and the honesty marker.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutPathWord
#assert_no_axioms FX1Poly.Polygraph.Amalgam.unitSplitsWallDom
#assert_no_axioms FX1Poly.Polygraph.Amalgam.unitSplitsWallCod
#assert_no_axioms FX1Poly.Polygraph.Amalgam.unitSplitsWallCell
#assert_no_axioms FX1Poly.Polygraph.Amalgam.unitSplitsWall_dom_wallBlocks
#assert_no_axioms FX1Poly.Polygraph.Amalgam.unitSplitsWall_cod_wallBlocks
#assert_no_axioms FX1Poly.Polygraph.Amalgam.unitSplitsWall_wallBlockCount_domCod_differ
#assert_no_axioms FX1Poly.Polygraph.Amalgam.unitSplitsWall_wallCount_preserved
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_wallBlockListNotDomCodInvariant

end FX1PolyAudit
