import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWallCountInvariance

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutWallCountInvariance — zero-axiom gate for the wall-count
invariant (WP-AMALG-2 r6, B1)

Per-declaration zero-axiom gate for the wall bit / word / path wall counts, the composePath homomorphism, the
straddle lemma (right-coprojected 1-cells are wall-free), the reconstructed generators' wall-free stored words, the
interpreter wall-count invariant, the dom-to-cod wall-count invariance theorem, the law-row straddle test, the
conversion corollary, and the honesty marker.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.wallBitCount
#assert_no_axioms FX1Poly.Polygraph.Amalgam.wordWallCount
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutPathWallCount
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutPathWallCount_composePath
#assert_no_axioms FX1Poly.Polygraph.Amalgam.mapPath_inclusionRight_wallFree
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutTwoGen_words_wallFree
#assert_no_axioms FX1Poly.Polygraph.Amalgam.interpretWordFrom_wallCount
#assert_no_axioms FX1Poly.Polygraph.Amalgam.wallLetterCount_dom_eq_cod
#assert_no_axioms FX1Poly.Polygraph.Amalgam.noGeneratorStraddlesWall
#assert_no_axioms FX1Poly.Polygraph.Amalgam.saturatedConv_boundary_wallCount_eq
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasWallCountInvariance

end FX1PolyAudit
