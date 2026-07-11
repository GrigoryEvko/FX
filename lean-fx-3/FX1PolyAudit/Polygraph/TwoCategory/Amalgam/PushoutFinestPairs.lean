import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFinestPairs

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutFinestPairs — zero-axiom gate for the cell-carrying finest
layout `finestLayout` and its domain round-trip (WP-AMALG-2 r11, B3)

Per-declaration zero-axiom gate for the boundary-word homomorphism, the per-letter pairs, the layout producer, the
word-level and path-level domain round-trips, the length smoke, and the concrete witness probe.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutPathWord_composePath
#assert_no_axioms FX1Poly.Polygraph.Amalgam.wallLetterPair
#assert_no_axioms FX1Poly.Polygraph.Amalgam.gapLetterPair
#assert_no_axioms FX1Poly.Polygraph.Amalgam.finestLetterPair
#assert_no_axioms FX1Poly.Polygraph.Amalgam.finestLayout
#assert_no_axioms FX1Poly.Polygraph.Amalgam.finestLetterPair_gapDomWord
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutPathWord_finestLayout
#assert_no_axioms FX1Poly.Polygraph.Amalgam.gapDomLayout_finestLayout
#assert_no_axioms FX1Poly.Polygraph.Amalgam.finestLayout_length
#assert_no_axioms FX1Poly.Polygraph.Amalgam.finestLayoutWitnessProbe
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasFinestPairsLayout

end FX1PolyAudit
