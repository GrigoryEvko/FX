import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringAdjointStringOrientationCrux

/-! # FX1PolyAudit.…WalkingString.StringAdjointStringOrientationCrux — zero-axiom gate (FC-4 r1 opener, O2 crux)

Per-declaration zero-axiom gate for the `n`-letter orientation label-pinning crux: the generic crux
(`ascendingPair_ne_descendingPair`), the `k = 2` bridge (`paths_ne_of_indexWords_ne`, the two orientation-recovered
separators, and `stringCupCod_ne_capDom_viaOrientation` recovering the FROZEN shipped crux), the `k = 3` fresh firing
(`quadCupCod_ne_capDom_fired`, `quadFreshPair_ne`, `carrierFixtureSpace_grows`), and the two honesty markers.  Must be
free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.ascendingPair_ne_descendingPair
#assert_no_axioms FX1Poly.Polygraph.paths_ne_of_indexWords_ne
#assert_no_axioms FX1Poly.Polygraph.stringFG_ne_stringHG_viaOrientation
#assert_no_axioms FX1Poly.Polygraph.stringGH_ne_stringGF_viaOrientation
#assert_no_axioms FX1Poly.Polygraph.stringCupCod_ne_capDom_viaOrientation
#assert_no_axioms FX1Poly.Polygraph.quadCupCod_ne_capDom_fired
#assert_no_axioms FX1Poly.Polygraph.quadFreshPair_ne
#assert_no_axioms FX1Poly.Polygraph.carrierFixtureSpace_grows
#assert_no_axioms FX1Poly.Polygraph.fxString_hasOrientationCruxBridgesShipped
#assert_no_axioms FX1Poly.Polygraph.fxString_hasOrientationCruxFiredAtKThree

end FX1PolyAudit
