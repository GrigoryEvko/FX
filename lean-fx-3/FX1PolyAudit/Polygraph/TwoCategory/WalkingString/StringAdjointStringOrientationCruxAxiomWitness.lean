import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringAdjointStringOrientationCrux

/-! # FX1PolyAudit.…WalkingString.StringAdjointStringOrientationCruxAxiomWitness — INDEPENDENT axiom witness (FC-4 r1 O2)

The trusted independent cross-check for the orientation label-pinning crux: raw `#print axioms` (the built-in, NOT the
custom `#assert_no_axioms` command) on the generic crux, the shipped-crux recovery, the `k = 3` firing, and the honesty
markers.  Each must print `does not depend on any axioms`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.ascendingPair_ne_descendingPair
#print axioms FX1Poly.Polygraph.stringFG_ne_stringHG_viaOrientation
#print axioms FX1Poly.Polygraph.stringGH_ne_stringGF_viaOrientation
#print axioms FX1Poly.Polygraph.stringCupCod_ne_capDom_viaOrientation
#print axioms FX1Poly.Polygraph.quadCupCod_ne_capDom_fired
#print axioms FX1Poly.Polygraph.quadFreshPair_ne
#print axioms FX1Poly.Polygraph.carrierFixtureSpace_grows
#print axioms FX1Poly.Polygraph.fxString_hasOrientationCruxBridgesShipped
#print axioms FX1Poly.Polygraph.fxString_hasOrientationCruxFiredAtKThree

end FX1PolyAudit
