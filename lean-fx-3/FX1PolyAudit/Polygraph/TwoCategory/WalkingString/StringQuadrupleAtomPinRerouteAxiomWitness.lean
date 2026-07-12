import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringQuadrupleAtomPinReroute

/-! # FX1PolyAudit.…WalkingString.StringQuadrupleAtomPinRerouteAxiomWitness — INDEPENDENT axiom witness (FC-4 r2)

The trusted independent cross-check for the cup-restricted COD reroute + the `k = 3` engine fire: raw `#print axioms`
(the built-in, NOT the custom `#assert_no_axioms` command) on the refutation pin, the two restricted pins, the wide
truth tables, the engine / LOCATE fixtures, and the markers.  Each must print `does not depend on any axioms`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.quad_dom_does_not_determine_cod
#print axioms FX1Poly.Polygraph.stringQuadTwoCell_domPack_uniqueOfCod_forCups
#print axioms FX1Poly.Polygraph.stringQuadTwoCell_codPack_uniqueOfDom_forCaps
#print axioms FX1Poly.Polygraph.cupCods_allDistinct_atThree
#print axioms FX1Poly.Polygraph.cupCods_allDistinct_atFour
#print axioms FX1Poly.Polygraph.capDoms_allDistinct_atThree
#print axioms FX1Poly.Polygraph.capDoms_allDistinct_atFour
#print axioms FX1Poly.Polygraph.cupCapCrossDisjoint_atThree
#print axioms FX1Poly.Polygraph.cupCapCrossDisjoint_atFour
#print axioms FX1Poly.Polygraph.collapsedCupDoms_notAllDistinct
#print axioms FX1Poly.Polygraph.quadEngineCupFires
#print axioms FX1Poly.Polygraph.quadEngineCupCapClosesLoop
#print axioms FX1Poly.Polygraph.quadLocateFiresOnCupThenCap
#print axioms FX1Poly.Polygraph.quadLocateDeclinesOnCupThenCup
#print axioms FX1Poly.Polygraph.fxString_hasQuadrupleAtomPinReroute
#print axioms FX1Poly.Polygraph.fxString_hasKGenericConnectivityEngineFired

end FX1PolyAudit
