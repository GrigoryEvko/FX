import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringKParameterizationCensus

/-! # FX1PolyAudit.…WalkingString.StringKParameterizationCensusAxiomWitness — INDEPENDENT axiom witness (FC-4 r1 O1)

The trusted independent cross-check for the `k`-parameterization census: raw `#print axioms` (the built-in, NOT the
custom `#assert_no_axioms` command) on the load-bearing carrier facts, the shipped-world embedding pins, and the road
markers.  Each must print `does not depend on any axioms`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.pathIndexWord
#print axioms FX1Poly.Polygraph.isAscendingPair
#print axioms FX1Poly.Polygraph.adjointStringCupCods
#print axioms FX1Poly.Polygraph.adjointStringCapDoms
#print axioms FX1Poly.Polygraph.adjointStringCupCods_atThree
#print axioms FX1Poly.Polygraph.adjointStringCapDoms_atThree
#print axioms FX1Poly.Polygraph.adjointStringCupCods_allAscending_atThree
#print axioms FX1Poly.Polygraph.adjointStringCapDoms_allDescending_atThree
#print axioms FX1Poly.Polygraph.shippedCupCods_eq_carrierAtTwo
#print axioms FX1Poly.Polygraph.shippedCapDoms_eq_carrierAtTwo
#print axioms FX1Poly.Polygraph.fxString_hasKParameterizationCensus
#print axioms FX1Poly.Polygraph.fxString_hasNColourOrientationLabelPinningCrux
#print axioms FX1Poly.Polygraph.fxString_hasNColourAtomPinReroute

end FX1PolyAudit
