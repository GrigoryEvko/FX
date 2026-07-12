import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringGenericMidDropInjective

/-! # FX1PolyAudit.…WalkingString.StringGenericMidDropInjectiveAxiomWitness — INDEPENDENT axiom witness (FC-4 r6)

The trusted independent cross-check for the generic mid-width drop bricks: raw `#print axioms` (the built-in, NOT
the custom `#assert_no_axioms` command) on the downward drop-injectivity, the upward back-append, each `k = 2`
recovery pair, the `k = 3` fires with their quad fixtures and computed-matching certificates, the negative control,
and the marker.  Each must print `does not depend on any axioms` (in particular the `by decide` certificates and
fires pull no `propext`). -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.genericDropLastCup_matching_injective_mid
#print axioms FX1Poly.Polygraph.genericBackAppend_matching_congr_mid
#print axioms FX1Poly.Polygraph.stringDropInjectiveMid_shippedInhabitant
#print axioms FX1Poly.Polygraph.stringDropInjectiveMid_viaGenericClassAtTwo
#print axioms FX1Poly.Polygraph.stringBackAppendMid_shippedInhabitant
#print axioms FX1Poly.Polygraph.stringBackAppendMid_viaGenericClassAtTwo
#print axioms FX1Poly.Polygraph.quadDropUnitOneW0
#print axioms FX1Poly.Polygraph.quadDropUnitThreeW0
#print axioms FX1Poly.Polygraph.quadDropLastCupW2
#print axioms FX1Poly.Polygraph.quadDropFullFirst_matchingComputes
#print axioms FX1Poly.Polygraph.quadDropFullSecond_matchingComputes
#print axioms FX1Poly.Polygraph.genericDropInjectiveMid_firesAtThree
#print axioms FX1Poly.Polygraph.genericBackAppendMid_firesAtThree
#print axioms FX1Poly.Polygraph.quadDropPrefixes_distinctGenerators
#print axioms FX1Poly.Polygraph.fxString_hasGenericMidDropInjective

end FX1PolyAudit
