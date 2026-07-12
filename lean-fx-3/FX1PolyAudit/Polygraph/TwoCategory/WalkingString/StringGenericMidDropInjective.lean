import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringGenericMidDropInjective

/-! # FX1PolyAudit.…WalkingString.StringGenericMidDropInjective — zero-axiom gate (FC-4 r6, the drop tranche)

Per-declaration zero-axiom gate for the generic mid-width drop bricks: the downward drop-injectivity linchpin, the
upward back-append companion, each `k = 2` recovery pair, the `k = 3` fires on genuinely DISTINCT quad spines with
their computed-matching certificates, the negative control, and the marker.  Must be free of `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.genericDropLastCup_matching_injective_mid
#assert_no_axioms FX1Poly.Polygraph.genericBackAppend_matching_congr_mid
#assert_no_axioms FX1Poly.Polygraph.stringDropInjectiveMid_shippedInhabitant
#assert_no_axioms FX1Poly.Polygraph.stringDropInjectiveMid_viaGenericClassAtTwo
#assert_no_axioms FX1Poly.Polygraph.stringBackAppendMid_shippedInhabitant
#assert_no_axioms FX1Poly.Polygraph.stringBackAppendMid_viaGenericClassAtTwo
#assert_no_axioms FX1Poly.Polygraph.quadDropUnitOneW0
#assert_no_axioms FX1Poly.Polygraph.quadDropUnitThreeW0
#assert_no_axioms FX1Poly.Polygraph.quadDropLastCupW2
#assert_no_axioms FX1Poly.Polygraph.quadDropFullFirst_matchingComputes
#assert_no_axioms FX1Poly.Polygraph.quadDropFullSecond_matchingComputes
#assert_no_axioms FX1Poly.Polygraph.genericDropInjectiveMid_firesAtThree
#assert_no_axioms FX1Poly.Polygraph.genericBackAppendMid_firesAtThree
#assert_no_axioms FX1Poly.Polygraph.quadDropPrefixes_distinctGenerators
#assert_no_axioms FX1Poly.Polygraph.fxString_hasGenericMidDropInjective

end FX1PolyAudit
