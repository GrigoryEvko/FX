import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringGenericWidthArityBridge

/-! # FX1PolyAudit.…WalkingString.StringGenericWidthArityBridgeAxiomWitness — INDEPENDENT axiom witness (FC-4 r5, B3)

The trusted independent cross-check for the generic width-arity bridge: raw `#print axioms` (the built-in, NOT the
custom `#assert_no_axioms` command) on the full-arity fields, the two connectivity instances, the generic total
classifier, the generic open-wire tracking, the `k = 2` recovery pair, the `k = 3` fire, and the marker.  Each must
print `does not depend on any axioms` (in particular the structurally-recursive tracking pulls no `WellFounded`-borne
axiom). -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.stringTripleGeneratorFullArity
#print axioms FX1Poly.Polygraph.quadGeneratorFullArity
#print axioms FX1Poly.Polygraph.adjointStringConnectivityAtTwo
#print axioms FX1Poly.Polygraph.adjointStringConnectivityAtThree
#print axioms FX1Poly.Polygraph.genericSpineAtom_hasCupOrCapArity
#print axioms FX1Poly.Polygraph.genericProcessSpine_openWires_length_ofChainedAppend
#print axioms FX1Poly.Polygraph.genericProcessSpine_prefix_openWires_eq_lastDomBoundary
#print axioms FX1Poly.Polygraph.stringPrefixOpenWires_shippedInhabitant
#print axioms FX1Poly.Polygraph.stringPrefixOpenWires_viaGenericClassAtTwo
#print axioms FX1Poly.Polygraph.quadCupChainSingleton
#print axioms FX1Poly.Polygraph.genericPrefixOpenWires_firesAtThreeOnCup
#print axioms FX1Poly.Polygraph.fxString_hasGenericWidthArityBridge

end FX1PolyAudit
