import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringGenericWidthArityBridge

/-! # FX1PolyAudit.…WalkingString.StringGenericWidthArityBridge — zero-axiom gate (FC-4 r5, B3)

Per-declaration zero-axiom gate for the generic width-arity bridge: the `k = 2` / `k = 3` full-arity fields, the two
connectivity instances, the generic total classifier, the generic open-wire tracking (structural recursion on the
prefix — the `#print axioms` witness confirms no `WellFounded.fix`-borne axiom), the `k = 2` recovery pair, the `k = 3`
fire (with its singleton chain), and the marker.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringTripleGeneratorFullArity
#assert_no_axioms FX1Poly.Polygraph.quadGeneratorFullArity
#assert_no_axioms FX1Poly.Polygraph.adjointStringConnectivityAtTwo
#assert_no_axioms FX1Poly.Polygraph.adjointStringConnectivityAtThree
#assert_no_axioms FX1Poly.Polygraph.genericSpineAtom_hasCupOrCapArity
#assert_no_axioms FX1Poly.Polygraph.genericProcessSpine_openWires_length_ofChainedAppend
#assert_no_axioms FX1Poly.Polygraph.genericProcessSpine_prefix_openWires_eq_lastDomBoundary
#assert_no_axioms FX1Poly.Polygraph.stringPrefixOpenWires_shippedInhabitant
#assert_no_axioms FX1Poly.Polygraph.stringPrefixOpenWires_viaGenericClassAtTwo
#assert_no_axioms FX1Poly.Polygraph.quadCupChainSingleton
#assert_no_axioms FX1Poly.Polygraph.genericPrefixOpenWires_firesAtThreeOnCup
#assert_no_axioms FX1Poly.Polygraph.fxString_hasGenericWidthArityBridge

end FX1PolyAudit
