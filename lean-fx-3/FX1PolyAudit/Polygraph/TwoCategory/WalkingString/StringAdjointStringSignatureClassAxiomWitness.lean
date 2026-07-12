import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringAdjointStringSignatureClass

/-! # FX1PolyAudit.…WalkingString.StringAdjointStringSignatureClassAxiomWitness — INDEPENDENT axiom witness (FC-4 r5)

The trusted independent cross-check for the adjoint-string signature class + the generic determinacy keystone: raw
`#print axioms` (the built-in, NOT the custom `#assert_no_axioms` command) on the `k = 2` instance-field analogues, the
two class instances, the generic dual keystone / consumers / singleton-block brick, the `k = 2` / `k = 3` recoveries,
the concrete fires, the negative control, and the two markers.  Each must print `does not depend on any axioms`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.stringTripleGeneratorDomLenZeroOrTwo
#print axioms FX1Poly.Polygraph.stringTripleCapCodZeroOfDomTwo
#print axioms FX1Poly.Polygraph.stringTripleCupCodDeterminesGenerator
#print axioms FX1Poly.Polygraph.stringTripleCapDomDeterminesGenerator
#print axioms FX1Poly.Polygraph.adjointStringSignatureAtTwo
#print axioms FX1Poly.Polygraph.adjointStringSignatureAtThree
#print axioms FX1Poly.Polygraph.genericStringCupSpineAtom_eq_of_codWordReadOffs
#print axioms FX1Poly.Polygraph.genericStringCapSpineAtom_eq_of_domWordReadOffs
#print axioms FX1Poly.Polygraph.genericStringCapAtom_eq_of_sharedDom_sameWindow
#print axioms FX1Poly.Polygraph.genericStringCupAtom_eq_of_sharedCod_sameWindow
#print axioms FX1Poly.Polygraph.genericStringChainedSingletonBlock_eq_of_readOffPair
#print axioms FX1Poly.Polygraph.stringSharedCodCupPin_shippedInhabitant
#print axioms FX1Poly.Polygraph.stringSharedCodCupPin_viaGenericClassAtTwo
#print axioms FX1Poly.Polygraph.stringSharedDomCapPin_shippedInhabitant
#print axioms FX1Poly.Polygraph.stringSharedDomCapPin_viaGenericClassAtTwo
#print axioms FX1Poly.Polygraph.stringQuadCupKeystone_shippedInhabitant
#print axioms FX1Poly.Polygraph.stringQuadCupKeystone_viaGenericClassAtThree
#print axioms FX1Poly.Polygraph.stringQuadCapKeystone_shippedInhabitant
#print axioms FX1Poly.Polygraph.stringQuadCapKeystone_viaGenericClassAtThree
#print axioms FX1Poly.Polygraph.stringQuadSingletonBlock_shippedInhabitant
#print axioms FX1Poly.Polygraph.stringQuadSingletonBlock_viaGenericClassAtThree
#print axioms FX1Poly.Polygraph.stringTripleCupAtomBase
#print axioms FX1Poly.Polygraph.stringTripleCapAtomTip
#print axioms FX1Poly.Polygraph.genericCupKeystone_firesAtTwoOnConcreteCup
#print axioms FX1Poly.Polygraph.genericCapConsumer_firesAtTwoOnConcreteCap
#print axioms FX1Poly.Polygraph.genericCupKeystone_firesAtThreeOnFreshL4Cup
#print axioms FX1Poly.Polygraph.genericCapKeystone_firesAtThreeOnFreshL4Cap
#print axioms FX1Poly.Polygraph.genericSingletonBlock_firesAtThreeOnFreshL4Cup
#print axioms FX1Poly.Polygraph.genericBrick_declinesOnDistinctCupPair
#print axioms FX1Poly.Polygraph.fxString_hasAdjointStringSignatureClass
#print axioms FX1Poly.Polygraph.fxString_hasGenericStringDeterminacyKeystone

end FX1PolyAudit
