import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringAdjointStringSignatureClass

/-! # FX1PolyAudit.…WalkingString.StringAdjointStringSignatureClass — zero-axiom gate (FC-4 r5, B1 + B2)

Per-declaration zero-axiom gate for the adjoint-string signature class and the generic determinacy keystone: the
`k = 2` instance-field analogues, the two class instances (`adjointStringSignatureAtTwo` /
`adjointStringSignatureAtThree`), the generic dual keystone + consumers + singleton-block brick, the `k = 2` / `k = 3`
recoveries (the shipped-inhabitant + via-generic pairs), the concrete `k = 2` / `k = 3` fires, the negative control,
and the two markers.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega` (the
`decide` guards on concrete `List Nat` / `Nat` lengths are propext-clean). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringTripleGeneratorDomLenZeroOrTwo
#assert_no_axioms FX1Poly.Polygraph.stringTripleCapCodZeroOfDomTwo
#assert_no_axioms FX1Poly.Polygraph.stringTripleCupCodDeterminesGenerator
#assert_no_axioms FX1Poly.Polygraph.stringTripleCapDomDeterminesGenerator
#assert_no_axioms FX1Poly.Polygraph.adjointStringSignatureAtTwo
#assert_no_axioms FX1Poly.Polygraph.adjointStringSignatureAtThree
#assert_no_axioms FX1Poly.Polygraph.genericStringCupSpineAtom_eq_of_codWordReadOffs
#assert_no_axioms FX1Poly.Polygraph.genericStringCapSpineAtom_eq_of_domWordReadOffs
#assert_no_axioms FX1Poly.Polygraph.genericStringCapAtom_eq_of_sharedDom_sameWindow
#assert_no_axioms FX1Poly.Polygraph.genericStringCupAtom_eq_of_sharedCod_sameWindow
#assert_no_axioms FX1Poly.Polygraph.genericStringChainedSingletonBlock_eq_of_readOffPair
#assert_no_axioms FX1Poly.Polygraph.stringSharedCodCupPin_shippedInhabitant
#assert_no_axioms FX1Poly.Polygraph.stringSharedCodCupPin_viaGenericClassAtTwo
#assert_no_axioms FX1Poly.Polygraph.stringSharedDomCapPin_shippedInhabitant
#assert_no_axioms FX1Poly.Polygraph.stringSharedDomCapPin_viaGenericClassAtTwo
#assert_no_axioms FX1Poly.Polygraph.stringQuadCupKeystone_shippedInhabitant
#assert_no_axioms FX1Poly.Polygraph.stringQuadCupKeystone_viaGenericClassAtThree
#assert_no_axioms FX1Poly.Polygraph.stringQuadCapKeystone_shippedInhabitant
#assert_no_axioms FX1Poly.Polygraph.stringQuadCapKeystone_viaGenericClassAtThree
#assert_no_axioms FX1Poly.Polygraph.stringQuadSingletonBlock_shippedInhabitant
#assert_no_axioms FX1Poly.Polygraph.stringQuadSingletonBlock_viaGenericClassAtThree
#assert_no_axioms FX1Poly.Polygraph.stringTripleCupAtomBase
#assert_no_axioms FX1Poly.Polygraph.stringTripleCapAtomTip
#assert_no_axioms FX1Poly.Polygraph.genericCupKeystone_firesAtTwoOnConcreteCup
#assert_no_axioms FX1Poly.Polygraph.genericCapConsumer_firesAtTwoOnConcreteCap
#assert_no_axioms FX1Poly.Polygraph.genericCupKeystone_firesAtThreeOnFreshL4Cup
#assert_no_axioms FX1Poly.Polygraph.genericCapKeystone_firesAtThreeOnFreshL4Cap
#assert_no_axioms FX1Poly.Polygraph.genericSingletonBlock_firesAtThreeOnFreshL4Cup
#assert_no_axioms FX1Poly.Polygraph.genericBrick_declinesOnDistinctCupPair
#assert_no_axioms FX1Poly.Polygraph.fxString_hasAdjointStringSignatureClass
#assert_no_axioms FX1Poly.Polygraph.fxString_hasGenericStringDeterminacyKeystone

end FX1PolyAudit
