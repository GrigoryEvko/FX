import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringQuadrupleSingletonBlockCoChain

/-! # FX1PolyAudit.…WalkingString.StringQuadrupleSingletonBlockCoChainAxiomWitness — INDEPENDENT axiom witness (FC-4 r4)

The trusted independent cross-check for the `k = 3` singleton-block `(dom, cod)` read-off-pair brick: raw `#print axioms`
(the built-in, NOT the custom `#assert_no_axioms` command) on the arity helper, the brick, the ported DOM-chain
fixtures, the COD co-chain carrier fires, the brick fires on the `L4`-carrying fixtures, the negative controls, and the
marker.  Each must print `does not depend on any axioms`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.quadAtomDomLenZeroOrTwo
#print axioms FX1Poly.Polygraph.stringQuadChainedSingletonBlock_eq_of_readOffPair
#print axioms FX1Poly.Polygraph.quadCupAtomBase_domChained
#print axioms FX1Poly.Polygraph.quadCupAtomBaseFresh_domChained
#print axioms FX1Poly.Polygraph.quadCapAtomTipFresh_domChained
#print axioms FX1Poly.Polygraph.quadSingletonTopWord_computesCupCod
#print axioms FX1Poly.Polygraph.quadSingletonTopWord_computesCapCod
#print axioms FX1Poly.Polygraph.stringQuadSingletonBlock_firesOnFreshL4Cup
#print axioms FX1Poly.Polygraph.stringQuadSingletonBlock_firesOnFreshL4Cap
#print axioms FX1Poly.Polygraph.quadDomOnlySingletonBlock_refutedAtThree
#print axioms FX1Poly.Polygraph.quadCupSingletonTopWords_differ
#print axioms FX1Poly.Polygraph.fxString_hasNColourSingletonBlockCoChainBrick

end FX1PolyAudit
