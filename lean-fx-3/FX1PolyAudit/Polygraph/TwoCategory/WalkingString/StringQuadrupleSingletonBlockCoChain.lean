import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringQuadrupleSingletonBlockCoChain

/-! # FX1PolyAudit.…WalkingString.StringQuadrupleSingletonBlockCoChain — zero-axiom gate (FC-4 r4, B1)

Per-declaration zero-axiom gate for the `k = 3` singleton-block `(dom, cod)` read-off-pair brick: the arity helper
(`quadAtomDomLenZeroOrTwo`), the brick (`stringQuadChainedSingletonBlock_eq_of_readOffPair`), the ported DOM-chain
fixtures (`quadCupAtomBase_domChained` / `quadCupAtomBaseFresh_domChained` / `quadCapAtomTipFresh_domChained`), the COD
co-chain carrier fires (`quadSingletonTopWord_computesCupCod` / `quadSingletonTopWord_computesCapCod`), the brick fires
on the `L4`-carrying fixtures (`stringQuadSingletonBlock_firesOnFreshL4Cup` / `stringQuadSingletonBlock_firesOnFreshL4Cap`),
the negative controls (`quadDomOnlySingletonBlock_refutedAtThree` / `quadCupSingletonTopWords_differ`), and the marker.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega` (the `decide` guard on concrete
`List Nat` is propext-clean). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.quadAtomDomLenZeroOrTwo
#assert_no_axioms FX1Poly.Polygraph.stringQuadChainedSingletonBlock_eq_of_readOffPair
#assert_no_axioms FX1Poly.Polygraph.quadCupAtomBase_domChained
#assert_no_axioms FX1Poly.Polygraph.quadCupAtomBaseFresh_domChained
#assert_no_axioms FX1Poly.Polygraph.quadCapAtomTipFresh_domChained
#assert_no_axioms FX1Poly.Polygraph.quadSingletonTopWord_computesCupCod
#assert_no_axioms FX1Poly.Polygraph.quadSingletonTopWord_computesCapCod
#assert_no_axioms FX1Poly.Polygraph.stringQuadSingletonBlock_firesOnFreshL4Cup
#assert_no_axioms FX1Poly.Polygraph.stringQuadSingletonBlock_firesOnFreshL4Cap
#assert_no_axioms FX1Poly.Polygraph.quadDomOnlySingletonBlock_refutedAtThree
#assert_no_axioms FX1Poly.Polygraph.quadCupSingletonTopWords_differ
#assert_no_axioms FX1Poly.Polygraph.fxString_hasNColourSingletonBlockCoChainBrick

end FX1PolyAudit
