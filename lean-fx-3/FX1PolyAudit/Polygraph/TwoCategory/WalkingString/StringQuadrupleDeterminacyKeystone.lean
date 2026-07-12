import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringQuadrupleDeterminacyKeystone

/-! # FX1PolyAudit.…WalkingString.StringQuadrupleDeterminacyKeystone — zero-axiom gate (FC-4 r3, K1 + K2)

Per-declaration zero-axiom gate for the `k = 3` determinacy keystone: the parallel-generator subsingleton
(`stringQuadTwoCell_unique_of_wordBoundaries`), the cap-arity bridge (`quadCapCodZero_ofDomTwo`), the dual keystone
(`stringQuadCapSpineAtom_eq_of_domWordReadOffs` / `stringQuadCupSpineAtom_eq_of_codWordReadOffs`), the two atom-level
consumers (`stringQuadCapAtom_eq_of_sharedDom_sameWindow` / `stringQuadCupAtom_eq_of_sharedCod_sameWindow`), the
`L4`-carrying fixtures + their fires, the negative controls, and the marker.  Must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega` (the `decide` guards on concrete `Nat` / `List Nat` are propext-clean). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringQuadTwoCell_unique_of_wordBoundaries
#assert_no_axioms FX1Poly.Polygraph.quadCapCodZero_ofDomTwo
#assert_no_axioms FX1Poly.Polygraph.stringQuadCapSpineAtom_eq_of_domWordReadOffs
#assert_no_axioms FX1Poly.Polygraph.stringQuadCupSpineAtom_eq_of_codWordReadOffs
#assert_no_axioms FX1Poly.Polygraph.stringQuadCapAtom_eq_of_sharedDom_sameWindow
#assert_no_axioms FX1Poly.Polygraph.stringQuadCupAtom_eq_of_sharedCod_sameWindow
#assert_no_axioms FX1Poly.Polygraph.quadCupAtomBaseFresh
#assert_no_axioms FX1Poly.Polygraph.quadCapAtomTipFresh
#assert_no_axioms FX1Poly.Polygraph.quadCapAtomTipOne
#assert_no_axioms FX1Poly.Polygraph.quadCupFreshCod_carriesL4
#assert_no_axioms FX1Poly.Polygraph.quadCapFreshDom_carriesL4
#assert_no_axioms FX1Poly.Polygraph.stringQuadCupKeystone_firesOnFreshL4Cup
#assert_no_axioms FX1Poly.Polygraph.stringQuadCapKeystone_firesOnFreshL4Cap
#assert_no_axioms FX1Poly.Polygraph.stringQuadCupConsumer_firesOnFreshL4Cup
#assert_no_axioms FX1Poly.Polygraph.stringQuadCapConsumer_firesOnFreshL4Cap
#assert_no_axioms FX1Poly.Polygraph.quadCupAtoms_distinctByCodReadOff
#assert_no_axioms FX1Poly.Polygraph.quadCupAtoms_shareDomWord
#assert_no_axioms FX1Poly.Polygraph.quadCapAtoms_distinctByDomReadOff
#assert_no_axioms FX1Poly.Polygraph.quadCapAtoms_shareCodWord
#assert_no_axioms FX1Poly.Polygraph.fxString_hasNColourAtomPinKeystone

end FX1PolyAudit
