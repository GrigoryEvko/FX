import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringQuadrupleDeterminacyKeystone

/-! # FX1PolyAudit.…WalkingString.StringQuadrupleDeterminacyKeystoneAxiomWitness — INDEPENDENT axiom witness (FC-4 r3)

The trusted independent cross-check for the `k = 3` determinacy keystone: raw `#print axioms` (the built-in, NOT the
custom `#assert_no_axioms` command) on the subsingleton, the cap-arity bridge, the dual keystone, the two consumers,
the `L4`-carrying fires, the negative controls, and the marker.  Each must print `does not depend on any axioms`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.stringQuadTwoCell_unique_of_wordBoundaries
#print axioms FX1Poly.Polygraph.quadCapCodZero_ofDomTwo
#print axioms FX1Poly.Polygraph.stringQuadCapSpineAtom_eq_of_domWordReadOffs
#print axioms FX1Poly.Polygraph.stringQuadCupSpineAtom_eq_of_codWordReadOffs
#print axioms FX1Poly.Polygraph.stringQuadCapAtom_eq_of_sharedDom_sameWindow
#print axioms FX1Poly.Polygraph.stringQuadCupAtom_eq_of_sharedCod_sameWindow
#print axioms FX1Poly.Polygraph.quadCupFreshCod_carriesL4
#print axioms FX1Poly.Polygraph.quadCapFreshDom_carriesL4
#print axioms FX1Poly.Polygraph.stringQuadCupKeystone_firesOnFreshL4Cup
#print axioms FX1Poly.Polygraph.stringQuadCapKeystone_firesOnFreshL4Cap
#print axioms FX1Poly.Polygraph.stringQuadCupConsumer_firesOnFreshL4Cup
#print axioms FX1Poly.Polygraph.stringQuadCapConsumer_firesOnFreshL4Cap
#print axioms FX1Poly.Polygraph.quadCupAtoms_distinctByCodReadOff
#print axioms FX1Poly.Polygraph.quadCupAtoms_shareDomWord
#print axioms FX1Poly.Polygraph.quadCapAtoms_distinctByDomReadOff
#print axioms FX1Poly.Polygraph.quadCapAtoms_shareCodWord
#print axioms FX1Poly.Polygraph.fxString_hasNColourAtomPinKeystone

end FX1PolyAudit
