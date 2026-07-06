import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPerfectMatchingIndexBridge

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcPerfectMatchingIndexBridge — zero-axiom gate

Per-declaration zero-axiom gate for the token→range bridge closing the noFixedPoint leg: the inverse index map
round-trips, the range-frame perfect matching, and the no-fixed-point capstone at the extracted spine state.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.indexOfToken_tokenOfIndex
#assert_no_axioms FX1Poly.Polygraph.tokenOfIndex_indexOfToken
#assert_no_axioms FX1Poly.Polygraph.indexOfToken_lt
#assert_no_axioms FX1Poly.Polygraph.arcPerfectMatching_ofTokens
#assert_no_axioms FX1Poly.Polygraph.partnerIndexOf_neSelf_ofChainedSpine

end FX1PolyAudit
