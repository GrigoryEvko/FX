import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingBoundaryIndexCensus

/-! # FX1PolyAudit/…/MatchingBoundaryIndexCensus — zero-axiom gate

Per-declaration zero-axiom gate for the carrier-free boundary-index census + partner INVOLUTION (Track B
b#1 infrastructure): the census-parameterized fixed-point-free involution over abstract
`(links, boundaryNodes, total)`, verbatim ports of the shipped `ArcWireState`-bound lemmas with the census
in plain index form.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.partnerIndexOf_below_generic
#assert_no_axioms FX1Poly.Polygraph.partnerIndexOf_sameComponent_or_fixed_generic
#assert_no_axioms FX1Poly.Polygraph.partnerIndexOf_uniqueSameComponent_generic
#assert_no_axioms FX1Poly.Polygraph.partnerIndexOf_isInvolution_ofBoundaryIndexCensus
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingBoundaryIndexCensus

end FX1PolyAudit
