import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingWidthZeroInvolution

/-! # FX1PolyAudit/…/MatchingWidthZeroInvolution — zero-axiom gate

Per-declaration zero-axiom gate for Track B b#1 (the make-or-break): the width-0 pure-cup partner
INVOLUTION, POSITIVITY-FREE.  The node-value root-class census `NodeRootClassSmall` and open-wire
distinctness both fold through the pure-cup `processSpine` run from the width-0 seed with NO sentinel; they
discharge the carrier-free `BoundaryIndexCensus`, and the carrier-free involution lands the partner
involution on `matchingOfSpineList 0` — NO `arcDiagram_eq_matching`, NO `0 < bottomCount`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.widthZeroPureCup_boundaryIndexCensus
#assert_no_axioms FX1Poly.Polygraph.matchingOfSpineListZero_partner_isInvolution
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingWidthZeroInvolution

end FX1PolyAudit
