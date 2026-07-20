import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.ZXPhaseFree.CombMovingFeed

/-! # FX1PolyAudit.Polygraph.Omega.ZXPhaseFree.CombMovingFeed — zero-axiom gate
(the isolated moving-position feed-collapse general in the left pad, the moving
chain extension, the composed moving-feed step, their fires and span pins, and the
honest general-fold wall)

Per-declaration zero-axiom gate for the moving-feed round: the moving-position
feed-collapse (`zxlFeedColumnCollapseAt`, general in the pad), the moving chain
extension (`zxlChainGainsLegAtPad`), the composed moving-feed step
(`zxlBundleFeedStepAt`, general in the pad), the five fires (the `k = 0`
reconciliation, the pad-1 collapse, the feed step at pads 0/1/2), the three span
pins (two correlated endpoints plus a discriminating FALSE control), the three live
content markers, and the owner-false full-fold marker.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`,
`omega`, `WellFounded.fix`, `funext`.  Built by the FX1PolyAudit lib glob;
AuditAll registration is a later round's bookkeeping (AuditAll untouched per this
round's commission). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxlFeedColumnCollapseAt
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxlChainGainsLegAtPad
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxlBundleFeedStepAt
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxlFeedColumnCollapseAtZeroFire
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxlFeedColumnCollapseAtOneFire
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxlBundleFeedStepAtZeroFire
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxlBundleFeedStepAtOneFire
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxlBundleFeedStepAtTwoFire
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxlBundleFeedStepAtOneSpanPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxlBundleFeedStepAtTwoSpanPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxlBundleFeedStepAtOneNotIndependentSpanPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxlHasMovingFeedCollapse
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxlHasMovingChainExtension
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxlHasMovingFeedStep
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxlHasMovingPositionFeed

end FX1PolyAudit
