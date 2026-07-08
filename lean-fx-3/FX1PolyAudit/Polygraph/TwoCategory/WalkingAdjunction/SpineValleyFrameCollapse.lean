import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyFrameCollapse

/-! # FX1PolyAudit/…/SpineValleyFrameCollapse — zero-axiom gate

Per-declaration zero-axiom gate for Piece I STRAIGHTEN Gap 2b — the GENERAL shared-leg frame collapse: the two
named seed-snake generator legs (`seedSnakeCupGenLeg` / `seedSnakeCapGenLeg`), the two shared-leg legs
(`sharedLegCupLeg` / `sharedLegCapLeg`), the distribution `whiskeredSnakeDistributesToLegs`, the cast-free general
collapse `generalContextFrameLegsCollapse`, its feed into `snakeStraightensInContext`
(`generalContextSnakeStraightensInContext`), the two merged-`atomFrame` split witnesses
(`cupLegSplitsToMergedCupFrameInner` / `capLegSplitsToMergedCapFrameInner`).  Every declaration must be free of
`propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.seedSnakeCupGenLeg
#assert_no_axioms FX1Poly.Polygraph.seedSnakeCapGenLeg
#assert_no_axioms FX1Poly.Polygraph.sharedLegCupLeg
#assert_no_axioms FX1Poly.Polygraph.sharedLegCapLeg
#assert_no_axioms FX1Poly.Polygraph.whiskeredSnakeDistributesToLegs
#assert_no_axioms FX1Poly.Polygraph.generalContextFrameLegsCollapse
#assert_no_axioms FX1Poly.Polygraph.generalContextSnakeStraightensInContext
#assert_no_axioms FX1Poly.Polygraph.cupLegSplitsToMergedCupFrameInner
#assert_no_axioms FX1Poly.Polygraph.capLegSplitsToMergedCapFrameInner
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasGeneralSharedLegFrameCollapse

end FX1PolyAudit
