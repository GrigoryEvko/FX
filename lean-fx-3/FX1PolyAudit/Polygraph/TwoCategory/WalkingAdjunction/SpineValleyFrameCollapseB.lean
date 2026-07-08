import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyFrameCollapseB

/-! # FX1PolyAudit/…/SpineValleyFrameCollapseB — zero-axiom gate

Per-declaration zero-axiom gate for Piece I STRAIGHTEN (ii) — the HANDEDNESS-B (RIGHT-snake) general shared-leg
frame collapse: the two named seed-snake generator legs (`seedSnakeCupGenLegB` / `seedSnakeCapGenLegB`), the two
shared-leg legs (`sharedLegCupLegB` / `sharedLegCapLegB`), the distribution `whiskeredSnakeDistributesToLegsB`, the
cast-free general collapse `generalContextFrameLegsCollapseB`, and its feed into `snakeStraightensInContext`
(`generalContextSnakeStraightensInContextB`).  Every declaration must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.seedSnakeCupGenLegB
#assert_no_axioms FX1Poly.Polygraph.seedSnakeCapGenLegB
#assert_no_axioms FX1Poly.Polygraph.sharedLegCupLegB
#assert_no_axioms FX1Poly.Polygraph.sharedLegCapLegB
#assert_no_axioms FX1Poly.Polygraph.whiskeredSnakeDistributesToLegsB
#assert_no_axioms FX1Poly.Polygraph.generalContextFrameLegsCollapseB
#assert_no_axioms FX1Poly.Polygraph.generalContextSnakeStraightensInContextB
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasGeneralSharedLegFrameCollapseB

end FX1PolyAudit
