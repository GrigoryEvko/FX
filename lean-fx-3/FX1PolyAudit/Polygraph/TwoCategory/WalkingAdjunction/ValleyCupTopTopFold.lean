import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyCupTopTopFold

/-! # FX1PolyAudit/…/ValleyCupTopTopFold — zero-axiom gate

Per-declaration zero-axiom gate for the two-floor peel induction of the top-top offset agreement (Piece II
tail): folding `topRegionOffsetAgrees_step` across a whole pure-cup boundary-chained block at two floors.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.topRegionOffsetAgrees_fold
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasCupTopTopFold

end FX1PolyAudit
