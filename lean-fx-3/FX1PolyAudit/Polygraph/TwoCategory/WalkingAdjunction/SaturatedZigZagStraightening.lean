import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedZigZagStraightening

/-! # FX1PolyAudit/…/SaturatedZigZagStraightening — zero-axiom gate

Per-declaration zero-axiom gate for the ZIG-ZAG straightening in arbitrary vertical context — the
machine-checked refutation that the free partial-overlap obstruction transfers to `SaturatedTwoCellConv`.
The master move `zigzagStraightensInVcompContext` and its prefix/suffix/seed/staircase instances must be
free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.zigzagStraightensInVcompContext
#assert_no_axioms FX1Poly.Polygraph.zigzagStraightensPrefix
#assert_no_axioms FX1Poly.Polygraph.zigzagStraightensSuffix
#assert_no_axioms FX1Poly.Polygraph.minimalZigZagStraightens
#assert_no_axioms FX1Poly.Polygraph.seedLeftSnakeStraightensInContext
#assert_no_axioms FX1Poly.Polygraph.seedRightSnakeStraightensInContext
#assert_no_axioms FX1Poly.Polygraph.staircaseZigZagStraightensInContext
#assert_no_axioms FX1Poly.Polygraph.whiskeredZigZagCollapses
#assert_no_axioms FX1Poly.Polygraph.seedLeftSnakeStraightensInFullContext
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasZigZagStraightensInContext

end FX1PolyAudit
