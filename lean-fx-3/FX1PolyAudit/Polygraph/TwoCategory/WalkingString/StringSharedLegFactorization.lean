import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSharedLegFactorization

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringSharedLegFactorization — zero-axiom gate (FC-3 r5, B1)

Per-declaration zero-axiom gate for the WORD-indexed shared-leg (zig-zag STRAIGHTEN) factorization: the
colour-blind width dispatch, the generic snake reconnect and mode-clash nodes, the genuinely-new same-colour
lemma, the STRAIGHTEN endpoint identification, and the two non-vacuity witnesses.  Must be free of `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringNatWindowDistance_eq_one_of_zigZag
#assert_no_axioms FX1Poly.Polygraph.stringZigZagSharedLeg_widthDichotomy
#assert_no_axioms FX1Poly.Polygraph.sharedLegSnakeReconnect
#assert_no_axioms FX1Poly.Polygraph.sharedLegModeClash
#assert_no_axioms FX1Poly.Polygraph.stringSharedLegForcesSameColour
#assert_no_axioms FX1Poly.Polygraph.stringCupCapDeletionReconnects
#assert_no_axioms FX1Poly.Polygraph.stringSharedLegReconnect_genuineSnake
#assert_no_axioms FX1Poly.Polygraph.stringSharedLegMixedPairExcluded
#assert_no_axioms FX1Poly.Polygraph.fxString_hasSharedLegFactor

end FX1PolyAudit
