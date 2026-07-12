import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidCanonicalWordMatrixToRecComb

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidCanonicalWordMatrixToRecCombAudit — zero-axiom gate for the
r18 T3 matrix->recComb leg of `CoxeterWordUnique`: `evalCell (permWord w1) = evalCell (permWord w2) -> recComb w1 =
recComb w2`, the composition of the r11 extractor+injective read-off with the r18 T1 canonicity.

Per-declaration `#assert_no_axioms` on the `positionsValid -> mentionsOnlyBelow` bridge, the matrix->recComb leg, the
braid-pair matrix-share, the non-vacuity fire, and the marker, PLUS independent (non-fuel) `#print axioms` on the leg,
the non-vacuity fire, and the marker. -/

namespace FX1PolyAudit

-- The validity bridge.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMentionsOnlyBelowOfPositionsValid

-- The matrix->recComb leg keystone.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRecCombEqOfEvalEq

-- The braid-pair matrix-share + the non-vacuity fire + the marker.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBraidPairEvalShared
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRecCombEqOfEvalEq_braidPair
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_hasMatrixToRecCombLeg

-- Independent (non-fuel) axiom prints on the leg, the non-vacuity fire, and the marker.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMentionsOnlyBelowOfPositionsValid
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRecCombEqOfEvalEq
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRecCombEqOfEvalEq_braidPair
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_hasMatrixToRecCombLeg

end FX1PolyAudit
