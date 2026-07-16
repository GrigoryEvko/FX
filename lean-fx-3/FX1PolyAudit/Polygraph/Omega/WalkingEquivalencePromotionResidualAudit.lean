import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingEquivalencePromotionResidual

/-! # FX1PolyAudit.Polygraph.Omega.WalkingEquivalencePromotionResidualAudit — zero-axiom gate for the
narrowed WP-EQUIV #2068 promotion residual (r2).

Per-declaration `#assert_no_axioms` on the whiskered-left-triangle collapses (the recon recipe's opening move),
the right inverse of the right defect (the dual of the shipped left inverse), the two-sided-inverse bundle, the
forward-round-trip non-vacuity witness, and the wall-narrowing honesty markers. -/

namespace FX1PolyAudit

-- the left triangle survives whiskering by g (the recon recipe's opening move)
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivLeftTriangleWhiskeredLeftCollapses
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivLeftTriangleWhiskeredRightCollapses

-- the right defect is a genuine two-sided iso
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivRightDefect_rightInverse
#assert_no_axioms FX1Poly.Polygraph.Omega.WalkingEquivRightDefectTwoSidedInverseStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivRightDefect_twoSidedInverse

-- the forward-round-trip non-vacuity witness
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivRightDefectForwardRoundTrip_notLiterallyId

-- the wall-narrowing honesty markers
#assert_no_axioms FX1Poly.Polygraph.Omega.fxEquiv_promotionWhiskeredLeftTriangleCollapsesMechanized
#assert_no_axioms FX1Poly.Polygraph.Omega.fxEquiv_promotionRightDefectTwoSidedIsoMechanized
#assert_no_axioms FX1Poly.Polygraph.Omega.fxEquiv_promotionResidualNarrowedToInterchangeBracketing

end FX1PolyAudit
