import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingEquivalencePromotionParityObstruction

/-! # FX1PolyAudit.Polygraph.Omega.WalkingEquivalencePromotionParityObstructionAudit — zero-axiom gate for
the WP-EQUIV #2068 B3 promotion adjudication (r3).

Per-declaration `#assert_no_axioms` on the parity carrier, the flagged fold, the row-conservation lemmas, the
absorber, the two separating contribution tables, the separation pins, the two refutations (hypothesis
uninhabited over bare; idempotency + right triangle underivable even with the left-triangle row adjoined),
the vacuously-shipped guarded theorems, and the honesty markers — plus independent `#print axioms` on the
headline refutations and the shipped guarded theorem. -/

namespace FX1PolyAudit

-- the parity carrier
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivParityAdd
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivParityAdd_assoc
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivParityAdd_comm
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivParityAdd_falseRight
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivParityAdd_self

-- the flagged generator parity fold
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivFlaggedGenParity

-- row conservation
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivFlaggedGenParity_ofStrictAxiom
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivFlaggedGenParity_ofCancellation
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivFlaggedGenParityAbsorbs
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivFlaggedGenParity_ofBaseRel

-- the two separating contribution tables
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivIsEtaFamilyLabel
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivEtaRightWhiskerOnlyContribution
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivEtaLeftWhiskerOnlyContribution
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivEtaRightWhiskerOnlyContribution_pairsEta
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivEtaRightWhiskerOnlyContribution_pairsEps
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivEtaLeftWhiskerOnlyContribution_pairsEta
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivEtaLeftWhiskerOnlyContribution_pairsEps

-- the kernel-computed separation pins
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivLeftTriangleLeg_rightSlotParityPin
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivIdF_rightSlotParityPin
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivRightTriangleLeg_leftSlotParityPin
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivDoubledRightTriangleLeg_leftSlotParityPin
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivIdG_leftSlotParityPin

-- refutation 1: the hypothesis is uninhabited over the bare relation
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivLeftTriangle_notDerivableOverBareRel

-- the guarded theorems, shipped vacuously
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivIdempotencyFromLeftTriangle
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivRightTriangleFromLeftTriangle

-- refutation 2: the non-vacuous adjudication over the adjoined relation
#assert_no_axioms FX1Poly.Polygraph.Omega.WalkingEquivLeftTriangleOnlyRow
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivLeftTriangleAdjoinedRel
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivLeftTriangle_derivableOverAdjoinedRel
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivEtaLeftWhiskerOnly_conservedByLeftTriangleRow
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivFlaggedGenParity_ofAdjoinedRel
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivIdempotency_notDerivableEvenWithLeftTriangleRow
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivRightTriangle_notDerivableEvenWithLeftTriangleRow
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivIdempotency_notDerivableOverBareRel

-- the honesty markers
#assert_no_axioms FX1Poly.Polygraph.Omega.fxEquiv_promotionIdempotencyFromLeftTriangleTheoremShippedVacuously
#assert_no_axioms FX1Poly.Polygraph.Omega.fxEquiv_promotionInterchangeBracketingRefuted
#assert_no_axioms FX1Poly.Polygraph.Omega.fxEquiv_promotionOverWhiskerUnitorScopeOpen

-- independent axiom prints on the headlines (must print "does not depend on any axioms")
#print axioms FX1Poly.Polygraph.Omega.walkingEquivLeftTriangle_notDerivableOverBareRel
#print axioms FX1Poly.Polygraph.Omega.walkingEquivIdempotencyFromLeftTriangle
#print axioms FX1Poly.Polygraph.Omega.walkingEquivRightTriangleFromLeftTriangle
#print axioms FX1Poly.Polygraph.Omega.walkingEquivIdempotency_notDerivableEvenWithLeftTriangleRow
#print axioms FX1Poly.Polygraph.Omega.walkingEquivRightTriangle_notDerivableEvenWithLeftTriangleRow

end FX1PolyAudit
