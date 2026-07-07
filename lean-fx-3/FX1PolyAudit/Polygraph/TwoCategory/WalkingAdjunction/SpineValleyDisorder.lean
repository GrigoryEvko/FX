import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyDisorder

/-! # FX1PolyAudit/…/SpineValleyDisorder — zero-axiom gate

Per-declaration zero-axiom gate for Piece I of the `MatchingReductsShareSpineTrace` beam: the valley-descent
DISORDER measure (inversion count of the cup/cap tags), the valley bridge (`spineDisorder = 0 ↔ valley`), the
COMMUTE / STRAIGHTEN strict-decrease facts, the redex-exposure brick, and the fuel-structural
`valleyDescentDriver` with its TERMINATION + VALLEY-CORRECTNESS (`valleyDescentDriver_reaches_valley` /
`spineValleyNormalize_isValley`).  Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.countBelowThreshold
#assert_no_axioms FX1Poly.Polygraph.countInversions
#assert_no_axioms FX1Poly.Polygraph.crossInversionCount
#assert_no_axioms FX1Poly.Polygraph.countBelowThreshold_zero
#assert_no_axioms FX1Poly.Polygraph.countBelowThreshold_append
#assert_no_axioms FX1Poly.Polygraph.countInversions_append
#assert_no_axioms FX1Poly.Polygraph.countBelowThreshold_swap_adjacent
#assert_no_axioms FX1Poly.Polygraph.countInversions_swap_adjacent_eq
#assert_no_axioms FX1Poly.Polygraph.countInversions_swap_adjacent_lt
#assert_no_axioms FX1Poly.Polygraph.countInversions_delete_head_lt
#assert_no_axioms FX1Poly.Polygraph.cupCapSlotValue
#assert_no_axioms FX1Poly.Polygraph.cupCapSlotValue_cup
#assert_no_axioms FX1Poly.Polygraph.cupCapSlotValue_cap
#assert_no_axioms FX1Poly.Polygraph.cupCapSlotValue_cap_lt_cup
#assert_no_axioms FX1Poly.Polygraph.spineDisorder
#assert_no_axioms FX1Poly.Polygraph.countBelowThreshold_one_of_allCups
#assert_no_axioms FX1Poly.Polygraph.countInversions_zero_of_allCups
#assert_no_axioms FX1Poly.Polygraph.countInversions_zero_of_valley
#assert_no_axioms FX1Poly.Polygraph.countInversions_pos_of_hasAdjacent
#assert_no_axioms FX1Poly.Polygraph.valley_of_disorder_zero
#assert_no_axioms FX1Poly.Polygraph.readbackSplit_exposesRedex
#assert_no_axioms FX1Poly.Polygraph.swapFirstCupCap
#assert_no_axioms FX1Poly.Polygraph.countBelowThreshold_swapFirstCupCap
#assert_no_axioms FX1Poly.Polygraph.isCapThenCupValley_cons_cons
#assert_no_axioms FX1Poly.Polygraph.swapFirstCupCap_disorder_lt
#assert_no_axioms FX1Poly.Polygraph.valleyDescentDriver
#assert_no_axioms FX1Poly.Polygraph.valleyDescentDriver_reaches_valley
#assert_no_axioms FX1Poly.Polygraph.spineValleyNormalize
#assert_no_axioms FX1Poly.Polygraph.spineValleyNormalize_isValley
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSpineValleyDisorderDriver

end FX1PolyAudit
