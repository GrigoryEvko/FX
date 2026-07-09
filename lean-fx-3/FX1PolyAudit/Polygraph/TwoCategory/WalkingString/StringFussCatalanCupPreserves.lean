import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringFussCatalanCupPreserves

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringFussCatalanCupPreserves — zero-axiom gate (FC-3b, CUP case)

Per-declaration zero-axiom gate for the CUP orientation-preservation heart: the root-below-bound facts, the fresh-leg
roots after the join, the fresh-pair isolation (same-component with each other, distinct from every old wire), the
cup-splice wire/label reads, the cup links equality, the both-old reduction, and the CUP case of the orientation
discipline (`stringOrientationDiscipline_stepCup`).  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringUnionFindRoot_lt_of_linksBelow
#assert_no_axioms FX1Poly.Polygraph.stringUnionFindRootOf_lt_of_linksBelow
#assert_no_axioms FX1Poly.Polygraph.stringFreshRightLeg_parentless_cons
#assert_no_axioms FX1Poly.Polygraph.stringUnionFindRootOf_freshRightLeg
#assert_no_axioms FX1Poly.Polygraph.stringUnionFindRootOf_freshLeftLeg
#assert_no_axioms FX1Poly.Polygraph.stringFreshPair_sameComponent
#assert_no_axioms FX1Poly.Polygraph.stringFreshLeg_not_sameComponent_old
#assert_no_axioms FX1Poly.Polygraph.stringOld_not_sameComponent_freshLeg
#assert_no_axioms FX1Poly.Polygraph.stringStepCup_openWires_read_below
#assert_no_axioms FX1Poly.Polygraph.stringStepCup_openWires_read_blockLow
#assert_no_axioms FX1Poly.Polygraph.stringStepCup_openWires_read_blockHigh
#assert_no_axioms FX1Poly.Polygraph.stringStepCup_openWires_read_above
#assert_no_axioms FX1Poly.Polygraph.stringAdvanceLabels_read_below
#assert_no_axioms FX1Poly.Polygraph.stringAdvanceLabels_read_blockLow
#assert_no_axioms FX1Poly.Polygraph.stringAdvanceLabels_read_blockHigh
#assert_no_axioms FX1Poly.Polygraph.stringAdvanceLabels_read_above
#assert_no_axioms FX1Poly.Polygraph.stringStepCup_links_eq
#assert_no_axioms FX1Poly.Polygraph.stringCupOrient_oldPair
#assert_no_axioms FX1Poly.Polygraph.stringOrientationDiscipline_stepCup

end FX1PolyAudit
