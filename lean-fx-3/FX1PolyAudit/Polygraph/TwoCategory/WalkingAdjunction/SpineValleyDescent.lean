import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyDescent

/-! # FX1PolyAudit/…/SpineValleyDescent — zero-axiom gate

Per-declaration zero-axiom gate for the two VALLEY-NORMALIZATION DESCENT invariants — `matchingOf` preserved by
every shipped straighten/commute move (the descent's fixed lexicographic component, from the boundary-disciplined
soundness) and `generatorCount` dropping by exactly the collapsed snake's count (the strictly-decreasing
component).  Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.matchingOf_invariant_ofSaturatedConv
#assert_no_axioms FX1Poly.Polygraph.matchingOf_invariant_underZigzagStraighten
#assert_no_axioms FX1Poly.Polygraph.matchingOf_invariant_underWhiskeredZigzag
#assert_no_axioms FX1Poly.Polygraph.matchingOf_invariant_underDisjointCommute
#assert_no_axioms FX1Poly.Polygraph.generatorCount_zigzagStraighten_drop
#assert_no_axioms FX1Poly.Polygraph.generatorCount_whiskeredZigzag_drop
#assert_no_axioms FX1Poly.Polygraph.generatorCount_disjointCommute_drop
#assert_no_axioms FX1Poly.Polygraph.generatorCount_zigzagStraighten_strictDrop
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSpineValleyDescentInvariants

end FX1PolyAudit
