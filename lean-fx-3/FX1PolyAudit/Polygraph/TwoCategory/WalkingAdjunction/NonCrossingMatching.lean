import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.NonCrossingMatching

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/NonCrossingMatching — zero-axiom gate

Per-declaration zero-axiom gate for the planarity predicate on an extracted partner matching
(cup rung D2a-i): the crossing shape and its decision, the non-crossing predicate and its
decision, and the empty base case.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.PartnerCrosses
#assert_no_axioms FX1Poly.Polygraph.instDecidablePartnerCrosses
#assert_no_axioms FX1Poly.Polygraph.IsNonCrossing
#assert_no_axioms FX1Poly.Polygraph.instDecidableIsNonCrossing
#assert_no_axioms FX1Poly.Polygraph.isNonCrossing_nil

end FX1PolyAudit
