import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcNonCrossingInvariant

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcNonCrossingInvariant — zero-axiom gate

Per-declaration zero-axiom gate for the state-level planarity invariant of the arc fold (cup rung
D2a-ii): the token-side cyclic boundary position, the non-crossing invariant, and its truth at the
fresh seed.  The private range/empty-link plumbing and the bottom-top arc helper are covered
transitively through `arcNonCrossing_initial`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcEndTokenPosition
#assert_no_axioms FX1Poly.Polygraph.ArcNonCrossing
#assert_no_axioms FX1Poly.Polygraph.arcNonCrossing_initial

end FX1PolyAudit
