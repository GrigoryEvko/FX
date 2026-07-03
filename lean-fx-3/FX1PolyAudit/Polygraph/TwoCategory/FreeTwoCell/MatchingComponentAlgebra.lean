import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingComponentAlgebra

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingComponentAlgebra — zero-axiom gate

Per-declaration zero-axiom gate for the same-component join algebra: the equivalence-relation kit, the
join-homogeneity of the fold's link updates, the flat-disjunction characterization of the join, and the
honesty marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Tier0.isSameComponent_self
#assert_no_axioms FX1Poly.Tier0.isSameComponent_symm
#assert_no_axioms FX1Poly.Tier0.isSameComponent_trans
#assert_no_axioms FX1Poly.Tier0.unionFindJoin_ofSameComponent
#assert_no_axioms FX1Poly.Tier0.stepCap_links_eq_unionFindJoin
#assert_no_axioms FX1Poly.Tier0.isSameComponent_unionFindJoin
#assert_no_axioms FX1Poly.Tier0.isSameComponent_flip
#assert_no_axioms FX1Poly.Tier0.isSameComponent_unionFindJoin_ofBase
#assert_no_axioms FX1Poly.Tier0.isSameComponent_unionFindJoin_joined
#assert_no_axioms FX1Poly.Tier0.isSameComponent_unionFindJoin_lift
#assert_no_axioms FX1Poly.Tier0.isSameComponent_acrossSwappedJoins
#assert_no_axioms FX1Poly.Tier0.isSameComponent_unionFindJoin_swap
#assert_no_axioms FX1Poly.Tier0.stepCap_loops_eq_addIncrement
#assert_no_axioms FX1Poly.Tier0.sameComponentIncrement_unionFindJoin_swap
#assert_no_axioms FX1Poly.Tier0.fxMode_hasSameComponentJoinAlgebra

end FX1PolyAudit
