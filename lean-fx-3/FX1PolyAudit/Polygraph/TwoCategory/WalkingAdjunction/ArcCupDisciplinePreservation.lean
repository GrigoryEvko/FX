import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupDisciplinePreservation

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupDisciplinePreservation — zero-axiom gate

Per-declaration zero-axiom gate for the cup preservation of the typed-ends discipline (peel
campaign C, rung 2b): the in-range read bound, the old-node component transfer, the two
leg-vs-old refutations, and the preservation theorem.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.natListGetAt_lt_ofInRange
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_stepCupArc_oldNodes
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_stepCupArc_oldLeg_eq_false
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_stepCupArc_legOld_eq_false
#assert_no_axioms FX1Poly.Polygraph.arcOpenEndsDiscipline_stepCupArc

end FX1PolyAudit
