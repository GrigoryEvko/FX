import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcStateAgreement

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcStateAgreement — zero-axiom gate

Per-declaration zero-axiom gate for the state-agreement vehicle: the join partition-congruence
crux, the three step-preservation lemmas, the spine/cell folds, the partition-level count
congruence, and the `SameArcPartition` / equal-extract readouts.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.isSameComponent_unionFindJoin_congr
#assert_no_axioms FX1Poly.Polygraph.arcStateAgree_stepCupArc
#assert_no_axioms FX1Poly.Polygraph.arcStateAgree_stepCapArc
#assert_no_axioms FX1Poly.Polygraph.arcStateAgree_stepArcAtom
#assert_no_axioms FX1Poly.Polygraph.arcStateAgree_processArcSpine
#assert_no_axioms FX1Poly.Polygraph.arcStateAgree_runArcCell
#assert_no_axioms FX1Poly.Polygraph.countEventsInRoot_atPortRoot_congr
#assert_no_axioms FX1Poly.Polygraph.sameArcPartition_of_arcStateAgree
#assert_no_axioms FX1Poly.Polygraph.extractArc_eq_of_arcStateAgree

end FX1PolyAudit
