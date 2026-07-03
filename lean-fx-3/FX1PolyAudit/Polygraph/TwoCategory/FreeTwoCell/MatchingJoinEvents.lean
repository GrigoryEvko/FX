import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingJoinEvents

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingJoinEvents — zero-axiom gate

Per-declaration zero-axiom gate for the join-event trace: the out-of-support root identities, the
event definitions, the trace-composition lemmas, the links/loops faithfulness theorems at atom, spine,
and cell granularity, the sigma-equivariance of the event fold, and the honesty marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.unionFindParent_eq_none_ofFresh
#assert_no_axioms FX1Poly.Polygraph.unionFindRootOf_eq_self_ofFresh
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_freshPair_eq_false
#assert_no_axioms FX1Poly.Polygraph.stepAtomJoinEvents
#assert_no_axioms FX1Poly.Polygraph.applyJoinEvents
#assert_no_axioms FX1Poly.Polygraph.countJoinEventLoops
#assert_no_axioms FX1Poly.Polygraph.spineJoinEvents
#assert_no_axioms FX1Poly.Polygraph.stepAtomJoinEvents_ofCupArity
#assert_no_axioms FX1Poly.Polygraph.stepAtomJoinEvents_ofCapArity
#assert_no_axioms FX1Poly.Polygraph.applyJoinEvents_append
#assert_no_axioms FX1Poly.Polygraph.countJoinEventLoops_append
#assert_no_axioms FX1Poly.Polygraph.stepAtom_links_eq_applyJoinEvents
#assert_no_axioms FX1Poly.Polygraph.stepAtom_loops_eq_addJoinEventLoops
#assert_no_axioms FX1Poly.Polygraph.processSpine_links_eq_applyJoinEvents
#assert_no_axioms FX1Poly.Polygraph.processSpine_loops_eq_addJoinEventLoops
#assert_no_axioms FX1Poly.Polygraph.runMatchingCell_links_eq_applyJoinEvents
#assert_no_axioms FX1Poly.Polygraph.runMatchingCell_loops_eq_addJoinEventLoops
#assert_no_axioms FX1Poly.Polygraph.componentView_applyJoinEvents
#assert_no_axioms FX1Poly.Polygraph.countJoinEventLoops_map_congr
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingJoinEventReification

end FX1PolyAudit
