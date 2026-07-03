import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingJoinEventExchange

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingJoinEventExchange — zero-axiom gate

Per-declaration zero-axiom gate for the block exchange of join-event traces: the forest
preservation of the event fold, the view/count congruences in the links argument, the list-level
universal property (monotone extension / completeness / elimination), the mem-equivalence view
invariance with its block-swap and fold-join-commute corollaries, the single-event and cross-block
count exchanges, the count-side block swap, and the honesty marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.isUnionFindForest_applyJoinEvents
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_unionFindJoin_congr
#assert_no_axioms FX1Poly.Polygraph.componentView_applyJoinEvents_congr
#assert_no_axioms FX1Poly.Polygraph.countJoinEventLoops_congr
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_applyJoinEvents_ofBase
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_applyJoinEvents_ofMem
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_applyJoinEvents_lift
#assert_no_axioms FX1Poly.Polygraph.componentView_applyJoinEvents_ofMemEquiv
#assert_no_axioms FX1Poly.Polygraph.componentView_applyJoinEvents_append_comm
#assert_no_axioms FX1Poly.Polygraph.componentView_applyJoinEvents_joinRight
#assert_no_axioms FX1Poly.Polygraph.countJoinEventLoops_singleJoinExchange
#assert_no_axioms FX1Poly.Polygraph.countJoinEventLoops_crossExchange
#assert_no_axioms FX1Poly.Polygraph.countJoinEventLoops_append_comm
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingJoinEventBlockExchange

end FX1PolyAudit
