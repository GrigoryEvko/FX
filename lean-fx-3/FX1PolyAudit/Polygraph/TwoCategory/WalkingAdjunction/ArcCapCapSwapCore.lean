import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapCapSwapCore

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCapCapSwapCore — zero-axiom gate

Per-declaration zero-axiom gate for the cap-cap partition-simulation core's wire leg.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.capCapSwap_openMap
#assert_no_axioms FX1Poly.Polygraph.natBeq_self
#assert_no_axioms FX1Poly.Polygraph.natBeq_comm
#assert_no_axioms FX1Poly.Polygraph.boolFalseAnd
#assert_no_axioms FX1Poly.Polygraph.boolOrFalse
#assert_no_axioms FX1Poly.Polygraph.boolTrueOr
#assert_no_axioms FX1Poly.Polygraph.boolFalseOr
#assert_no_axioms FX1Poly.Polygraph.boolTrueAnd
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_unionFindJoin_split

end FX1PolyAudit
