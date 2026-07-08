import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingJoinEventOffConfined

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingJoinEventOffConfined — zero-axiom gate

Per-declaration zero-axiom gate for the CONVERSE (support-confinement) half of the same-component
window-locality: the single-join off-support equality, the single-join detachment-preservation step,
the event-fold converse, and the honesty marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.isSameComponent_unionFindJoin_eq_ofFirstDisconnected
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_unionFindJoin_disconnected_preserved
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_applyJoinEvents_offConfined
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasOffConfinedConverse

end FX1PolyAudit
