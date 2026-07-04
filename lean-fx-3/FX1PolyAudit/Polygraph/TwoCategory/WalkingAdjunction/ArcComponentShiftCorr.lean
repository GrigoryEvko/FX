import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcComponentShiftCorr

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcComponentShiftCorr — zero-axiom gate

Per-declaration zero-axiom gate for the component-leg invariant of the head cancellation
(peel campaign H, rung 2 core): the join transport and the corresponding-join preservation.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.isSameComponent_unionFindJoin_mapTransport
#assert_no_axioms FX1Poly.Polygraph.arcComponentShiftCorr_correspondingJoin

end FX1PolyAudit
