import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcComponentShiftStep

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcComponentShiftStep — zero-axiom gate

Per-declaration zero-axiom gate for the component-leg step lemmas of the head cancellation
(peel campaign H, rung 2b): the cup step, the cap step, and the boundary-tracked per-atom
dispatch.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcComponentShiftCorr_stepCupArc
#assert_no_axioms FX1Poly.Polygraph.arcComponentShiftCorr_stepCapArc
#assert_no_axioms FX1Poly.Polygraph.arcComponentShiftCorr_stepArcAtom

end FX1PolyAudit
