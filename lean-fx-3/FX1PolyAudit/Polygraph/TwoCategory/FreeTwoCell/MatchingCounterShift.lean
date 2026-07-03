import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingCounterShift

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingCounterShift — zero-axiom gate

Per-declaration zero-axiom gate for the counter-shift simulation: the shifted cup leg, the
arity-dispatched component view, step stability, the boundary-disciplined fold, the
zero-boundary read-off, the empty-boundary counter-shift bridge, and the honesty marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stepCup_componentComm_ofShift
#assert_no_axioms FX1Poly.Polygraph.stepAtom_componentComm_ofShift
#assert_no_axioms FX1Poly.Polygraph.matchingShiftSim_step_ofInRange
#assert_no_axioms FX1Poly.Polygraph.matchingShiftSim_processSpine_ofBoundaryDiscipline
#assert_no_axioms FX1Poly.Polygraph.extractDiagram_zeroBoundary_ofShiftSim
#assert_no_axioms FX1Poly.Polygraph.extractAfterProcessing_emptyBoundary_counterShift
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasEmptyBoundaryCounterShiftBridge

end FX1PolyAudit
