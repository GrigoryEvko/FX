import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingComponentSimInRange

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingComponentSimInRange — zero-axiom gate

Per-declaration zero-axiom gate for the sentinel-free component-sim chain: the two in-range
read-site clones, step stability, the boundary-disciplined fold, the rename-relation read-off,
the sentinel-free suffix peel, and the honesty marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stepAtom_componentComm_ofInRange
#assert_no_axioms FX1Poly.Polygraph.stepAtom_loopsEq_ofInRange
#assert_no_axioms FX1Poly.Polygraph.matchingComponentSim_step_ofInRange
#assert_no_axioms FX1Poly.Polygraph.matchingComponentSim_processSpine_ofBoundaryDiscipline
#assert_no_axioms FX1Poly.Polygraph.matchingComponentRenameRel_of_matchingComponentSim_ofInRange
#assert_no_axioms FX1Poly.Polygraph.matchingComponentRenameRel_ofCoreSim_boundaryDiscipline
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSentinelFreeComponentSim

end FX1PolyAudit
