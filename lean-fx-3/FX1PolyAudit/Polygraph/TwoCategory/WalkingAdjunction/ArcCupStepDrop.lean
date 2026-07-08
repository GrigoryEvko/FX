import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupStepDrop

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupStepDrop — zero-axiom gate

Per-declaration zero-axiom gate for the top-of-stack cup-drop field legs: the internal cap-count list splices
`[0, 0]` at the window and the internal cup-count list splices `[1, 1]` at the window.  Also gates the round-2
general-state cup census locator: in an ARBITRARY `ArcStateFresh` preceding state the fresh cup reads `1` at each
window leg and contributes `0` delta at every old port (`= base`, the honesty-corrected below-window invariant).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.internalCapCounts_stepCupArc
#assert_no_axioms FX1Poly.Polygraph.internalCupCounts_stepCupArc
#assert_no_axioms FX1Poly.Polygraph.diagramPartner_stepCupArc
#assert_no_axioms FX1Poly.Polygraph.dropLastCup_arc_injective
#assert_no_axioms FX1Poly.Polygraph.generalStateCupInternalCupCount_atLeftLeg
#assert_no_axioms FX1Poly.Polygraph.generalStateCupInternalCupCount_atRightLeg
#assert_no_axioms FX1Poly.Polygraph.generalStateCupInternalCupCount_belowFreshLegIsBase
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupGeneralStateCensusLocator

end FX1PolyAudit
