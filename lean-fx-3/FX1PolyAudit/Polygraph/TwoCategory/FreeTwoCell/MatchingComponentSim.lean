import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingComponentSim

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingComponentSim — zero-axiom gate

Per-declaration zero-axiom gate for the corrected component-level simulation substrate: the join-transport
workhorse, the six-field invariant with its step / spine / cell preservation, the four-field rename relation,
the matching-extract invariance, and the component-level suffix-peel.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.componentView_unionFindJoin
#assert_no_axioms FX1Poly.Polygraph.MatchingComponentSim
#assert_no_axioms FX1Poly.Polygraph.stepCup_componentComm
#assert_no_axioms FX1Poly.Polygraph.stepCap_componentComm
#assert_no_axioms FX1Poly.Polygraph.stepAtom_componentComm
#assert_no_axioms FX1Poly.Polygraph.stepAtom_loopsEq_ofComponentView
#assert_no_axioms FX1Poly.Polygraph.matchingComponentSim_step
#assert_no_axioms FX1Poly.Polygraph.matchingComponentSim_processSpine
#assert_no_axioms FX1Poly.Polygraph.matchingComponentSim_runMatchingCell
#assert_no_axioms FX1Poly.Polygraph.MatchingComponentRenameRel
#assert_no_axioms FX1Poly.Polygraph.extractDiagram_of_matchingComponentRenameRel
#assert_no_axioms FX1Poly.Polygraph.matchingComponentRenameRel_of_matchingComponentSim
#assert_no_axioms FX1Poly.Polygraph.matchingComponentRenameRel_full_of_coreSim
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingComponentSimSubstrate

end FX1PolyAudit
