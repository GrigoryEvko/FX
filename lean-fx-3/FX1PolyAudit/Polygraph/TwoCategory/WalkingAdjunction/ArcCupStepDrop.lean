import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupStepDrop

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupStepDrop — zero-axiom gate

Per-declaration zero-axiom gate for the top-of-stack cup-drop field legs: the internal cap-count list splices
`[0, 0]` at the window and the internal cup-count list splices `[1, 1]` at the window.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.internalCapCounts_stepCupArc
#assert_no_axioms FX1Poly.Polygraph.internalCupCounts_stepCupArc
#assert_no_axioms FX1Poly.Polygraph.diagramPartner_stepCupArc

end FX1PolyAudit
