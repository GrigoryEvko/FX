import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ClassSaturation

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/ClassSaturation — zero-axiom gate

Per-declaration zero-axiom gate for the BFS class-saturation worker and its safety
half: growth, seed containment, and chain-reachability soundness.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.listMemDecidable
#assert_no_axioms FX1Poly.Polygraph.listMemFilterInverted
#assert_no_axioms FX1Poly.Polygraph.freshSwapSuccessors
#assert_no_axioms FX1Poly.Polygraph.saturateClassWorker
#assert_no_axioms FX1Poly.Polygraph.saturateClass
#assert_no_axioms FX1Poly.Polygraph.saturateClassWorker_keepsVisited
#assert_no_axioms FX1Poly.Polygraph.saturateClass_containsSeed
#assert_no_axioms FX1Poly.Polygraph.freshSwapSuccessors_areReachable
#assert_no_axioms FX1Poly.Polygraph.saturateClassWorker_isSound
#assert_no_axioms FX1Poly.Polygraph.saturateClass_isSound

end FX1PolyAudit
