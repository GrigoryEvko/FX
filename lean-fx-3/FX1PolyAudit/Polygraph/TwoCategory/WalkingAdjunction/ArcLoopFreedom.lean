import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcLoopFreedom

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcLoopFreedom — zero-axiom gate

Per-declaration zero-axiom gate for the loop-freedom consequence (peel campaign C, rung 3):
the disciplined-cap refutation, the per-atom step, the whole-fold constancy, the
canonical-seed capstone, and the extracted-diagram circle-freedom.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stepCapArc_loops_ofDisciplined
#assert_no_axioms FX1Poly.Polygraph.stepArcAtom_loops_ofDisciplined
#assert_no_axioms FX1Poly.Polygraph.processArcSpine_loops_ofChained
#assert_no_axioms FX1Poly.Polygraph.arcFoldLoops_zero_ofChainedSpineList
#assert_no_axioms FX1Poly.Polygraph.arcStructureOfSpineList_diagramLoops_zero_ofChained

end FX1PolyAudit
