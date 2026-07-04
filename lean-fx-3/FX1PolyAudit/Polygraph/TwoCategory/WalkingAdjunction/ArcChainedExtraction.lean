import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcChainedExtraction

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcChainedExtraction — zero-axiom gate

Per-declaration zero-axiom gate for the chained assembly: the chained head-extraction matching and the
seed reduction of `ArcCellReconstruction adjunctionModeSignature` to the single chained obligation.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.spineTraceMatched_of_chainedHeadExtraction
#assert_no_axioms FX1Poly.Polygraph.adjunctionArcCellReconstruction_of_chainedExtraction

end FX1PolyAudit
