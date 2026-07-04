import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcChainedReconstruction

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcChainedReconstruction — zero-axiom gate

Per-declaration zero-axiom gate for the chained reconstruction reduction: the boundary-chain
transfer along `SpineTraceEquiv`, the chained head-extraction assembly, and the adjunction
cell-reconstruction gate.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.spineBoundaryChained_iff_of_spineTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.spineTraceMatched_of_chainedHeadExtraction
#assert_no_axioms FX1Poly.Polygraph.arcCellReconstruction_adjunction_of_chainedExtraction

end FX1PolyAudit
