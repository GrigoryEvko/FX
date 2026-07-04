import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcChainedReconstruction

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcChainedReconstruction — zero-axiom gate

Per-declaration zero-axiom gate for the boundary-chain transfer along `SpineTraceEquiv`.  (The
chained head-extraction reduction formerly gated here duplicated the canonical
`ArcChainedExtraction` and is retired; see that twin for the canonical gates.)

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.spineBoundaryChained_iff_of_spineTraceEquiv

end FX1PolyAudit
