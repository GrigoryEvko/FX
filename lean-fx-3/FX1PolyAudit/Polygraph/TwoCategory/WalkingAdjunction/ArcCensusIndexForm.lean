import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCensusIndexForm

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCensusIndexForm — zero-axiom gate

Per-declaration zero-axiom gate for the census index form (peel campaign H, cup rung 2d-v
opener): the abstract-boundary index form and the canonical-extraction-boundary instance.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcBoundaryCensus_indexForm
#assert_no_axioms FX1Poly.Polygraph.arcBoundaryCensus_boundaryNodes

end FX1PolyAudit
