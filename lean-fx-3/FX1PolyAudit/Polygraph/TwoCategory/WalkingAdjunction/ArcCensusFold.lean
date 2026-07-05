import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCensusFold

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCensusFold — zero-axiom gate

Per-declaration zero-axiom gate for the census fold transport (peel campaign H, cup rung
2d-iv): the per-atom census step, the whole-fold transport over boundary-chained spines, and
the canonical-seed capstone.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcBoundaryCensus_stepArcAtom
#assert_no_axioms FX1Poly.Polygraph.arcBoundaryCensus_processArcSpine_ofChained
#assert_no_axioms FX1Poly.Polygraph.arcBoundaryCensus_ofChainedSpineList

end FX1PolyAudit
