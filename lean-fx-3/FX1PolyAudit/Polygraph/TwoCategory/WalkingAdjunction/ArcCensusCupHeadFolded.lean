import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCensusCupHeadFolded

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCensusCupHeadFolded — zero-axiom gate

Per-declaration zero-axiom gate for the folded census instances (peel campaign H, cup rung
2d-v): the census at the cup-head folded composite and the ready-to-dispatch partner pins at
both states of the cup geometry.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcBoundaryCensus_cupHeadFolded
#assert_no_axioms FX1Poly.Polygraph.arcCupHeadFolded_partner_ofSameComponent
#assert_no_axioms FX1Poly.Polygraph.arcFreshFolded_partner_ofSameComponent

end FX1PolyAudit
