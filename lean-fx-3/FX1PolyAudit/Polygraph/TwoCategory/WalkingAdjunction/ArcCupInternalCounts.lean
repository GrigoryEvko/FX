import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupInternalCounts

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupInternalCounts — zero-axiom gate

Per-declaration zero-axiom gate for the composite internal-count lists through the cup
transport (peel campaign H, cup rung 6): the per-index count transport and the two list
correspondences (cup counts at head contribution 1, cap counts at head contribution 0),
both unconditional over the chained fragment.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCupCountTransport
#assert_no_axioms FX1Poly.Polygraph.arcCupHeadFolded_internalCupCountsCorr
#assert_no_axioms FX1Poly.Polygraph.arcCupHeadFolded_internalCapCountsCorr

end FX1PolyAudit
