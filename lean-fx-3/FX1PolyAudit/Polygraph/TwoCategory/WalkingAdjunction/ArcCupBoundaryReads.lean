import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupBoundaryReads

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupBoundaryReads — zero-axiom gate

Per-declaration zero-axiom gate for the cup-head composite boundary reads (peel campaign
H, cup rung 1): the two generic zone correspondences, their folded-state corollaries, and
the fresh-side two-extra-ports count fact.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCupBoundaryRead_belowWindow
#assert_no_axioms FX1Poly.Polygraph.arcCupBoundaryRead_atOrPastWindow
#assert_no_axioms FX1Poly.Polygraph.arcCupHeadFolded_boundaryRead_belowWindow
#assert_no_axioms FX1Poly.Polygraph.arcCupHeadFolded_boundaryRead_atOrPastWindow
#assert_no_axioms FX1Poly.Polygraph.arcCupHeadFolded_totalPorts

end FX1PolyAudit
