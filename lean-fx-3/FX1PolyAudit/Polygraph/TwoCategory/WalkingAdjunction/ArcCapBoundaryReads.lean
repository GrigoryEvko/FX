import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapBoundaryReads

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCapBoundaryReads — zero-axiom gate

Per-declaration zero-axiom gate for the cap-head composite boundary reads (peel campaign H,
rung E-3, part 1): the two generic zone correspondences, their folded-state corollaries,
and the total-port count fact.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCapBoundaryRead_belowWindow
#assert_no_axioms FX1Poly.Polygraph.arcCapBoundaryRead_atOrPastWindow
#assert_no_axioms FX1Poly.Polygraph.arcCapHeadFolded_boundaryRead_belowWindow
#assert_no_axioms FX1Poly.Polygraph.arcCapHeadFolded_boundaryRead_atOrPastWindow
#assert_no_axioms FX1Poly.Polygraph.arcCapHeadFolded_totalPorts

end FX1PolyAudit
