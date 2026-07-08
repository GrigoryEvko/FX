import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupDisjointTailJoinInvariance

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupDisjointTailJoinInvariance — zero-axiom gate

Per-declaration zero-axiom gate for the JOIN side of the head-cup census read-off lifted past an ARBITRARY
window-disjoint tail: `isSameComponent_foldJoins_offProbe` (the FM Prop. 4.2.4 "stable under pushouts by
induction on `k`" step) and its leg-strand-zone corollary `isSameComponent_foldJoins_offZone`, generalizing
the shipped single-cap `cupEventComponent_reduce_pastDisjointCap` to arbitrary tail length.  The public
assertions transitively cover `foldJoins` and `isUnionFindForest_foldJoins`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.isUnionFindForest_foldJoins
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_foldJoins_offProbe
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_foldJoins_offZone
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupDisjointTailJoinInvariance

end FX1PolyAudit
