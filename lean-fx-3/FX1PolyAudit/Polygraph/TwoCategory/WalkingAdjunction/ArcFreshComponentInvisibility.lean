import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcFreshComponentInvisibility

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcFreshComponentInvisibility — zero-axiom gate

Per-declaration zero-axiom gate for the fresh-join transparency toolkit (peel campaign H, cup
rung 2d-ii prep): fresh nodes are component-invisible to bounded probes, off-probes joins are
transparent, and the cap/cup step-level peels.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.isSameComponent_offFreshNode
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_unionFindJoin_offProbes
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_stepCapArc_oldProbes
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_stepCupArc_oldProbes

end FX1PolyAudit
