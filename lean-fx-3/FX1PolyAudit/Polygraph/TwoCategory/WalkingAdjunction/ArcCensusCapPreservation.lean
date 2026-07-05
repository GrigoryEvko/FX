import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCensusCapPreservation

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCensusCapPreservation — zero-axiom gate

Per-declaration zero-axiom gate for the cap census preservation (peel campaign H, cup rung
2d-ii): the window backmap package (node/validity/injectivity/window-missing), the join
membership dispatch, and the nine-branch preservation theorem.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.capEndTokenBackmap_node
#assert_no_axioms FX1Poly.Polygraph.capEndTokenBackmap_isValid
#assert_no_axioms FX1Poly.Polygraph.capEndTokenBackmap_injective
#assert_no_axioms FX1Poly.Polygraph.capEndTokenBackmap_missesLeftWindow
#assert_no_axioms FX1Poly.Polygraph.capEndTokenBackmap_missesRightWindow
#assert_no_axioms FX1Poly.Polygraph.sameComponent_unionFindJoin_dispatch
#assert_no_axioms FX1Poly.Polygraph.arcBoundaryCensus_stepCapArc

end FX1PolyAudit
