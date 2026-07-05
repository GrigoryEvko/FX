import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCensusCupPreservation

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCensusCupPreservation — zero-axiom gate

Per-declaration zero-axiom gate for the cup census preservation (peel campaign H, cup rung
2d-iii): the splice backmap package (node/validity/injectivity on the old zone) and the full
old/leg dispatch preservation theorem.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.cupEndTokenBackmap_node
#assert_no_axioms FX1Poly.Polygraph.cupEndTokenBackmap_isValid
#assert_no_axioms FX1Poly.Polygraph.cupEndTokenBackmap_injective
#assert_no_axioms FX1Poly.Polygraph.arcBoundaryCensus_stepCupArc

end FX1PolyAudit
