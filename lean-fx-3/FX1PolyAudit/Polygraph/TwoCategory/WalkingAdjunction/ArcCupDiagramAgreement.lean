import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupDiagramAgreement

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupDiagramAgreement — zero-axiom gate

Per-declaration zero-axiom gate for the partner cancel's diagram-agreement leg: the
machine-checked witness diagram agreement and the off-fused fresh partner agreement.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCupObstruction_freshDiagram_agrees
#assert_no_axioms FX1Poly.Polygraph.arcCupHeadFolded_offFusedPartner_agrees
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupDiagramAgreement

end FX1PolyAudit
