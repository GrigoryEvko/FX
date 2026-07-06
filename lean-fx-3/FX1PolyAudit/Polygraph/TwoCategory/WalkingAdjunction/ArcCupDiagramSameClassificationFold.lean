import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupDiagramSameClassificationFold

/-! # FX1PolyAudit/…/ArcCupDiagramSameClassificationFold — zero-axiom gate

Per-declaration zero-axiom gate for the diagram-leg fold from per-index `sameClassification`: the leg-
attachment classifier predicate and the composition
`arcCupFoldedDiagramPartnerList_agrees_ofSameClassification` (the shipped per-index agreement folded over
the composite range, with the fresh-length bridge) must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCupFreshPartnerLandsOnWindowLeg
#assert_no_axioms FX1Poly.Polygraph.arcCupFoldedDiagramPartnerList_agrees_ofSameClassification
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupDiagramSameClassificationFold

end FX1PolyAudit
