import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupHeadDiagram

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupHeadDiagram — zero-axiom gate

Per-declaration zero-axiom gate for the assembled cup-head diagram correspondence (peel
campaign H, cup rung 5): the transported partner list and the composite extract's
`DiagramType` equality.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCupHeadFolded_partnerListCorr
#assert_no_axioms FX1Poly.Polygraph.arcCupHeadFolded_extractDiagram

end FX1PolyAudit
