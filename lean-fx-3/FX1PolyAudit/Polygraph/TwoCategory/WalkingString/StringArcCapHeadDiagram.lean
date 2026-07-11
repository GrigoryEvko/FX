import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcCapHeadDiagram

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringArcCapHeadDiagram — zero-axiom gate
(FC-3 r21, THE 110-PERCENT GRIND — the cap-head `DiagramType` correspondence, pure-cap)

Per-declaration zero-axiom gate for the ported cap-head boundary-diagram correspondence.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringArcCapHeadFolded_extractDiagram
#assert_no_axioms FX1Poly.Polygraph.fxString_hasArcCapHeadDiagramLeg

end FX1PolyAudit
