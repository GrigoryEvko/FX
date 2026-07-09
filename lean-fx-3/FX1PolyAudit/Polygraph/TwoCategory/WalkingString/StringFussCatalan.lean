import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringFussCatalan

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringFussCatalan — zero-axiom gate (FC-0)

Per-declaration zero-axiom gate for the Fuss–Catalan Phase-0 foundations: the carrier (`FcArc`, `FcDiagram`,
`fcDiagramOf`, the forgetful bridge), the no-loops content, and the FC-number fingerprint (the enumerator, the
Fuss–Catalan formula, and the match theorem).  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- N1 — the Fuss–Catalan carrier
#assert_no_axioms FX1Poly.Polygraph.wireLabelListGetAt
#assert_no_axioms FX1Poly.Polygraph.fcArcColour
#assert_no_axioms FX1Poly.Polygraph.fcBoundaryLabelAt
#assert_no_axioms FX1Poly.Polygraph.fcArcsFromPartner
#assert_no_axioms FX1Poly.Polygraph.fcDiagramOf
#assert_no_axioms FX1Poly.Polygraph.fcDiagramForget
#assert_no_axioms FX1Poly.Polygraph.fcDiagramForget_fcDiagramOf
#assert_no_axioms FX1Poly.Polygraph.fcDiagramOf_stringUnitLower
#assert_no_axioms FX1Poly.Polygraph.fcDiagramOf_stringCrossLevelCell
#assert_no_axioms FX1Poly.Polygraph.fxString_hasFcCarrier

end FX1PolyAudit
