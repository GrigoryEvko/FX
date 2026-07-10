import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcAnchor

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescArcAnchor — zero-axiom gate (BRAUER-ARC-DESCENT r2, B1/B2)

Per-declaration zero-axiom gate for the standard-form readback function and the anchored-measure target wall: the
gated readback (`standardFormOfDiagram`), its unconditional soundness (`standardFormOfDiagram_sound`), the
reachable-class roundtrips, the two walls exhibited by the readback's `none`s (`standardFormOfDiagram_straddle_none` /
`standardFormOfDiagram_pureCrossing_none`), the machine-checked crossing straddle target
(`straddleDiagram_isCrossing`), the assembled anchored-measure wall (`anchoredMeasure_targetWall`), and the two
honesty markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.standardFormOfDiagram
#assert_no_axioms FX1Poly.Polygraph.standardFormOfDiagram_sound
#assert_no_axioms FX1Poly.Polygraph.standardFormOfDiagram_roundtrip_identity
#assert_no_axioms FX1Poly.Polygraph.standardFormOfDiagram_roundtrip_cupCap
#assert_no_axioms FX1Poly.Polygraph.straddleDiagram_eq
#assert_no_axioms FX1Poly.Polygraph.straddleDiagram_isCrossing
#assert_no_axioms FX1Poly.Polygraph.standardFormOfDiagram_straddle_none
#assert_no_axioms FX1Poly.Polygraph.standardFormOfDiagram_pureCrossing_none
#assert_no_axioms FX1Poly.Polygraph.standardFormOfDiagram_nonVacuity
#assert_no_axioms FX1Poly.Polygraph.anchoredMeasure_targetWall
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasStandardFormReadbackFunction
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasAnchoredMeasureTargetWall

end FX1PolyAudit
