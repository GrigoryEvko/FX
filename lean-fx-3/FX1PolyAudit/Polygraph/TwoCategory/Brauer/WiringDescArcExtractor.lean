import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcExtractor

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescArcExtractor — zero-axiom gate (BRAUER-MIDDLE r2, B1)

Per-declaration zero-axiom gate for the general arc EXTRACTOR + the 5-block-plus-loops extended standard form: the
datatype (`BrauerStandardFormExt5`), the circle word (`circleWord`) and its realization smokes, the word / diagram
realizers (`standardFormWordExt5` / `standardFormDiagramExt5`), the arc-partition read-offs (`natReplicate`,
`capArcFeetIndices`, `expandBottomFeetPairs`, `capArcFeet`, `throughStrandTops`, `cupArcTopIndices`,
`expandCupTopPairs`, `cupArcTops`), the extractor (`reconstructStandardFormExt5`), the guarded readback
(`standardFormOfDiagramExt`) with its unconditional soundness (`standardFormOfDiagramExt_sound`), the adversarial-B
existence + readback (`adversarialB_ext5_realizes` / `standardFormOfDiagramExt_adversarialB_some`), the straddle
readback (`standardFormOfDiagramExt_straddle_some`), the roundtrips / regression, the non-vacuity bundle, and the two
honesty markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.circleWord
#assert_no_axioms FX1Poly.Polygraph.standardFormWordExt5
#assert_no_axioms FX1Poly.Polygraph.standardFormDiagramExt5
#assert_no_axioms FX1Poly.Polygraph.natReplicate
#assert_no_axioms FX1Poly.Polygraph.capArcFeetIndices
#assert_no_axioms FX1Poly.Polygraph.expandBottomFeetPairs
#assert_no_axioms FX1Poly.Polygraph.capArcFeet
#assert_no_axioms FX1Poly.Polygraph.throughStrandTops
#assert_no_axioms FX1Poly.Polygraph.cupArcTopIndices
#assert_no_axioms FX1Poly.Polygraph.expandCupTopPairs
#assert_no_axioms FX1Poly.Polygraph.cupArcTops
#assert_no_axioms FX1Poly.Polygraph.reconstructStandardFormExt5
#assert_no_axioms FX1Poly.Polygraph.standardFormOfDiagramExt
#assert_no_axioms FX1Poly.Polygraph.standardFormOfDiagramExt_sound
#assert_no_axioms FX1Poly.Polygraph.circleWord_realizes_loop
#assert_no_axioms FX1Poly.Polygraph.circleWord_realizes_twoLoops
#assert_no_axioms FX1Poly.Polygraph.adversarialBDiagram
#assert_no_axioms FX1Poly.Polygraph.adversarialB_ext5_realizes
#assert_no_axioms FX1Poly.Polygraph.standardFormOfDiagramExt_adversarialB_some
#assert_no_axioms FX1Poly.Polygraph.standardFormOfDiagramExt_straddle_some
#assert_no_axioms FX1Poly.Polygraph.standardFormOfDiagramExt_roundtrip_loops
#assert_no_axioms FX1Poly.Polygraph.standardFormOfDiagramExt_crossingCap_some
#assert_no_axioms FX1Poly.Polygraph.standardFormOfDiagramExt_pureCrossing_some
#assert_no_axioms FX1Poly.Polygraph.standardFormOfDiagramExt_nonVacuity
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasExt5ArcExtractor
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasExt5TotalExtractor

end FX1PolyAudit
