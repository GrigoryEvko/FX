import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcInsertionPeel

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescArcInsertionPeel — zero-axiom gate (BRAUER r35)

Per-declaration zero-axiom gate for the single-arc PEEL STEP over the r34 leg fuel and the J1 working-region seam
resolution: the compositional cupless read (`hasNoCup_append`), the two Σ-carried leg-fuel sink rungs
(`legSink_cupCrossing` / `legSink_cupCap`), the two J1-seam-resolving rungs with the standard prefix whiskered off
(`legSink_cupCrossing_underStandardPrefix` / `legSink_cupCap_underStandardPrefix`), the flagship single-arc peel to
arrival (`legPeelToArrival_demo`), the honest arrival-is-not-tail companion (`legPeelToArrival_topPermTail_demo`), the
honesty markers, and the machine-checked terminal state.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.hasNoCup_append
#assert_no_axioms FX1Poly.Polygraph.legSink_cupCrossing
#assert_no_axioms FX1Poly.Polygraph.legSink_cupCap
#assert_no_axioms FX1Poly.Polygraph.legSink_cupCrossing_underStandardPrefix
#assert_no_axioms FX1Poly.Polygraph.legSink_cupCap_underStandardPrefix
#assert_no_axioms FX1Poly.Polygraph.legPeelToArrival_demo
#assert_no_axioms FX1Poly.Polygraph.legPeelToArrival_topPermTail_demo
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasLegFuelPeelRung
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasLegFuelWorkingRegionScoped
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasLegFuelPeelToArrival
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasLegFuelOuterAssembly
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_legFuelPeelTerminalState

end FX1PolyAudit
