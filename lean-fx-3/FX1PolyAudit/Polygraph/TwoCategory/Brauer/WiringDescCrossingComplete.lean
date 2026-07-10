import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCrossingComplete

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescCrossingComplete — zero-axiom gate
(BRAUER-V2 r2 B3/B4: unconditional crossing-only completeness + the pass-5-arc wall)

Per-declaration zero-axiom gate for the UNCONDITIONAL crossing-only completeness (`crossingCompleteness_inRange`, no
readback hypothesis, feeding the proven `brauerCrossingOnlyReadbackInRange`), the two decision verdicts
(`crossingCompleteness_bothVerdicts`: isTrue + isFalse), and the honest ledger markers (crossing block CLOSES;
the FULL V2 free word problem stays WALLED on pass-5-arc — `fxBrauer_hasBrauerV2FullCompleteness = false`).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

-- ★ Unconditional crossing-only completeness + the two decision verdicts
#assert_no_axioms FX1Poly.Polygraph.crossingCompleteness_inRange
#assert_no_axioms FX1Poly.Polygraph.crossingCompleteness_bothVerdicts

-- The honest ledger markers: crossing block closes; full V2 completeness stays walled (pass-5-arc)
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCrossingOnlyCompletenessUnconditional
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBrauerV2FullCompleteness

end FX1PolyAudit
