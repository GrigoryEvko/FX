import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescExtractorLedger

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescExtractorLedger — zero-axiom gate (BRAUER-MIDDLE r2, B4)

Per-declaration zero-axiom gate for the terminal ledger: the three named r3 residual nodes
(`fxBrauer_hasExt5TotalExtractorRoundtrip`, `fxBrauer_hasStraddleGlobalFuelNode`, `fxBrauer_hasWhiskerFreeSortDriver`),
the machine-checked grand ledger (`fxBrauer_r2GrandLedger`), and the terminal honesty marker
(`fxBrauer_hasBrauerMiddleR2Complete`).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasExt5TotalExtractorRoundtrip
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasStraddleGlobalFuelNode
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasWhiskerFreeSortDriver
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_r2GrandLedger
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBrauerMiddleR2Complete

end FX1PolyAudit
