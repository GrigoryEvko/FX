import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStandardFoldPhasesLedger

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescStandardFoldPhasesLedger — zero-axiom gate
(BRAUER-MIDDLE r4, B4 ledger)

Per-declaration zero-axiom gate for the r4 grand ledger and the terminal honesty marker.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.fxBrauer_r4GrandLedger
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBrauerMiddleR4Complete

end FX1PolyAudit
