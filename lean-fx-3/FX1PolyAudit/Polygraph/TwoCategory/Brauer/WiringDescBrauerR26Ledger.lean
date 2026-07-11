import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBrauerR26Ledger

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescBrauerR26Ledger — zero-axiom gate (BRAUER r26 grand ledger)

Per-declaration zero-axiom gate for the r26 grand ledger: the machine-checked #2013 marker state
(`fxBrauer_r26GrandLedger`) and the not-complete honesty marker (`fxBrauer_hasBrauerR26Complete`).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.fxBrauer_r26GrandLedger
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBrauerR26Complete

end FX1PolyAudit
