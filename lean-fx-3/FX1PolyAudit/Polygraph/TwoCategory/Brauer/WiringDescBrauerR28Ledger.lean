import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBrauerR28Ledger

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescBrauerR28Ledger — zero-axiom gate (BRAUER r28 grand ledger)

Per-declaration zero-axiom gate for the r28 grand ledger: the machine-checked #2013 marker state
(`fxBrauer_r28GrandLedger` — the THROUGH weld + all-class routing markers true, every master false) and the
not-complete honesty marker (`fxBrauer_hasBrauerR28Complete`).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.fxBrauer_r28GrandLedger
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBrauerR28Complete

end FX1PolyAudit
