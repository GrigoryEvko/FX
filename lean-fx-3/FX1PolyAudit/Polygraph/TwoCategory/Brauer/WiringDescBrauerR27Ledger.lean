import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBrauerR27Ledger

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescBrauerR27Ledger — zero-axiom gate (BRAUER r27 grand ledger)

Per-declaration zero-axiom gate for the r27 grand ledger: the machine-checked #2013 marker state
(`fxBrauer_r27GrandLedger` — the THROUGH crux + P1 decode leg true, every master false) and the not-complete honesty
marker (`fxBrauer_hasBrauerR27Complete`).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.fxBrauer_r27GrandLedger
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBrauerR27Complete

end FX1PolyAudit
