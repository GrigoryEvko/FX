import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStandardFoldR5Ledger

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescStandardFoldR5Ledger — zero-axiom gate (BRAUER-MIDDLE r5,
B3 + B4 + B5: the named TAG-CORRESPONDENCE residual, the roundtrip wall, and the terminal r5 grand ledger)

Per-declaration zero-axiom gate for the r5 terminal ledger: the named TAG-CORRESPONDENCE decomposition marker
(`fxBrauer_hasTagCorrDecomposition`), the machine-checked r5 grand ledger (`fxBrauer_r5GrandLedger`), and the
terminal honesty marker (`fxBrauer_hasBrauerMiddleR5Complete`).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasTagCorrDecomposition
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_r5GrandLedger
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBrauerMiddleR5Complete

end FX1PolyAudit
