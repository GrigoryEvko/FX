import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBrauerR25Ledger

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescBrauerR25Ledger — zero-axiom gate (BRAUER r25 ledger)

Per-declaration zero-axiom gate for the r25 gap ledger: the `rfl`-conjunction recording the three NEW r25 ingredient
markers (GAP β, GAP γ-witness, the CUP / THROUGH join-site reductions) true and every master wall false
(`fxBrauer_r25GapLedger`), and the honest not-complete marker (`fxBrauer_hasBrauerR25Complete`).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.fxBrauer_r25GapLedger
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBrauerR25Complete

end FX1PolyAudit
