import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCupSlideLedger

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescCupSlideLedger — zero-axiom gate (WP-BRAUER-4 r4, B5)

Per-declaration zero-axiom gate for the BRAUER-V2 ledger: the machine-checked flag-coherence theorem
(`brauerV2_ledger_coherent`) pinning the exact honest state after the round, the grand ledger marker, and the
POLY-TAB-2 migration note (delete-nothing-this-round).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- the machine-checked ledger coherence + markers
#assert_no_axioms FX1Poly.Polygraph.brauerV2_ledger_coherent
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBrauerV2Ledger
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBrauerV2PolyTabMigrationNote

end FX1PolyAudit
