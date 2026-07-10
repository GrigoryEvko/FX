import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcAnchorLedger

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescArcAnchorLedger — zero-axiom gate (BRAUER-ARC-DESCENT r2, B5)

Per-declaration zero-axiom gate for the terminal ledger: the machine-checked terminal-state decomposition
(`fxBrauer_arcAnchorTerminalState`), the three bundled permanent walls (`fxBrauer_arcAnchorWalls`), and the ledger
honesty marker.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.fxBrauer_arcAnchorTerminalState
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_arcAnchorWalls
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasArcAnchorLedger

end FX1PolyAudit
