import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcDescentLedger

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescArcDescentLedger — zero-axiom gate (BRAUER-ARC-DESCENT r1, B4)

Per-declaration zero-axiom gate for the arc-descent ledger: the machine-checked terminal-state decomposition, the
pinned-wall theorem (the straddle resister), and the ledger honesty marker.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.fxBrauer_arcDescentTerminalState
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_arcDescentWall
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasArcDescentLedger

end FX1PolyAudit
