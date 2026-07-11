import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringCapDualR25Ledger

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringCapDualR25Ledger — zero-axiom gate (FC-3 r25, B4)

Per-declaration zero-axiom gate for the r25 valley-program ledger.  Must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- B4 — the r25 valley-program ledger (the descent re-founding scoreboard)
#assert_no_axioms FX1Poly.Polygraph.fxString_hasCapDualR25Ledger

end FX1PolyAudit
