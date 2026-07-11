import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringCapDualR24Ledger

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringCapDualR24Ledger — zero-axiom gate (FC-3 r24, B4)

Per-declaration zero-axiom gate for the r24 valley-program ledger.  Must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- B4 — the FC-3 r24 valley-program ledger (the honest scoreboard)
#assert_no_axioms FX1Poly.Polygraph.fxString_hasCapDualR24Ledger

end FX1PolyAudit
