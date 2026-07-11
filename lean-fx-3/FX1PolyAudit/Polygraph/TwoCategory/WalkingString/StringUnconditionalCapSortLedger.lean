import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringUnconditionalCapSortLedger

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringUnconditionalCapSortLedger — zero-axiom gate
(FC-3 r24, B3)

Per-declaration zero-axiom gate for the unconditional pure-cap sort ledger (held FALSE) + the fresh-valley
example.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- B3 — the fresh six-wire valley firing the B2 colour-free exclusion (past-window branch)
#assert_no_axioms FX1Poly.Polygraph.stringFreshValleyProbeState
#assert_no_axioms FX1Poly.Polygraph.stringFreshValleyProbe_fires

-- B3 — the honest marker: the unconditional pure-cap sort is NOT achieved (pin uninhabited)
#assert_no_axioms FX1Poly.Polygraph.fxString_hasUnconditionalPureCapSort

end FX1PolyAudit
