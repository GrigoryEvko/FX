import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringPositiveMidSnakeExclusion

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringPositiveMidSnakeExclusion — zero-axiom gate
(FC-3 r43 P2a)

Per-declaration zero-axiom gate for the positive-mid snake exclusion + cup-end split.  Must be free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  The project `#assert_no_axioms`
macro is fuel-based; the independent `#print axioms` lines below are the trusted cross-check (they catch a
`decide` silently degraded to `sorryAx` and any `Lean.ofReduceBool` from `native_decide`). -/

namespace FX1PolyAudit

-- ★ the snake refutation at positive mid-width (rides the shipped positive-boundary involution)
#assert_no_axioms FX1Poly.Polygraph.stringMatchingForwardChordsNotAdjacent_mid

-- ★ the cup-end open-wire split at the midWidth seed
#assert_no_axioms FX1Poly.Polygraph.stringMatchingOpenWiresCupEndSplit_mid

-- the concrete mid-2 cup-fixture fire (anti-vacuity)
#assert_no_axioms FX1Poly.Polygraph.stringPositiveMidCupEndSplit_firesOnMidTwoCup

-- honesty marker
#assert_no_axioms FX1Poly.Polygraph.fxString_hasPositiveMidSnakeExclusion

-- independent cross-check (the fuel macro is not trusted alone)
#print axioms FX1Poly.Polygraph.stringMatchingForwardChordsNotAdjacent_mid
#print axioms FX1Poly.Polygraph.stringMatchingOpenWiresCupEndSplit_mid
#print axioms FX1Poly.Polygraph.stringPositiveMidCupEndSplit_firesOnMidTwoCup
#print axioms FX1Poly.Polygraph.fxString_hasPositiveMidSnakeExclusion

end FX1PolyAudit
