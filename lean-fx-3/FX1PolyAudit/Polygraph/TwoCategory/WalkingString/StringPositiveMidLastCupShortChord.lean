import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringPositiveMidLastCupShortChord

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringPositiveMidLastCupShortChord — zero-axiom gate
(FC-3 r44, P2b)

Per-declaration zero-axiom gate for the positive-mid last-cup short-chord readoff + its two positive-mid
fixture fires + the two concrete-matching certificates.  Must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega`.  The project `#assert_no_axioms` macro is fuel-based; the
independent `#print axioms` cross-check lives in the sibling `...AxiomWitness` file (it catches a `decide`
silently degraded to `sorryAx` and any `Lean.ofReduceBool` from `native_decide`). -/

namespace FX1PolyAudit

-- ★ the positive-mid last-cup short-chord readoff (the seed-offset of the r16 width-0 readoff)
#assert_no_axioms FX1Poly.Polygraph.stringMatchingLastCup_isShortChord_mid

-- the concrete mid-1 / mid-2 partner-list certificates (anti-vacuity: the genuinely-computed matchings)
#assert_no_axioms FX1Poly.Polygraph.stringMidOneCupOverG_matchingComputes
#assert_no_axioms FX1Poly.Polygraph.stringMidTwoCupOverGH_matchingComputes

-- the two positive-mid fires
#assert_no_axioms FX1Poly.Polygraph.stringMatchingLastCupShortChord_mid_firesAtMidOne
#assert_no_axioms FX1Poly.Polygraph.stringMatchingLastCupShortChord_mid_firesAtMidTwo

-- honesty marker
#assert_no_axioms FX1Poly.Polygraph.fxString_hasPositiveMidLastCupShortChord

end FX1PolyAudit
