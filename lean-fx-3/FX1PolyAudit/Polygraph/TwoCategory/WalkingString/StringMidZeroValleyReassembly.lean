import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMidZeroValleyReassembly

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringMidZeroValleyReassembly — zero-axiom gate
(FC-3 r27 B3)

Per-declaration zero-axiom gate for the mid-`0` valley block reassembly (the first consumer of the unconditional
cap sort) and its concrete mixed-valley truth-probe.  Must be free of `propext`, `Quot.sound`, `Classical`,
`sorry`, `native_decide`, `omega`.  The project `#assert_no_axioms` macro is fuel-based; the independent
`#print axioms` lines below are the trusted cross-check. -/

namespace FX1PolyAudit

-- probe data (a genuine same-endpoint cup partner + the two block boundary words)
#assert_no_axioms FX1Poly.Polygraph.stringValleyReassemblyProbeCup
#assert_no_axioms FX1Poly.Polygraph.stringValleyReassemblyProbeCapWord
#assert_no_axioms FX1Poly.Polygraph.stringValleyReassemblyProbeMidWord

-- ★ the mid-`0` valley block reassembly (the FIRST consumer of the unconditional cap sort)
#assert_no_axioms FX1Poly.Polygraph.stringMidZeroSameMatchingValleys_spineTraceEquiv

-- the concrete mixed-valley truth-probe (fires BOTH arms end-to-end)
#assert_no_axioms FX1Poly.Polygraph.stringMidZeroValleyReassembly_firesOnMixedValley

-- honesty marker
#assert_no_axioms FX1Poly.Polygraph.fxString_hasMidZeroValleyReassembly

-- independent cross-check (the fuel macro is not trusted alone)
#print axioms FX1Poly.Polygraph.stringMidZeroSameMatchingValleys_spineTraceEquiv
#print axioms FX1Poly.Polygraph.stringMidZeroValleyReassembly_firesOnMixedValley
#print axioms FX1Poly.Polygraph.fxString_hasMidZeroValleyReassembly

end FX1PolyAudit
