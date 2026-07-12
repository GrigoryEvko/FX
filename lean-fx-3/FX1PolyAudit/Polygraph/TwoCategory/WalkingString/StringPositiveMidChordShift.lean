import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringPositiveMidChordShift

/-! # FX1PolyAudit.…WalkingString.StringPositiveMidChordShift — zero-axiom gate (FC-3 r45, R1)

Per-declaration zero-axiom gate for the positive-mid chord-shift LOCATE descents (the seed-offset ports of
the r16 width-`0` chord-shifts, riding `diagramPartner_stepCup` at `seedBoundary := midWidth` + the new
`midWidth ≤ nextFresh` obligation off `processSpine_nextFresh_le`).  Must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega`.  The project `#assert_no_axioms` macro is fuel-based; the
independent `#print axioms` cross-check lives in the sibling `...AxiomWitness` file. -/

namespace FX1PolyAudit

-- ★ the positive-mid chord-shift descents (the seed-offset ports of the r16 width-0 chord-shifts)
#assert_no_axioms FX1Poly.Polygraph.stringMatchingChordShift_below_mid
#assert_no_axioms FX1Poly.Polygraph.stringMatchingChordShift_above_mid

-- honesty marker
#assert_no_axioms FX1Poly.Polygraph.fxString_hasPositiveMidChordShift

end FX1PolyAudit
