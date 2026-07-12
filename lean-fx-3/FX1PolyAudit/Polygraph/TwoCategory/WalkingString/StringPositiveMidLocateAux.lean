import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringPositiveMidLocateAux

/-! # FX1PolyAudit.…WalkingString.StringPositiveMidLocateAux — zero-axiom gate (FC-3 r45, R3)

Per-declaration zero-axiom gate for the positive-mid fueled partner-LOCATE (the width-`0` locate
re-parameterized `0 ⤳ midWidth`, riding R1 chord-shifts + P2a snake exclusion + P2b readoff + P2c base floor).
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  The independent
`#print axioms` cross-check lives in the sibling `...AxiomWitness` file. -/

namespace FX1PolyAudit

-- ★ the positive-mid fueled partner-LOCATE
#assert_no_axioms FX1Poly.Polygraph.stringMatchingLocateAuxMid

-- honesty marker
#assert_no_axioms FX1Poly.Polygraph.fxString_hasPositiveMidLocateAux

end FX1PolyAudit
