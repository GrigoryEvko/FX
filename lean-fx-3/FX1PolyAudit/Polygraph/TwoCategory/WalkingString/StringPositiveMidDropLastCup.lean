import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringPositiveMidDropLastCup

/-! # FX1PolyAudit.…WalkingString.StringPositiveMidDropLastCup — zero-axiom gate (FC-3 r45, R2)

Per-declaration zero-axiom gate for the positive-mid drop-injectivity linchpin + its back-append companion
(the seed-offset ports of the r16 width-`0` drop, riding `diagramPartner_stepCup` at `seedBoundary := midWidth`
and the already-seed-general per-field congruence, with the new `midWidth ≤ nextFresh` obligations off
`processSpine_nextFresh_le`).  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`,
`omega`.  The independent `#print axioms` cross-check lives in the sibling `...AxiomWitness` file. -/

namespace FX1PolyAudit

-- ★ the positive-mid drop-injectivity linchpin + its back-append companion
#assert_no_axioms FX1Poly.Polygraph.stringDropLastCup_matching_injective_mid
#assert_no_axioms FX1Poly.Polygraph.stringBackAppend_matching_congr_mid

-- honesty marker
#assert_no_axioms FX1Poly.Polygraph.fxString_hasPositiveMidDropLastCup

end FX1PolyAudit
