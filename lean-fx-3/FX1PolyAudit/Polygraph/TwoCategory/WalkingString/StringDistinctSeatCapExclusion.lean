import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringDistinctSeatCapExclusion

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringDistinctSeatCapExclusion — zero-axiom gate
(FC-3 r24, B2)

Per-declaration zero-axiom gate for the colour-free cap-step gap-closing exclusion.  Must be free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- B2 — position-uniqueness from positional distinctness
#assert_no_axioms FX1Poly.Polygraph.natListGetAt_inj_ofWireListDistinct

-- B2 — the COLOUR-FREE cap-step gap-closing exclusion (the keystone replacing the false colour premise)
#assert_no_axioms FX1Poly.Polygraph.stringArcPairSeated_beforeCapStep_ofDistinctSeat

-- B2 — the concrete truth-probe + the honesty marker
#assert_no_axioms FX1Poly.Polygraph.stringDistinctSeatProbeState
#assert_no_axioms FX1Poly.Polygraph.stringDistinctSeatProbe_fires
#assert_no_axioms FX1Poly.Polygraph.fxString_hasDistinctSeatCapExclusion

end FX1PolyAudit
