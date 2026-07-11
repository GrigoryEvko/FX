import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringWordPairSeatedDescent

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringWordPairSeatedDescent — zero-axiom gate (FC-3 r23)

Per-declaration zero-axiom gate for the WORD-founded prefix descent master at the adjoint triple.  Must be free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- B1 — the same-parity-generic cap-step gap-closing exclusion (the crux prerequisite)
#assert_no_axioms FX1Poly.Polygraph.stringArcPairSeated_beforeCapStep_ofSameParities
#assert_no_axioms FX1Poly.Polygraph.stringSameParityProbeState
#assert_no_axioms FX1Poly.Polygraph.stringSameParityProbe_fires
#assert_no_axioms FX1Poly.Polygraph.fxString_hasCapStepSameParityExclusion

end FX1PolyAudit
