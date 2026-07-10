import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringOrientationExcludedRefutation

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringOrientationExcludedRefutation — zero-axiom gate
(FC-3 r7, B3)

Per-declaration zero-axiom gate for the orientation-excluded refutation: the width pin, the same-length window
clash, and the four-combo vacuity theorem.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringOrientationLeftContextLengthEq
#assert_no_axioms FX1Poly.Polygraph.stringSameLengthWindowClash
#assert_no_axioms FX1Poly.Polygraph.stringOrientationExcluded_vacuous
#assert_no_axioms FX1Poly.Polygraph.fxString_hasOrientationExcludedRefutation

end FX1PolyAudit
