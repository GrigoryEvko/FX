import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMatchingWidthZeroChordShift

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringMatchingWidthZeroChordShift — zero-axiom gate
(FC-3 r16, PORT 2)

Per-declaration zero-axiom gate for the adjoint-triple-seed width-0 chord-shift descents
(`stringMatchingChordShift_below` / `stringMatchingChordShift_above`) and the marker.  The private setup
`stringMatchingChordShiftSetup` and the range / map / Nat helpers are covered transitively.  Must be free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringMatchingChordShift_below
#assert_no_axioms FX1Poly.Polygraph.stringMatchingChordShift_above
#assert_no_axioms FX1Poly.Polygraph.fxString_hasMatchingWidthZeroChordShift

end FX1PolyAudit
