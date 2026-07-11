import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMatchingLastCupShortChord

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringMatchingLastCupShortChord — zero-axiom gate
(FC-3 r16, PORT 1)

Per-declaration zero-axiom gate for the adjoint-triple-seed width-0 LOCATE readoff
(`stringMatchingLastCup_isShortChord`) and its marker.  The private `List.range` read-off helpers are
covered transitively.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringMatchingLastCup_isShortChord
#assert_no_axioms FX1Poly.Polygraph.fxString_hasMatchingLastCupShortChord

end FX1PolyAudit
