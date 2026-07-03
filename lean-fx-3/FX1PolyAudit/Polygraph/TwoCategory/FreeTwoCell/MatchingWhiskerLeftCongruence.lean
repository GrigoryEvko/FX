import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWhiskerLeftCongruence

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingWhiskerLeftCongruence — zero-axiom gate

Per-declaration zero-axiom gate for the left-whisker matching compositionality: the
signature-generic congruence, the unconditional walking-adjunction field inhabitant, and the
honesty marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.matchingOf_whiskerLeft_congr
#assert_no_axioms FX1Poly.Polygraph.matchingOf_whiskerLeft_congruence
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingWhiskerLeftCongruence

end FX1PolyAudit
