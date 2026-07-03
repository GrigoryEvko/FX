import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWhiskerRightCongruence

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingWhiskerRightCongruence — zero-axiom gate

Per-declaration zero-axiom gate for the right-whisker matching congruence: the
signature-generic assembly, the unconditional walking-adjunction field inhabitant, and the
honesty marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.matchingOf_whiskerRight_congr
#assert_no_axioms FX1Poly.Polygraph.matchingOf_whiskerRight_congruence
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingWhiskerRightCongruence

end FX1PolyAudit
