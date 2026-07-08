import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingWidthZeroChordShift

/-! # FX1PolyAudit/…/MatchingWidthZeroChordShift — zero-axiom gate

Per-declaration zero-axiom gate for Track B LOCATE ports b#2/b#3/b#4: the width-0 chord-shift twins on the
plain `matchingOf` carrier.  The empty-spine forward-chord floor, and the below/above chord-shift descents,
read forward chords off `matchingOfSpineList 0 .partner` riding the shipped brick-3 splice
`diagramPartner_stepCup`, never the arc census / `0 < bottomCount`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.matchingChordShift_below
#assert_no_axioms FX1Poly.Polygraph.matchingChordShift_above
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingWidthZeroChordShift

end FX1PolyAudit
