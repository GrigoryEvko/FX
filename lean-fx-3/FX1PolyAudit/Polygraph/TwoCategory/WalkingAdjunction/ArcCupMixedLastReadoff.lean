import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupMixedLastReadoff

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupMixedLastReadoff — zero-axiom gate

Per-declaration zero-axiom gate for the mixed-spine last-cup short-chord readoff (S1-mixed): the last cup
of a boundary-chained MIXED (cup AND cap) spine reads off the boundary matching as an adjacent short chord.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.mixedSpine_lastCup_isShortChord

end FX1PolyAudit
