import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.NonCrossingShortChord

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/NonCrossingShortChord — zero-axiom gate

Per-declaration zero-axiom gate for the short-chord planar lemma (cup rung D2): a non-crossing
fixed-point-free involution matching has an adjacent matched pair.  The private clean min/max and the
minimal-gap descent are covered transitively.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.nonCrossing_hasAdjacentMatchedPair

end FX1PolyAudit
