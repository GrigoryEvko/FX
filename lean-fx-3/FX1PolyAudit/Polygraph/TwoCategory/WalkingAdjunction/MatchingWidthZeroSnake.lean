import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingWidthZeroSnake

/-! # FX1PolyAudit/…/MatchingWidthZeroSnake — zero-axiom gate

Per-declaration zero-axiom gate for Track B b#5 core: the width-0 snake exclusion (riding the b#1 partner
involution) and the cup-end open-wire split.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.matchingForwardChordsNotAdjacent
#assert_no_axioms FX1Poly.Polygraph.matchingOpenWiresCupEndSplit
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingWidthZeroSnake

end FX1PolyAudit
