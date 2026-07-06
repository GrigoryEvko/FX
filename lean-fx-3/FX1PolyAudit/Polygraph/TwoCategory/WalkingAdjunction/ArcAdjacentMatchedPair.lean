import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcAdjacentMatchedPair

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcAdjacentMatchedPair — zero-axiom gate

Per-declaration zero-axiom gate for the short-chord planar lemma's application to the real matching: the
adjacent matched pair from the three fold invariants, and its specialisation to the chained-spine extracted
state.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.hasAdjacentMatchedPair_ofInvariants
#assert_no_axioms FX1Poly.Polygraph.hasAdjacentMatchedPair_ofChainedSpine

end FX1PolyAudit
