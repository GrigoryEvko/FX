import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcFreshBlockTransposition

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcFreshBlockTransposition — zero-axiom gate

Per-declaration zero-axiom gate for the singleton swap's renaming sigma: the fresh-block
transposition with its fixing laws, block-value laws, left inverse, and injectivity.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcFreshBlockTransposition
#assert_no_axioms FX1Poly.Polygraph.arcFreshBlockTransposition_ofBelow
#assert_no_axioms FX1Poly.Polygraph.arcFreshBlockTransposition_fixesZero
#assert_no_axioms FX1Poly.Polygraph.arcFreshBlockTransposition_ofAtOrAbove
#assert_no_axioms FX1Poly.Polygraph.arcFreshBlockTransposition_onFirstBlock
#assert_no_axioms FX1Poly.Polygraph.arcFreshBlockTransposition_onSecondBlock
#assert_no_axioms FX1Poly.Polygraph.arcFreshBlockTransposition_leftInverse
#assert_no_axioms FX1Poly.Polygraph.arcFreshBlockTransposition_injective

end FX1PolyAudit
