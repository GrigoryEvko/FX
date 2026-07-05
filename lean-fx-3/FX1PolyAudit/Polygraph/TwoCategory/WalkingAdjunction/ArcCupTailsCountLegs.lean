import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupTailsCountLegs

/-! # FX1PolyAudit/…/ArcCupTailsCountLegs — zero-axiom gate

Per-declaration zero-axiom gate for the cup cancel's TWO total-count legs: cup-atom and cap-atom
count additivity over `++`, the bubble's generator-arity count invariance, and the two total-count
agreements (`cupCountAgree` / `capCountAgree`) discharged from the cup-case dispatch data alone.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.cupAtomCount_append
#assert_no_axioms FX1Poly.Polygraph.capAtomCount_append
#assert_no_axioms FX1Poly.Polygraph.bubblesToFront_cupAtomCount
#assert_no_axioms FX1Poly.Polygraph.bubblesToFront_capAtomCount
#assert_no_axioms FX1Poly.Polygraph.arcCupCase_cupCountAgree
#assert_no_axioms FX1Poly.Polygraph.arcCupCase_capCountAgree
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupTailsCountLegs

end FX1PolyAudit
