import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingCommutativeMonoid.TwoColourCommutativeMonoidSeed

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingCommutativeMonoid.TwoColourCommutativeMonoidSeed — zero-axiom gate (the FULLY DECIDED walking commutative monoid, TWO generators)

Per-declaration zero-axiom gate for the walking commutative monoid on two generating slots: the
`TwoColourCommMonoidTree` carrier, the `countAOf` / `countBOf` Parikh-vector folds + smokes, the
`TwoColourCommMonoidTreeConv` four-law convertibility, both soundness components, the
`combBBlock` / `combOfCounts` canonical normal form, the `prependBBubble` / `combMergeBBlock` /
`combMerge` merge lemmas, normalization, completeness, the decision biconditional, the shipped decider +
instance, the commutativity / positive-decision / negative-decision groundings, and the marker.  The whole
decision (soundness + normalization + completeness) must be free of `propext`, `Quot.sound`, `Classical`,
`sorry`, `native_decide`, `omega` — only `Nat.add_assoc` / `Nat.add_comm` / `Nat.add_zero` arithmetic is
used. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.TwoColourCommMonoidTree
#assert_no_axioms FX1Poly.Polygraph.countAOf
#assert_no_axioms FX1Poly.Polygraph.countBOf
#assert_no_axioms FX1Poly.Polygraph.countAOf_leafA
#assert_no_axioms FX1Poly.Polygraph.countBOf_leafB
#assert_no_axioms FX1Poly.Polygraph.countBOf_twoLeafB
#assert_no_axioms FX1Poly.Polygraph.TwoColourCommMonoidTreeConv
#assert_no_axioms FX1Poly.Polygraph.twoColourCommMonoidConv_soundA
#assert_no_axioms FX1Poly.Polygraph.twoColourCommMonoidConv_soundB
#assert_no_axioms FX1Poly.Polygraph.combBBlock
#assert_no_axioms FX1Poly.Polygraph.combOfCounts
#assert_no_axioms FX1Poly.Polygraph.prependBBubble
#assert_no_axioms FX1Poly.Polygraph.combMergeBBlock
#assert_no_axioms FX1Poly.Polygraph.combMerge
#assert_no_axioms FX1Poly.Polygraph.twoColourCommMonoidReducesToNormal
#assert_no_axioms FX1Poly.Polygraph.twoColourCommMonoidConv_complete
#assert_no_axioms FX1Poly.Polygraph.twoColourCommMonoidConv_iff_counts
#assert_no_axioms FX1Poly.Polygraph.decideTwoColourCommMonoidTreeConv
#assert_no_axioms FX1Poly.Polygraph.instDecidableTwoColourCommMonoidTreeConv
#assert_no_axioms FX1Poly.Polygraph.twoColourCommMonoidCommHolds
#assert_no_axioms FX1Poly.Polygraph.twoColourCommMonoidDecidesEqualCounts
#assert_no_axioms FX1Poly.Polygraph.twoColourCommMonoidRejectsUnequalCountB
#assert_no_axioms FX1Poly.Polygraph.fxWalkingCommMonoid_hasTwoColourDecision

end FX1PolyAudit
