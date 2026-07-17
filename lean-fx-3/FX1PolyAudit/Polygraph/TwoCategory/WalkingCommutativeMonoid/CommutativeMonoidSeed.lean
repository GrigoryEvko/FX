import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingCommutativeMonoid.CommutativeMonoidSeed

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingCommutativeMonoid.CommutativeMonoidSeed — zero-axiom gate (the FULLY DECIDED walking commutative monoid, single generator)

Per-declaration zero-axiom gate for the walking commutative monoid: the `CommMonoidTree` carrier, the
`leafCount` soundness invariant + smokes, the `CommMonoidTreeConv` four-law convertibility, the `0 + n = n`
helper, soundness, the `combOf` right-comb normal form, `combAppend`, normalization, completeness, the
decision biconditional, the associativity / commutativity / positive-decision / negative-decision groundings,
and the marker.  The whole decision (soundness + normalization + completeness) must be free of `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega` — only `Nat.add_assoc` / `Nat.add_comm` /
`Nat.add_zero` arithmetic is used. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.CommMonoidTree
#assert_no_axioms FX1Poly.Polygraph.leafCount
#assert_no_axioms FX1Poly.Polygraph.leafCount_leaf
#assert_no_axioms FX1Poly.Polygraph.leafCount_unit
#assert_no_axioms FX1Poly.Polygraph.leafCount_threeSlot
#assert_no_axioms FX1Poly.Polygraph.CommMonoidTreeConv
#assert_no_axioms FX1Poly.Polygraph.commMonoidNatZeroAdd
#assert_no_axioms FX1Poly.Polygraph.commMonoidTreeConv_sound
#assert_no_axioms FX1Poly.Polygraph.combOf
#assert_no_axioms FX1Poly.Polygraph.combAppend
#assert_no_axioms FX1Poly.Polygraph.commMonoidTreeReducesToComb
#assert_no_axioms FX1Poly.Polygraph.commMonoidTreeConv_complete
#assert_no_axioms FX1Poly.Polygraph.commMonoidTreeConv_iff_leafCount
#assert_no_axioms FX1Poly.Polygraph.commMonoidAssocHolds
#assert_no_axioms FX1Poly.Polygraph.commMonoidCommHolds
#assert_no_axioms FX1Poly.Polygraph.commMonoidDecidesEqualCount
#assert_no_axioms FX1Poly.Polygraph.commMonoidRejectsUnequalCount
#assert_no_axioms FX1Poly.Polygraph.fxWalkingCommMonoid_hasSingleGeneratorDecision

end FX1PolyAudit
