import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingCommutativeMonoid.MultisetCommutativeMonoidSeed

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingCommutativeMonoid.MultisetCommutativeMonoidSeed — zero-axiom gate (the FULLY DECIDED walking commutative monoid, ARBITRARY alphabet)

Per-declaration zero-axiom gate for the walking commutative monoid on an arbitrary alphabet: the purpose-built
structural `natBle` ordering + its totality / transitivity / antisymmetry, the `insertSorted` / `insertMany`
sorted-list kit with the crux `insertSortedComm` (insertion commutes = permutation-invariance) and the
`insertMany` associativity / commutativity lemmas, the `ColourTree` carrier, the `insertTree` /
`sortedColoursOf` multiset normal form + smokes + `insertTreeSpread` / `sortedColoursOfMul`, the
`MultisetCommMonoidTreeConv` four-law convertibility, soundness, the `combOfList` comb, the
`combInsertSorted` / `combMerge` merge lemmas, normalization, completeness, the decision biconditional, the
shipped decider + instance, the reordering / rejection groundings, and the marker.  The whole decision
(soundness + normalization + completeness) must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega` — no `Nat.le`/`Nat.ble` lemma and no `List.append` (`++`) is used anywhere. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.natBle
#assert_no_axioms FX1Poly.Polygraph.natBleTotal
#assert_no_axioms FX1Poly.Polygraph.natBleTrans
#assert_no_axioms FX1Poly.Polygraph.natBleAntisymm
#assert_no_axioms FX1Poly.Polygraph.insertSorted
#assert_no_axioms FX1Poly.Polygraph.insertSortedNilEq
#assert_no_axioms FX1Poly.Polygraph.insertSortedConsTrue
#assert_no_axioms FX1Poly.Polygraph.insertSortedConsFalse
#assert_no_axioms FX1Poly.Polygraph.insertMany
#assert_no_axioms FX1Poly.Polygraph.insertSortedComm
#assert_no_axioms FX1Poly.Polygraph.insertSortedInsertMany
#assert_no_axioms FX1Poly.Polygraph.insertManyInsertSorted
#assert_no_axioms FX1Poly.Polygraph.insertManyAssoc
#assert_no_axioms FX1Poly.Polygraph.insertManyComm
#assert_no_axioms FX1Poly.Polygraph.ColourTree
#assert_no_axioms FX1Poly.Polygraph.insertTree
#assert_no_axioms FX1Poly.Polygraph.sortedColoursOf
#assert_no_axioms FX1Poly.Polygraph.sortedColoursOf_leaf
#assert_no_axioms FX1Poly.Polygraph.sortedColoursOf_mulSorts
#assert_no_axioms FX1Poly.Polygraph.sortedColoursOf_threeSorts
#assert_no_axioms FX1Poly.Polygraph.insertTreeSpread
#assert_no_axioms FX1Poly.Polygraph.sortedColoursOfMul
#assert_no_axioms FX1Poly.Polygraph.insertManySortedColoursNil
#assert_no_axioms FX1Poly.Polygraph.MultisetCommMonoidTreeConv
#assert_no_axioms FX1Poly.Polygraph.multisetCommMonoidConv_sound
#assert_no_axioms FX1Poly.Polygraph.combOfList
#assert_no_axioms FX1Poly.Polygraph.combInsertSorted
#assert_no_axioms FX1Poly.Polygraph.combMergeColourLists
#assert_no_axioms FX1Poly.Polygraph.multisetTreeReducesToComb
#assert_no_axioms FX1Poly.Polygraph.multisetCommMonoidConv_complete
#assert_no_axioms FX1Poly.Polygraph.multisetCommMonoidConv_iff_sortedColours
#assert_no_axioms FX1Poly.Polygraph.decideMultisetCommMonoidTreeConv
#assert_no_axioms FX1Poly.Polygraph.instDecidableMultisetCommMonoidTreeConv
#assert_no_axioms FX1Poly.Polygraph.multisetCommMonoidReordersTwoColours
#assert_no_axioms FX1Poly.Polygraph.multisetCommMonoidReordersThreeColours
#assert_no_axioms FX1Poly.Polygraph.multisetCommMonoidRejectsUnequalMultiset
#assert_no_axioms FX1Poly.Polygraph.fxWalkingCommMonoid_hasMultisetDecision

end FX1PolyAudit
