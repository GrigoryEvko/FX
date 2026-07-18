import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingSemilattice.FiniteSetSemilatticeSeed

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingSemilattice.FiniteSetSemilatticeSeed — zero-axiom gate (the FULLY DECIDED walking bounded semilattice, ARBITRARY alphabet)

Per-declaration zero-axiom gate for the walking bounded semilattice on an arbitrary alphabet: the `natBle`
reflexivity add-on and the two transitivity-contradiction helpers, the dedup-on-equal `insertSortedSet`
kit with its three equation lemmas and the two crux lemmas `insertSortedSetIdem` (idempotency of the
set-insert) and `insertSortedSetComm` (insertion commutes = permutation-invariance of the sorted-distinct
normal form), the `insertManySet` layer with its associativity / commutativity / idempotency lemmas, the
`insertTreeSet` / `setColoursOf` sorted-distinct normal form + smokes (incl. the DEDUP smoke) +
`insertTreeSetSpread` / `setColoursOfMul`, the `FiniteSetSemilatticeTreeConv` FIVE-law convertibility,
soundness, the `combInsertSortedSet` / `combMergeSet` merge lemmas, normalization, completeness, the decision
biconditional, the shipped decider + instance, the reorder / idempotent-collapse / dedup / rejection
groundings, and the marker.  The whole decision (soundness + normalization + completeness) must be free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega` — the ordering is the imported
structural `natBle` (no `Nat.le`/`Nat.ble` lemma), the inserts are cons-only, and no `List.append` (`++`) is
used anywhere. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.natBleRefl
#assert_no_axioms FX1Poly.Polygraph.natBleFalseMid
#assert_no_axioms FX1Poly.Polygraph.natBleFalseEnd
#assert_no_axioms FX1Poly.Polygraph.insertSortedSet
#assert_no_axioms FX1Poly.Polygraph.insertSortedSetNilEq
#assert_no_axioms FX1Poly.Polygraph.insertSortedSetEq
#assert_no_axioms FX1Poly.Polygraph.insertSortedSetLt
#assert_no_axioms FX1Poly.Polygraph.insertSortedSetGt
#assert_no_axioms FX1Poly.Polygraph.insertSortedSetIdem
#assert_no_axioms FX1Poly.Polygraph.insertSortedSetComm
#assert_no_axioms FX1Poly.Polygraph.insertManySet
#assert_no_axioms FX1Poly.Polygraph.insertSortedSetInsertMany
#assert_no_axioms FX1Poly.Polygraph.insertManySetInsertSorted
#assert_no_axioms FX1Poly.Polygraph.insertManySetAssoc
#assert_no_axioms FX1Poly.Polygraph.insertManySetComm
#assert_no_axioms FX1Poly.Polygraph.insertManySetIdem
#assert_no_axioms FX1Poly.Polygraph.insertTreeSet
#assert_no_axioms FX1Poly.Polygraph.setColoursOf
#assert_no_axioms FX1Poly.Polygraph.setColoursOf_leaf
#assert_no_axioms FX1Poly.Polygraph.setColoursOf_dedup
#assert_no_axioms FX1Poly.Polygraph.setColoursOf_sorts
#assert_no_axioms FX1Poly.Polygraph.insertTreeSetSpread
#assert_no_axioms FX1Poly.Polygraph.setColoursOfMul
#assert_no_axioms FX1Poly.Polygraph.insertManySetSetColoursNil
#assert_no_axioms FX1Poly.Polygraph.FiniteSetSemilatticeTreeConv
#assert_no_axioms FX1Poly.Polygraph.finiteSetSemilatticeConv_sound
#assert_no_axioms FX1Poly.Polygraph.combInsertSortedSet
#assert_no_axioms FX1Poly.Polygraph.combMergeSet
#assert_no_axioms FX1Poly.Polygraph.finiteSetTreeReducesToComb
#assert_no_axioms FX1Poly.Polygraph.finiteSetSemilatticeConv_complete
#assert_no_axioms FX1Poly.Polygraph.finiteSetSemilatticeConv_iff_setColours
#assert_no_axioms FX1Poly.Polygraph.decideFiniteSetSemilatticeTreeConv
#assert_no_axioms FX1Poly.Polygraph.instDecidableFiniteSetSemilatticeTreeConv
#assert_no_axioms FX1Poly.Polygraph.finiteSetSemilatticeReordersColours
#assert_no_axioms FX1Poly.Polygraph.finiteSetSemilatticeCollapsesRepeatedColour
#assert_no_axioms FX1Poly.Polygraph.finiteSetSemilatticeDedupsRepeatedColour
#assert_no_axioms FX1Poly.Polygraph.finiteSetSemilatticeRejectsMissingColour
#assert_no_axioms FX1Poly.Polygraph.fxWalkingSemilattice_hasFiniteSetDecision

end FX1PolyAudit
