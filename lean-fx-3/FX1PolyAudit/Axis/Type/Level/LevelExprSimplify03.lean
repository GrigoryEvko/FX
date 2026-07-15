import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Type.Level.LevelExprSimplify

/-! # FX1PolyAudit.Axis.Type.Level.LevelExprSimplify03

Zero-axiom audit shard mirroring kernel module `FX1Poly.Axis.Type.Level.LevelExprSimplify` (part 3 of 7).
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Universe.LevelExpr.compare_lt_trans

#assert_no_axioms FX1Poly.Universe.LevelExpr.swapToCanonicalLmax

#assert_no_axioms FX1Poly.Universe.LevelExpr.canonicalizeLmaxPair

#assert_no_axioms FX1Poly.Universe.LevelExpr.swapToCanonicalLmax_denoteEquiv

#assert_no_axioms FX1Poly.Universe.LevelExpr.canonicalizeLmaxPair_denoteEquiv

#assert_no_axioms FX1Poly.Universe.LevelExpr.canonicalizeLmaxPair_swapToCanonicalLmax

#assert_no_axioms FX1Poly.Universe.LevelExpr.canonicalizeLmaxPair_idempotent

#assert_no_axioms FX1Poly.Universe.LevelExpr.lmaxAtoms

#assert_no_axioms FX1Poly.Universe.LevelExpr.foldLmax

#assert_no_axioms FX1Poly.Universe.LevelExpr.foldLmax_append_denoteEquiv

#assert_no_axioms FX1Poly.Universe.LevelExpr.foldLmax_lmaxAtoms_denoteEquiv

#assert_no_axioms FX1Poly.Universe.LevelExpr.dropLzeroAtoms

#assert_no_axioms FX1Poly.Universe.LevelExpr.foldLmax_dropLzeroAtoms_denoteEquiv

#assert_no_axioms FX1Poly.Universe.LevelExpr.foldLmax_swap_denoteEquiv

#assert_no_axioms FX1Poly.Universe.LevelExpr.insertStep

#assert_no_axioms FX1Poly.Universe.LevelExpr.insertByCompare

#assert_no_axioms FX1Poly.Universe.LevelExpr.foldLmax_insertByCompare_denoteEquiv

#assert_no_axioms FX1Poly.Universe.LevelExpr.insertionSortByCompare

#assert_no_axioms FX1Poly.Universe.LevelExpr.foldLmax_insertionSortByCompare_denoteEquiv

#assert_no_axioms FX1Poly.Universe.LevelExpr.foldLmax_dup_head_denoteEquiv

#assert_no_axioms FX1Poly.Universe.LevelExpr.dedupStep

#assert_no_axioms FX1Poly.Universe.LevelExpr.dedupAdjacent

#assert_no_axioms FX1Poly.Universe.LevelExpr.foldLmax_dedupAdjacent_denoteEquiv

#assert_no_axioms FX1Poly.Universe.LevelExpr.canonicalize

#assert_no_axioms FX1Poly.Universe.LevelExpr.canonicalize_denoteEquiv

#assert_no_axioms FX1Poly.Universe.LevelExpr.denoteAtomList

#assert_no_axioms FX1Poly.Universe.LevelExpr.denoteAtomList_append

#assert_no_axioms FX1Poly.Universe.LevelExpr.foldLmax_denote

#assert_no_axioms FX1Poly.Universe.LevelExpr.lmaxAtoms_denote

#assert_no_axioms FX1Poly.Universe.LevelExpr.IsLowerBound

#assert_no_axioms FX1Poly.Universe.LevelExpr.IsSorted

#assert_no_axioms FX1Poly.Universe.LevelExpr.IsLowerBound_insertByCompare

#assert_no_axioms FX1Poly.Universe.LevelExpr.insertByCompare_sorted

#assert_no_axioms FX1Poly.Universe.LevelExpr.insertionSortByCompare_sorted

#assert_no_axioms FX1Poly.Universe.LevelExpr.IsLowerBound_dedupAdjacent

#assert_no_axioms FX1Poly.Universe.LevelExpr.dedupAdjacent_sorted

#assert_no_axioms FX1Poly.Universe.LevelExpr.compare_lzero_ne_gt

#assert_no_axioms FX1Poly.Universe.LevelExpr.compare_le_lzero_imp_eq

#assert_no_axioms FX1Poly.Universe.LevelExpr.lzero_isLowerBound

#assert_no_axioms FX1Poly.Universe.LevelExpr.IsLowerBound_dropLzeroAtoms

#assert_no_axioms FX1Poly.Universe.LevelExpr.dropLzeroAtoms_sorted

#assert_no_axioms FX1Poly.Universe.LevelExpr.IsStrictLowerBound

#assert_no_axioms FX1Poly.Universe.LevelExpr.IsStrictlySorted

#assert_no_axioms FX1Poly.Universe.LevelExpr.IsStrictLowerBound_dedupAdjacent

#assert_no_axioms FX1Poly.Universe.LevelExpr.dedupAdjacent_strictlySorted

#assert_no_axioms FX1Poly.Universe.LevelExpr.OccursIn

#assert_no_axioms FX1Poly.Universe.LevelExpr.strictlySorted_head_lt

#assert_no_axioms FX1Poly.Universe.LevelExpr.compare_lt_imp_ne

#assert_no_axioms FX1Poly.Universe.LevelExpr.compare_lt_asymm

end FX1PolyAudit
