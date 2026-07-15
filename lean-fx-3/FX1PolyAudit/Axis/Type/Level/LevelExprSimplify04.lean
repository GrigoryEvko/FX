import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Type.Level.LevelExprSimplify

/-! # FX1PolyAudit.Axis.Type.Level.LevelExprSimplify04

Zero-axiom audit shard mirroring kernel module `FX1Poly.Axis.Type.Level.LevelExprSimplify` (part 4 of 7).
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Universe.LevelExpr.strictlySorted_unique

#assert_no_axioms FX1Poly.Universe.LevelExpr.levelMax_ge_left

#assert_no_axioms FX1Poly.Universe.LevelExpr.levelMax_ge_right

#assert_no_axioms FX1Poly.Universe.LevelExpr.denote_le_denoteAtomList_of_occurs

#assert_no_axioms FX1Poly.Universe.LevelExpr.denoteAtomList_eq_zero_of_all_zero

#assert_no_axioms FX1Poly.Universe.LevelExpr.denoteAtomList_eq_zero_iff

#assert_no_axioms FX1Poly.Universe.LevelExpr.pointEnvironment

#assert_no_axioms FX1Poly.Universe.LevelExpr.denote_lvar_pointEnvironment

#assert_no_axioms FX1Poly.Universe.LevelExpr.denote_lvar_pointEnvironment_self

#assert_no_axioms FX1Poly.Universe.LevelExpr.denoteAtomList_pointEnvironment_ne_zero_of_occursLvar

#assert_no_axioms FX1Poly.Universe.LevelExpr.AllAtomsAreVariables

#assert_no_axioms FX1Poly.Universe.LevelExpr.isLvar_of_occursIn_allVariables

#assert_no_axioms FX1Poly.Universe.LevelExpr.denoteAtomList_pointEnvironment_eq_zero_of_not_occursLvar

#assert_no_axioms FX1Poly.Universe.LevelExpr.occursLvar_iff_denoteAtomList_pointEnvironment_ne_zero

#assert_no_axioms FX1Poly.Universe.LevelExpr.canonicalAtoms

#assert_no_axioms FX1Poly.Universe.LevelExpr.canonicalize_eq_foldLmax_canonicalAtoms

#assert_no_axioms FX1Poly.Universe.LevelExpr.denote_eq_denoteAtomList_canonicalAtoms

#assert_no_axioms FX1Poly.Universe.LevelExpr.canonicalAtoms_sameLvarMembership_of_denoteEquiv

#assert_no_axioms FX1Poly.Universe.LevelExpr.compare_right_lzero_ne_lt

#assert_no_axioms FX1Poly.Universe.LevelExpr.IsStrictLowerBound_dropLzeroAtoms

#assert_no_axioms FX1Poly.Universe.LevelExpr.dropLzeroAtoms_strictlySorted

#assert_no_axioms FX1Poly.Universe.LevelExpr.canonicalAtoms_strictlySorted

#assert_no_axioms FX1Poly.Universe.LevelExpr.sameMembership_of_sameLvarMembership

#assert_no_axioms FX1Poly.Universe.LevelExpr.canonicalize_eq_of_denoteEquiv_onVariableFragment

#assert_no_axioms FX1Poly.Universe.LevelExpr.IsVariableJoin

#assert_no_axioms FX1Poly.Universe.LevelExpr.AllAtomsAreVarsOrLzero

#assert_no_axioms FX1Poly.Universe.LevelExpr.AllAtomsAreVarsOrLzero_append

#assert_no_axioms FX1Poly.Universe.LevelExpr.lmaxAtoms_allVarsOrLzero_of_isVariableJoin

#assert_no_axioms FX1Poly.Universe.LevelExpr.AllAtomsAreVarsOrLzero_insertByCompare

#assert_no_axioms FX1Poly.Universe.LevelExpr.AllAtomsAreVarsOrLzero_insertionSortByCompare

#assert_no_axioms FX1Poly.Universe.LevelExpr.AllAtomsAreVarsOrLzero_dedupAdjacent

#assert_no_axioms FX1Poly.Universe.LevelExpr.AllAtomsAreVariables_dropLzeroAtoms

#assert_no_axioms FX1Poly.Universe.LevelExpr.canonicalAtoms_allVariables_of_isVariableJoin

#assert_no_axioms FX1Poly.Universe.LevelExpr.canonicalize_eq_of_denoteEquiv_of_isVariableJoin

#assert_no_axioms FX1Poly.Universe.LevelExpr.denoteEquiv_of_canonicalize_eq

#assert_no_axioms FX1Poly.Universe.LevelExpr.decidableDenoteEquivOfVariableJoin

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.denoteVarOffsets

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.denote

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.incrementOffsets

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.shiftSucc

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.denoteVarOffsets_incrementOffsets_shift

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.shiftSucc_denote

#assert_no_axioms FX1Poly.Universe.LevelExpr.levelMax_interchange

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.denoteVarOffsets_append

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.merge

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.merge_denote

#assert_no_axioms FX1Poly.Universe.LevelExpr.and_eq_true_imp_left

#assert_no_axioms FX1Poly.Universe.LevelExpr.and_eq_true_imp_right

end FX1PolyAudit
