import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Type.Level.LevelExprSimplify

/-! # FX1PolyAudit.Axis.Type.Level.LevelExprSimplify05

Zero-axiom audit shard mirroring kernel module `FX1Poly.Axis.Type.Level.LevelExprSimplify` (part 5 of 7).
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Universe.LevelExpr.isPredicative

#assert_no_axioms FX1Poly.Universe.LevelExpr.isPredicative_lmax_smoke

#assert_no_axioms FX1Poly.Universe.LevelExpr.isPredicative_limax_smoke

#assert_no_axioms FX1Poly.Universe.LevelExpr.toMaxPlusForm

#assert_no_axioms FX1Poly.Universe.LevelExpr.toMaxPlusForm_denote

#assert_no_axioms FX1Poly.Universe.LevelExpr.levelMax_add_left_distrib

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.denoteVarOffsets_swap_adjacent

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.denoteVarOffsets_absorb_adjacent

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.insertByVariable

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.denoteVarOffsets_insertByVariable

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.sortByVariable

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.denoteVarOffsets_sortByVariable

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.absorbFrom

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.denoteVarOffsets_absorbFrom

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.absorbAdjacent

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.denoteVarOffsets_absorbAdjacent

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.canonicalizeVarOffsets

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.denoteVarOffsets_canonicalizeVarOffsets

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.canonicalize

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.canonicalize_denote

#assert_no_axioms FX1Poly.Universe.LevelExpr.canonicalize_toMaxPlusForm_denote

#assert_no_axioms FX1Poly.Universe.LevelExpr.levelMax_offset_dominatedRight

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.maxOffset

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.maxOffset_dominated

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.normalizeBase

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.normalizeBase_denote

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.fullCanonicalize

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.fullCanonicalize_denote

#assert_no_axioms FX1Poly.Universe.LevelExpr.fullCanonicalize_toMaxPlusForm_denote

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.zeroEnvironment

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.denoteVarOffsets_zeroEnvironment

#assert_no_axioms FX1Poly.Universe.LevelExpr.levelMax_reabsorb_right

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.normalizeBase_baseConstant_eq_denote_zeroEnvironment

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.allVariablesAtLeast

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.isSortedByVariable

#assert_no_axioms FX1Poly.Universe.LevelExpr.and_eq_true_of_both

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.insertByVariable_preserves_allVariablesAtLeast

#assert_no_axioms FX1Poly.Universe.LevelExpr.ble_trans

#assert_no_axioms FX1Poly.Universe.LevelExpr.ble_false_swap

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.allVariablesAtLeast_mono

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.insertByVariable_preserves_isSortedByVariable

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.sortByVariable_produces_sorted

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.isStrictlySortedByVariable

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.absorbFrom_preserves_allVariablesAtLeast

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.absorbAdjacent_preserves_allVariablesAtLeast

#assert_no_axioms FX1Poly.Universe.LevelExpr.ble_succ_of_beq_false_of_ble

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.absorbFrom_strictlySorted

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.absorbAdjacent_produces_strictlySorted

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.canonicalizeVarOffsets_produces_strictlySorted

end FX1PolyAudit
