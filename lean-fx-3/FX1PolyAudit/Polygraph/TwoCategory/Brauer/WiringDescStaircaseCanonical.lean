import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStaircaseCanonical

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescStaircaseCanonical — zero-axiom gate (BREACH r2)

Per-declaration zero-axiom gate for the recursive-comb staircase, canonicity, and THE FLIP.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- R1: the data-fold projections + the recursive comb + its convertibility
#assert_no_axioms FX1Poly.Polygraph.combFoldState_below
#assert_no_axioms FX1Poly.Polygraph.combFoldState_runLe
#assert_no_axioms FX1Poly.Polygraph.recComb
#assert_no_axioms FX1Poly.Polygraph.recCombConv
#assert_no_axioms FX1Poly.Polygraph.recComb_r9_stuck_word
#assert_no_axioms FX1Poly.Polygraph.recComb_r11_residual_left
#assert_no_axioms FX1Poly.Polygraph.recComb_r11_residual_right
#assert_no_axioms FX1Poly.Polygraph.combNormalizeForm_r11_left_fixed
#assert_no_axioms FX1Poly.Polygraph.recComb_width5_word
#assert_no_axioms FX1Poly.Polygraph.recCombConv_r9_stuck_word
#assert_no_axioms FX1Poly.Polygraph.recCombConv_r11_left
#assert_no_axioms FX1Poly.Polygraph.recCombConv_width5_word
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasStaircaseCombNormalForm

-- R3.A: the permutation-carry crux (the soundness leg's hard lemma)
#assert_no_axioms FX1Poly.Polygraph.foldl_append_swap
#assert_no_axioms FX1Poly.Polygraph.applyAdjacentSwap_commute_of_le
#assert_no_axioms FX1Poly.Polygraph.swap_commutes_runAbove
#assert_no_axioms FX1Poly.Polygraph.swap_commutes_runBelow
#assert_no_axioms FX1Poly.Polygraph.carry_perm

-- R3.B: the DATA comb fold preserves the through-strand permutation (the soundness leg)
#assert_no_axioms FX1Poly.Polygraph.perm_append_split
#assert_no_axioms FX1Poly.Polygraph.combInsertData_realizesSwap
#assert_no_axioms FX1Poly.Polygraph.combFold_preservesPerm
#assert_no_axioms FX1Poly.Polygraph.combNormalizeForm_preservesPerm

-- R2.A: the strand pins + the prefix-fixes-top lemma (private helpers covered transitively)
#assert_no_axioms FX1Poly.Polygraph.swap_moves_value_down
#assert_no_axioms FX1Poly.Polygraph.run_bubblesFromIndex
#assert_no_axioms FX1Poly.Polygraph.perm_extend_fixedTop

end FX1PolyAudit
