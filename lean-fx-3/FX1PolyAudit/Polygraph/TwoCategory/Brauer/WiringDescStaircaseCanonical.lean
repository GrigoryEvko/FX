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

end FX1PolyAudit
