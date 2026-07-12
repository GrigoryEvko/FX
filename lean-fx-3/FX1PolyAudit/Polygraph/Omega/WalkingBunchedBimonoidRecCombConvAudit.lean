import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidRecCombConv

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidRecCombConvAudit — zero-axiom gate for the recursive
comb-staircase CONV (F4), its width-generalized F1-F3 engine, and the perm-middle word-problem completeness
decision (WP-PROP r26).

Per-declaration `#assert_no_axioms` on the width-generalized four-branch comb-insertion step
(`combInsertConvAtWidth`), the comb-fold + one-level normal-form CONV at width (`combFoldConvAtWidth` /
`combNormalizeFormConvAtWidth`), the recursive comb-staircase CONV at width and its natural-width headline
(`recCombConvAtWidth` / `recCombConv`), the perm-middle word-problem completeness (`coxeterWordUniqueViaRecComb`),
the non-vacuity fires (F4 at widths 3/4/5, the perm-middle braid-pair decision), the negative controls, and the
delivery markers — PLUS an independent (non-fuel) `#print axioms` on the same public declarations.  The project
`#assert_no_axioms` macro is fuel-based; the independent `#print axioms` closes the gate.  (The private arithmetic
+ list + descending-run + Bool + monotonicity backbone `{PredSuccRecComb, NatLePredRecComb, NatAddSubCancelRecComb,
NatEqSubOfAddEqRecComb, NatLeOfAddLeAddRightRecComb, NatLeOfAddLeAddLeftRecComb, SubOneCommRecComb,
AppendAssocRecComb, DescendingPositionsSnocRecComb, NatBleOfLeRecComb, NatBltOfLtRecComb,
DescendingPositionsMentionBelowRecComb, BoolAndLeftRecComb, BoolAndRightRecComb, NatLeOfBleRecComb, NatLtOfBltRecComb,
AppendNilRecComb, MentionsBelowZeroNilRecComb, LtPredOfAddTwoLeRecComb, MentionsOnlyBelowMonoRecComb}` is checked
transitively through the public `combInsertConvAtWidth` / `combFoldConvAtWidth` / `combNormalizeFormConvAtWidth` /
`recCombConvAtWidth` that consume it.) -/

namespace FX1PolyAudit

-- A1 — the width-generalized four-branch comb-insertion CONV step.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCombInsertConvAtWidth

-- A2 — the comb-fold CONV + the one-level normal-form CONV, at arbitrary width.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCombFoldConvAtWidth
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCombNormalizeFormConvAtWidth

-- A3 — the recursive comb-staircase CONV (F4) + its natural-width headline.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRecCombConvAtWidth
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRecCombConv

-- A4 — the perm-middle word-problem completeness decision.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCoxeterWordUniqueViaRecComb

-- A5 — the non-vacuity fires + the negative controls.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRecCombConvJamInstance
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRecCombConvWidthFiveInstance
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRecCombConvBraidInstance
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCoxeterWordUniqueViaRecCombBraidPair
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRecCombConvBaseGuardRejects
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCoxeterViaRecCombGuardSeparates

-- The delivery markers.
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_recCombConvShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_permMiddleWordProblemCompleteViaRecComb
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_recCombRouteBypassesBubbleSortOwners

-- Independent (non-fuel) axiom prints on the width engine, the F4 fold, the perm-middle decision, the fires,
-- the negative controls, and the markers.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCombInsertConvAtWidth
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCombFoldConvAtWidth
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCombNormalizeFormConvAtWidth
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRecCombConvAtWidth
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRecCombConv
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCoxeterWordUniqueViaRecComb
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRecCombConvJamInstance
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRecCombConvWidthFiveInstance
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRecCombConvBraidInstance
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCoxeterWordUniqueViaRecCombBraidPair
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRecCombConvBaseGuardRejects
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCoxeterViaRecCombGuardSeparates
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_recCombConvShipped
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_permMiddleWordProblemCompleteViaRecComb
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_recCombRouteBypassesBubbleSortOwners

end FX1PolyAudit
