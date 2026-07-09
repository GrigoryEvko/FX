import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.BareConvCompleteness

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.BareConvCompleteness — zero-axiom gate

Per-declaration zero-axiom gate for the bare-`TwoCellConv` COMPLETENESS frontier: the three further bare-conv
moments (`RawTwoCellExpr.leftCount` / `.coCrossSum` / `.nestedCrossSum`) and their step / conv invariance (all
six `_eq` lemmas, including the interchange critical pair); the three cast-invariance twins and the five
whisker-functoriality DEFECT vectors; the COMPOSITE separating pair (`cellLRRL` / `cellRLLR`, the cast-free
full-conv `cellLRRL_convFull_cellRLLR`, the equal `whiskerSum` / `rSum` / `crossSum`, the distinct
`nestedCrossSum`, and the resulting `cellLRRL_not_twoCellConv_cellRLLR`); the three-moment incompleteness over
composites (`bareConvCandidate_not_complete_composite`); the four-moment candidate (`bareConvCandidate4`) with
soundness, decidability (`adjunctionDecideBareConvCandidate4`), exclusion, and non-vacuity; the full-conv-variance
of the fourth invariant; and the honesty marker.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.leftCount
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.coCrossSum
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.nestedCrossSum
#assert_no_axioms FX1Poly.Polygraph.TwoCellStep.leftCount_eq
#assert_no_axioms FX1Poly.Polygraph.TwoCellConv.leftCount_eq
#assert_no_axioms FX1Poly.Polygraph.TwoCellStep.coCrossSum_eq
#assert_no_axioms FX1Poly.Polygraph.TwoCellConv.coCrossSum_eq
#assert_no_axioms FX1Poly.Polygraph.TwoCellStep.nestedCrossSum_eq
#assert_no_axioms FX1Poly.Polygraph.TwoCellConv.nestedCrossSum_eq
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.castBoundary_whiskerSum
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.castBoundary_rSum
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.castBoundary_crossSum
#assert_no_axioms FX1Poly.Polygraph.whiskerLeftUnit_defect
#assert_no_axioms FX1Poly.Polygraph.whiskerRightUnit_defect
#assert_no_axioms FX1Poly.Polygraph.whiskerLeftComp_defect
#assert_no_axioms FX1Poly.Polygraph.whiskerRightComp_defect
#assert_no_axioms FX1Poly.Polygraph.whiskerExchange_defect
#assert_no_axioms FX1Poly.Polygraph.cellLRRL
#assert_no_axioms FX1Poly.Polygraph.cellRLLR
#assert_no_axioms FX1Poly.Polygraph.nilWhiskerExchange
#assert_no_axioms FX1Poly.Polygraph.cellLRRL_convFull_cellRLLR
#assert_no_axioms FX1Poly.Polygraph.cellLRRL_whiskerSum_eq_cellRLLR
#assert_no_axioms FX1Poly.Polygraph.cellLRRL_rSum_eq_cellRLLR
#assert_no_axioms FX1Poly.Polygraph.cellLRRL_crossSum_eq_cellRLLR
#assert_no_axioms FX1Poly.Polygraph.cellLRRL_nestedCrossSum
#assert_no_axioms FX1Poly.Polygraph.cellRLLR_nestedCrossSum
#assert_no_axioms FX1Poly.Polygraph.cellLRRL_nestedCrossSum_differs
#assert_no_axioms FX1Poly.Polygraph.cellLRRL_not_twoCellConv_cellRLLR
#assert_no_axioms FX1Poly.Polygraph.bareConvCandidate_not_complete_composite
#assert_no_axioms FX1Poly.Polygraph.bareConvCandidate4
#assert_no_axioms FX1Poly.Polygraph.bareConvCandidate4_of_twoCellConv
#assert_no_axioms FX1Poly.Polygraph.adjunctionDecideBareConvCandidate4
#assert_no_axioms FX1Poly.Polygraph.bareConvCandidate4_excludes_cellLRRL_cellRLLR
#assert_no_axioms FX1Poly.Polygraph.bareConvCandidate4_accepts_parallelUnits
#assert_no_axioms FX1Poly.Polygraph.cellLRRL_convFull_but_nestedCrossSum_differs
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasBareConvMomentFamilyProvablyLossy

end FX1PolyAudit
