import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.InterchangeFreeNormalize

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.InterchangeFreeNormalize — zero-axiom gate (mode-3 floor)

Per-declaration zero-axiom gate for the COMPUTABLE normalizer of the interchange-free 2-cell fragment: the
deterministic one-step reducer (`reduceOnce` + its root probes), its soundness and completeness, the
`Acc.rec`-built `ConvergentNormalizer`, and the headline "interchange-free convertibility = normal-form equality".

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- ★ The deterministic one-step reducer + its non-recursive root probes
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.dropRightIdentity
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.reduceRootVcomp
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.reduceRootWhiskerLeft
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.reduceRootWhiskerRight
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.reduceOnce

-- ★ Soundness of the reducer (each fired redex is a genuine interchange-free step)
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.dropRightIdentity_sound
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.reduceRootVcomp_sound
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.reduceRootWhiskerLeft_sound
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.reduceRootWhiskerRight_sound
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.reduceOnce_sound

-- ★ Completeness (a halted reducer marks a normal form)
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.reduceRootVcomp_rightId_ne_none
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.reduceOnce_ne_none_of_step
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.reduceOnce_complete

-- ★ The convergent normalizer + interchange-free convertibility = normal-form equality
#assert_no_axioms FX1Poly.Polygraph.interchangeFreeNormalizer
#assert_no_axioms FX1Poly.Polygraph.interchangeFreeConv_iff_normalFormEq

-- ★ The sound positive half of the FULL TwoCellConv decision (the gate's target)
#assert_no_axioms FX1Poly.Polygraph.interchangeFreeConv_imp_twoCellConv
#assert_no_axioms FX1Poly.Polygraph.normalFormEq_imp_twoCellConv

end FX1PolyAudit
