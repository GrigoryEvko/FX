import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Frobenius.SpiderCompleteness

/-! # FX1PolyAudit.Polygraph.TwoCategory.Frobenius.SpiderCompleteness — zero-axiom gate (WP-FROB r7, FROB-7)

Per-declaration zero-axiom gate for spider completeness + the decidable extraspecial word problem: the
block-label boundary-view bridge, the unconditional completeness theorem, the partition characterization, the
`Decidable` instance, the connected-spider Fauser readback + its realization, the fusion witnesses, the decider
non-vacuity, and the honesty markers (including the flipped `fxFrob_hasSpiderCompleteness`).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- FROB-7: the bridge (equal partition ⟹ equal boundary view — the converse of the forward view lemma)
#assert_no_axioms FX1Poly.Polygraph.matchingSameComponent_eq_blockLabelBeq

-- FROB-7: completeness + the partition characterization + the decision
#assert_no_axioms FX1Poly.Polygraph.spiderConv_complete
#assert_no_axioms FX1Poly.Polygraph.spiderConv_iff_extraEq
#assert_no_axioms FX1Poly.Polygraph.instDecidableSpiderConv

-- FROB-7: the connected-spider Fauser readback (`stepView` + μ-comb + δ-comb) and its realization
#assert_no_axioms FX1Poly.Polygraph.spiderViewOf
#assert_no_axioms FX1Poly.Polygraph.mergeToOne
#assert_no_axioms FX1Poly.Polygraph.fanToN
#assert_no_axioms FX1Poly.Polygraph.canonicalSpiderOf
#assert_no_axioms FX1Poly.Polygraph.canonicalSpider_realizes_2_1
#assert_no_axioms FX1Poly.Polygraph.canonicalSpider_realizes_2_2
#assert_no_axioms FX1Poly.Polygraph.canonicalSpider_realizes_3_2
#assert_no_axioms FX1Poly.Polygraph.canonicalSpider_realizes_0_3

-- FROB-7: the fusion witnesses (connected words reduce to their canonical spider via completeness)
#assert_no_axioms FX1Poly.Polygraph.spiderFusion_assocRhs_toCanonical
#assert_no_axioms FX1Poly.Polygraph.spiderFusion_frobLeftLhs_toCanonical

-- FROB-7: the decider non-vacuity — both verdicts on real pairs
#assert_no_axioms FX1Poly.Polygraph.spiderConvDecision_isTrue_frobLeft
#assert_no_axioms FX1Poly.Polygraph.spiderConvDecision_isFalse_HvsIdentity
#assert_no_axioms FX1Poly.Polygraph.spiderConvDecision_bothVerdicts

-- FROB-7: the honesty markers (new + the flipped completeness ledger flag)
#assert_no_axioms FX1Poly.Polygraph.fxFrob_hasSpiderConvDecision
#assert_no_axioms FX1Poly.Polygraph.fxFrob_hasConnectedSpiderNF
#assert_no_axioms FX1Poly.Polygraph.fxFrob_hasSpiderFusionNF
#assert_no_axioms FX1Poly.Polygraph.fxFrob_hasMultiBlockSpiderRealization
#assert_no_axioms FX1Poly.Polygraph.fxFrob_hasSpecialFrobeniusDecision
#assert_no_axioms FX1Poly.Polygraph.fxFrob_hasSpiderCompleteness

end FX1PolyAudit
