import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Mode.ExhibitedConvergentDecision

/-! # FX1PolyAudit/Axis/Mode/ExhibitedConvergentDecision — zero-axiom gate (Tier-C exhibited-convergent)

Per-declaration zero-axiom gate for the Tier-C exhibited-convergent decision of the walking involution: the
oriented rewrite, termination (length drop + SN + WellFounded), the parity funnel + confluence, the
convergent normalizer + carrier `DecidableEq` + the KB decision, the Tier B <-> Tier C tie, the non-vacuity
witnesses, and the Tier-C flag + its involution-marker pin.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.InvolutionRewrite
#assert_no_axioms FX1Poly.Polygraph.involutionRewrite_lengthDecreases
#assert_no_axioms FX1Poly.Polygraph.involutionRewriteTerminating
#assert_no_axioms FX1Poly.Polygraph.involutionRewriteWellFounded
#assert_no_axioms FX1Poly.Polygraph.involutionRewrite_preservesParity
#assert_no_axioms FX1Poly.Polygraph.involutionRewriteStar_preservesParity
#assert_no_axioms FX1Poly.Polygraph.involutionRewriteStar_consCongr
#assert_no_axioms FX1Poly.Polygraph.reducesToParityNF_consStep
#assert_no_axioms FX1Poly.Polygraph.reducesToParityNF_ofLength
#assert_no_axioms FX1Poly.Polygraph.reducesToParityNF
#assert_no_axioms FX1Poly.Polygraph.involutionNil_isNormal
#assert_no_axioms FX1Poly.Polygraph.involutionS_isNormal
#assert_no_axioms FX1Poly.Polygraph.parityNF_isNormal
#assert_no_axioms FX1Poly.Polygraph.involutionRewriteConfluent
#assert_no_axioms FX1Poly.Polygraph.involutionConvergentNormalizer
#assert_no_axioms FX1Poly.Polygraph.involutionModeDecEq
#assert_no_axioms FX1Poly.Polygraph.involutionModalityDecEq
#assert_no_axioms FX1Poly.Polygraph.involutionModalityPathDecEq
#assert_no_axioms FX1Poly.Polygraph.decideInvolutionEquationalTheory
#assert_no_axioms FX1Poly.Polygraph.involutionRewrite_toConv
#assert_no_axioms FX1Poly.Polygraph.involutionEquationalTheory_consCongr
#assert_no_axioms FX1Poly.Polygraph.involutionOneCellConv_of_equationalTheory
#assert_no_axioms FX1Poly.Polygraph.equationalTheory_of_involutionOneCellConv
#assert_no_axioms FX1Poly.Polygraph.equationalTheory_iff_involutionOneCellConv
#assert_no_axioms FX1Poly.Polygraph.involutionEquationalTheory_double_nil
#assert_no_axioms FX1Poly.Polygraph.involutionEquationalTheory_notSingle_nil
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasExhibitedConvergentDecision
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasExhibitedConvergentDecision_matchesInvolutionMarker

end FX1PolyAudit
