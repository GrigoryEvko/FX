import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingDistLawSortNF

/-! # FX1PolyAudit.Polygraph.Omega.WalkingDistLawSortNFAudit — zero-axiom gate for the distributive law's
1-cell sorted normal form and word problem decision (WP-DISTLAW r1, B2 + B3).

Per-declaration `#assert_no_axioms` on the alphabet, the swap bubble step and its equation lemmas, the letter
counts and inversion measure, the normal form, the structural-fuel sort, the count-preservation and
termination lemmas, the convergence-to-normal-form theorem, the confluence witnesses, the word-convertibility
relation, the soundness / completeness of the decision, the decision equivalence, both concrete verdicts, the
carrier bridge, and the honesty markers. -/

namespace FX1PolyAudit

-- the alphabet and the swap bubble step
#assert_no_axioms FX1Poly.Polygraph.Omega.DistLawColour
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawBubbleStep
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawBubbleStep_tHead
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawBubbleStep_ssHead
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawBubbleStep_stHead

-- the counts, the inversion measure, the normal form
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawCountT
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawCountS
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawInversions
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawSPower
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawTThenS
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawNf

-- the structural-fuel sort
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawSortFueled
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawSortFueled_stepSome
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawSortFueled_stepNone

-- termination: count preservation and the strict inversion decrease
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawAddEqZeroLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawCountT_step
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawCountS_step
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawInversions_step

-- convergence to the normal form
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawBubbleNone_inversionsZero
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawAllColourS_ofCountTZero
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawInversionsZero_eqNf
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawNf_step
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawSortReachesNf
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawSortReachesNf_atInversions

-- confluence witnesses (normal form terminal and unique)
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawCountT_sPower
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawInversions_sPower
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawInversions_tThenS
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawInversions_nf
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawSortConfluent

-- B3: the word convertibility, its decision, and both verdicts
#assert_no_axioms FX1Poly.Polygraph.Omega.DistLawWordConv
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawSameCount_ofConv
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawBubbleStep_conv
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawConv_toSortFueled
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawConv_toNf
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawConv_ofSameCount
#assert_no_axioms FX1Poly.Polygraph.Omega.DistLawWordSameCount
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawConv_iffSameCount
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawWordST
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawWordTS
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawWordSST
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawWordDecisionYes
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawWordDecisionNo

-- the carrier bridge and the honesty markers
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawColourGen
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawWordToCell
#assert_no_axioms FX1Poly.Polygraph.Omega.fxDistLaw_oneCellSortedNormalFormShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxDistLaw_oneCellWordProblemDecided
#assert_no_axioms FX1Poly.Polygraph.Omega.fxDistLaw_oneCellDecisionDoesNotLiftToTwoCell

end FX1PolyAudit
