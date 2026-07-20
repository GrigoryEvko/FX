import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Probability.FiniteSupportDistribution

/-! # FX1PolyAudit/ComputerAlgebra/Probability/FiniteSupportDistribution —
    zero-axiom gate (MEAS-1)

Per-declaration zero-axiom gate for the exact finite-support ℚ-probability
distribution layer: the carrier `FpDist`, the mass-sum fold with its
append-splits-sum law, well-formedness, the mass-sum-preserving normalisation
(merge duplicate outcomes, drop zeros, sort), the pushforward / convex mixture
/ independent product / conditioning operations each with their
`fpd*PreservesMassOne` total-stays-one theorem, expectation with its linearity
and dirac laws, the structural equality decision with soundness and the genuine
`FpConv` normal-form congruence (both halves), the closed-value fires, and the
two WALLED markers `fpdHasCountableSupport` / `fpdHasGiryMonadLaws`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.qnfMulZeroRight
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfMulZeroLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfAddMiddleFour
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfMulLeftSwap
#assert_no_axioms FX1Poly.ComputerAlgebra.FpDist
#assert_no_axioms FX1Poly.ComputerAlgebra.FpDist.mk
#assert_no_axioms FX1Poly.ComputerAlgebra.FpDist.support
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdMassSum
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdCat
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdMassSumCat
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdMassIsNonNeg
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdAllMassesNonNeg
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdIsWellFormed
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdDirac
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdDiracMassSumOne
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdDiracIsWellFormed
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdInsert
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdInsertMassSum
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdMergeAll
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdMergeAllMassSum
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdDropZeros
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdDropZerosMassSum
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdNormalise
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdNormaliseMassSum
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdRelabel
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdRelabelMassSum
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdMap
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdMapPreservesMassOne
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdScale
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdScaleMassSum
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfAddWeightComplement
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdConvex
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdConvexPreservesMassOne
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdPairNat
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdProductRow
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdProductRowMassSum
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdProductSupport
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdProductSupportMassSum
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdProduct
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdProductPreservesMassOne
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdFilter
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdCondition
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdConditionPreservesMassOne
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdExpectationList
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdExpectation
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdDiracExpectation
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdExpectationAddPayoff
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdExpectationScalePayoff
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdExpectationLinear
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdSupportBeq
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdSupportBeqRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdSupportBeqSound
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdDistEq
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdEqOfSupportEq
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdDistEqSound
#assert_no_axioms FX1Poly.ComputerAlgebra.FpConv
#assert_no_axioms FX1Poly.ComputerAlgebra.fpConvRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.fpConvSymm
#assert_no_axioms FX1Poly.ComputerAlgebra.fpConvTrans
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdConvSound
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdConvComplete
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdDistEqIffConv
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdHasCountableSupport
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdHasGiryMonadLaws
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdFairCoin
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdFireFairCoinWellFormed
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdFireFairCoinMassOne
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdFireFairCoinExpectation
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdFireReorderMergeEqual
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdFireDifferentNotEqual
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdFireProductFourOutcomes
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdFireProductMassOne
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdHasMassPreservation
#assert_no_axioms FX1Poly.ComputerAlgebra.fpdHasDecidableEquality

end FX1PolyAudit
