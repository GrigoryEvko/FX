import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.CyclicThreeChainComplex

/-! # FX1PolyAudit/Polygraph/Homology/CyclicThreeChainComplex — zero-axiom gate (the cyclic-order-three
    walker `⟨s | sss ⟹ id⟩`: polygraphic chain complex + machine-checked `d d = 0` + Smith-normal
    boundaries + the homology read-offs `H1 = ZZ/3` and `H2 = 0` + the generic-carrier recovery)

Per-declaration zero-axiom gate for the H2-WALKERS r2 third instance: the basis counts, the two
critical pairs as DATA, the three boundary-matrix literals, the augmented directed complex instance and
its `d d = 0` corollary, the oracle / non-vacuity smokes, the three Smith reduction certificates and
rank/torsion read-offs (★★ `H1(cyclic Z/3) = ZZ/3`, the first odd-torsion walker homology, and
`H2 = 0`), the third-instance recovery through the generic carrier, and the census update.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeBasisCount
#assert_no_axioms FX1Poly.Polygraph.Homology.allCyclicThreeCriticalPairs
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeCriticalPairCountIsTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.allCyclicThreeCriticalPairsExhaustive
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeCriticalPairIndex
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeCriticalPairOverlapCell
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeCriticalPairBoundaryColumn
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeBoundaryOfDimZero
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeBoundaryOfDimOne
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeBoundaryOfDimTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeBoundaryMatrix
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeBoundaryComposesToZero
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeChainComplex
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeChainComplexBoundaryComposesToZero
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeBoundaryDimZeroMatchesOracle
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeBoundaryDimOneIsNonzero
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeBoundaryDimTwoColumnMatchesCriticalPair
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeChainComplexIsNonVacuous
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeBoundaryOfDimZeroSmithCertificate
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeBoundaryOfDimOneSmithCertificate
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeBoundaryOfDimTwoSmithCertificate
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeBoundaryOfDimZeroReducesToSmith
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeBoundaryOfDimOneReducesToSmith
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeBoundaryOfDimTwoReducesToSmith
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeSmithNormalFormOfDimZero
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeSmithNormalFormOfDimOne
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeSmithNormalFormOfDimTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeDimZeroCertificateProducesSmithNormalForm
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeDimOneCertificateProducesSmithNormalForm
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeDimTwoCertificateProducesSmithNormalForm
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeRankOfDimZero
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeRankOfDimOne
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeRankOfDimTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeNullityOfDimZero
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeNullityOfDimZeroValue
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeDegreeOneHomologyFreeRank
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeDegreeOneHomologyFreeRankIsZero
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeDegreeOneTorsionFactors
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeDegreeOneTorsionFactorsValue
#assert_no_axioms FX1Poly.Polygraph.Homology.CyclicThreeDegreeOneHomologyStatement
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeDegreeOneHomologyIsZmodThree
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeNullityOfDimOne
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeNullityOfDimOneValue
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeDegreeTwoHomologyFreeRank
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeDegreeTwoHomologyFreeRankIsZero
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeDimTwoHasNoTorsion
#assert_no_axioms FX1Poly.Polygraph.Homology.CyclicThreeDegreeTwoHomologyIsZeroStatement
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeDegreeTwoHomologyIsZero
#assert_no_axioms FX1Poly.Polygraph.Homology.CyclicThreeSmithHandoffStatement
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeSmithHandoff
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeWalkerPresentation
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreePresentationComputesBasisCount
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreePresentationComputesBoundaryDimZero
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreePresentationComputesBoundaryDimOne
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreePresentationComputesBoundaryDimTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreePresentationComputesBoundaryMatrix
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreePresentationIsWellFormed
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeGenericCarrierBoundaryComposesToZero
#assert_no_axioms FX1Poly.Polygraph.Homology.walkersWithComputedHomologyCountAfterCyclicThree
#assert_no_axioms FX1Poly.Polygraph.Homology.walkersWithComputedHomologyCountAfterCyclicThreeValue
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeHomologyLedgerIsComplete

end FX1PolyAudit
