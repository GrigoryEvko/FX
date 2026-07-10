import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.InvolutionChainComplex

/-! # FX1PolyAudit/Polygraph/Homology/InvolutionChainComplex — zero-axiom gate (the walking-involution
    polygraphic chain complex + machine-checked `d d = 0` + Smith-normal boundaries + the homology
    read-offs `H1 = ZZ/2` and `H2 = 0`)

Per-declaration zero-axiom gate for the H2-WALKERS r1 walking-involution chain complex: the basis
counts, the single critical pair as DATA, the three boundary-matrix literals, the augmented directed
complex instance, the instance `d d = 0` corollary, the oracle / non-vacuity smokes, the three Smith
reduction certificates, the new torsion EXTRACTOR `smithInvariantFactorsWithin`, and both homology
read-offs (★★ `H1(walking involution) = ZZ/2`, the first torsion walker homology, and
`H2(walking involution) = 0`), plus the carrier census.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Homology.involutionBasisCount
#assert_no_axioms FX1Poly.Polygraph.Homology.allInvolutionCriticalPairs
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionCriticalPairCountIsOne
#assert_no_axioms FX1Poly.Polygraph.Homology.allInvolutionCriticalPairsExhaustive
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionCriticalPairIndex
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionCriticalPairOverlapCell
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionCriticalPairBoundaryColumn
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionBoundaryOfDimZero
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionBoundaryOfDimOne
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionBoundaryOfDimTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionBoundaryMatrix
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionBoundaryComposesToZero
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionChainComplex
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionChainComplexBoundaryComposesToZero
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionBoundaryDimZeroMatchesOracle
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionBoundaryDimOneIsNonzero
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionBoundaryDimTwoColumnMatchesCriticalPair
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionChainComplexIsNonVacuous
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionBoundaryOfDimZeroSmithCertificate
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionBoundaryOfDimOneSmithCertificate
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionBoundaryOfDimTwoSmithCertificate
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionBoundaryOfDimZeroReducesToSmith
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionBoundaryOfDimOneReducesToSmith
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionBoundaryOfDimTwoReducesToSmith
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionSmithNormalFormOfDimZero
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionSmithNormalFormOfDimOne
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionSmithNormalFormOfDimTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionDimZeroCertificateProducesSmithNormalForm
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionDimOneCertificateProducesSmithNormalForm
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionDimTwoCertificateProducesSmithNormalForm
#assert_no_axioms FX1Poly.Polygraph.Homology.smithInvariantFactorsWithin
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionRankOfDimZero
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionRankOfDimOne
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionRankOfDimTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionNullityOfDimZero
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionNullityOfDimZeroValue
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionDegreeOneHomologyFreeRank
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionDegreeOneHomologyFreeRankIsZero
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionDegreeOneTorsionFactors
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionDegreeOneTorsionFactorsValue
#assert_no_axioms FX1Poly.Polygraph.Homology.WalkingInvolutionDegreeOneHomologyStatement
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionDegreeOneHomologyIsZmodTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionNullityOfDimOne
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionNullityOfDimOneValue
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionDegreeTwoHomologyFreeRank
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionDegreeTwoHomologyFreeRankIsZero
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionDimTwoHasNoTorsion
#assert_no_axioms FX1Poly.Polygraph.Homology.InvolutionDegreeTwoHomologyIsZeroStatement
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionDegreeTwoHomologyIsZero
#assert_no_axioms FX1Poly.Polygraph.Homology.InvolutionSmithHandoffStatement
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionSmithHandoff
#assert_no_axioms FX1Poly.Polygraph.Homology.decidedWalkerCount
#assert_no_axioms FX1Poly.Polygraph.Homology.walkersWithComputedHomologyCount
#assert_no_axioms FX1Poly.Polygraph.Homology.walkersWithComputedHomologyCountValue
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionHomologyLedgerIsComplete

end FX1PolyAudit
