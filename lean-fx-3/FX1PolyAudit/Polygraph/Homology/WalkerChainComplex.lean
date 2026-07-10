import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.WalkerChainComplex

/-! # FX1PolyAudit/Polygraph/Homology/WalkerChainComplex — zero-axiom gate (the walking-monad
    polygraphic chain complex + machine-checked `d d = 0` + Smith-normal boundaries)

Per-declaration zero-axiom gate for the H2-CHAIN r1 walking-monad chain complex: the basis counts,
the generic and instance `d d = 0` theorems, the three boundary-matrix literals, the augmented
directed complex instance, the oracle / non-vacuity smokes, and the two Smith reduction certificates
seeding the H2-WALKERS handoff.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Homology.walkerBasisCount
#assert_no_axioms FX1Poly.Polygraph.Homology.augmentedDirectedComplexBoundaryComposesToZero
#assert_no_axioms FX1Poly.Polygraph.Homology.monadCriticalPairBoundaryColumn
#assert_no_axioms FX1Poly.Polygraph.Homology.walkerBoundaryOfDimZero
#assert_no_axioms FX1Poly.Polygraph.Homology.walkerBoundaryOfDimOne
#assert_no_axioms FX1Poly.Polygraph.Homology.walkerBoundaryOfDimTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.walkerBoundaryMatrix
#assert_no_axioms FX1Poly.Polygraph.Homology.walkerBoundaryComposesToZero
#assert_no_axioms FX1Poly.Polygraph.Homology.walkerChainComplex
#assert_no_axioms FX1Poly.Polygraph.Homology.walkerChainComplexBoundaryComposesToZero
#assert_no_axioms FX1Poly.Polygraph.Homology.monadCriticalPairIndex
#assert_no_axioms FX1Poly.Polygraph.Homology.walkerBoundaryDimTwoColumnMatchesCriticalPair
#assert_no_axioms FX1Poly.Polygraph.Homology.walkerBoundaryDimOneMatchesOracle
#assert_no_axioms FX1Poly.Polygraph.Homology.walkerBoundaryDimZeroMatchesOracle
#assert_no_axioms FX1Poly.Polygraph.Homology.walkerBoundaryDimTwoIsNonzero
#assert_no_axioms FX1Poly.Polygraph.Homology.walkerBoundaryDimOneIsNonzero
#assert_no_axioms FX1Poly.Polygraph.Homology.walkerChainComplexIsNonVacuous
#assert_no_axioms FX1Poly.Polygraph.Homology.walkerBoundaryOfDimOneSmithCertificate
#assert_no_axioms FX1Poly.Polygraph.Homology.walkerBoundaryOfDimOneReducesToSmith
#assert_no_axioms FX1Poly.Polygraph.Homology.walkerBoundaryOfDimTwoSmithCertificate
#assert_no_axioms FX1Poly.Polygraph.Homology.walkerBoundaryOfDimTwoReducesToSmith
#assert_no_axioms FX1Poly.Polygraph.Homology.WalkerDegreeTwoSmithHandoffStatement
#assert_no_axioms FX1Poly.Polygraph.Homology.walkerDegreeTwoSmithHandoff
#assert_no_axioms FX1Poly.Polygraph.Homology.walkerSmithNormalFormOfDimOne
#assert_no_axioms FX1Poly.Polygraph.Homology.walkerSmithNormalFormOfDimTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.walkerDimOneCertificateProducesSmithNormalForm
#assert_no_axioms FX1Poly.Polygraph.Homology.walkerDimTwoCertificateProducesSmithNormalForm
#assert_no_axioms FX1Poly.Polygraph.Homology.smithRankWithin
#assert_no_axioms FX1Poly.Polygraph.Homology.walkerRankOfDimOne
#assert_no_axioms FX1Poly.Polygraph.Homology.walkerRankOfDimTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.walkerNullityOfDimOne
#assert_no_axioms FX1Poly.Polygraph.Homology.walkerNullityOfDimOneValue
#assert_no_axioms FX1Poly.Polygraph.Homology.walkerDegreeTwoHomologyFreeRank
#assert_no_axioms FX1Poly.Polygraph.Homology.walkerDegreeTwoHomologyFreeRankIsZero
#assert_no_axioms FX1Poly.Polygraph.Homology.hasNoSmithTorsionWithin
#assert_no_axioms FX1Poly.Polygraph.Homology.walkerDimTwoHasNoTorsion
#assert_no_axioms FX1Poly.Polygraph.Homology.WalkerDegreeTwoHomologyIsZeroStatement
#assert_no_axioms FX1Poly.Polygraph.Homology.walkerDegreeTwoHomologyIsZero
#assert_no_axioms FX1Poly.Polygraph.Homology.monadCriticalPairOverlapCell
#assert_no_axioms FX1Poly.Polygraph.Homology.allMonadCriticalPairs
#assert_no_axioms FX1Poly.Polygraph.Homology.monadCriticalPairCountIsFive
#assert_no_axioms FX1Poly.Polygraph.Homology.allMonadCriticalPairsExhaustive
#assert_no_axioms FX1Poly.Polygraph.Homology.walkerHomologyLedgerIsComplete

end FX1PolyAudit
