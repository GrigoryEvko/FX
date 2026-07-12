import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.AmalgamMultiplicationObstruction

/-! # FX1PolyAudit/Polygraph/Homology/AmalgamMultiplicationObstruction — zero-axiom gate (the
    double-monoid amalgam chain complex, its degree-`0..2` homology, and the first machine-checked
    amalgamation-obstruction 2-cocycle)

Per-declaration zero-axiom gate for TOWER-MV r1 (the amalgamation-homology opener): the finite-sum
Fubini / distributivity kit; the `doubleMonoidAmalgam` presentation + literal boundaries + census
pins; the well-formed complex `amalgamChainComplex` (`d d = 0` via the shipped generic assembler); the
part-embedding Mayer-Vietoris chain-level seed; the Smith read-off `H2(amalgam) = 0`; the obstruction
2-cocycle `phi` with `crossCycleEscapesPartBoundarySpan` (the first machine-checked amalgamation
obstruction); the bimonoid `-2` no-go; and the two round-1 markers.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Homology.sumOverIndicesCongrEverywhere
#assert_no_axioms FX1Poly.Polygraph.Homology.sumOverIndicesZeroWithinBound
#assert_no_axioms FX1Poly.Polygraph.Homology.sumOverIndicesLeftDistrib
#assert_no_axioms FX1Poly.Polygraph.Homology.sumOverIndicesAdd
#assert_no_axioms FX1Poly.Polygraph.Homology.sumOverIndicesSwap
#assert_no_axioms FX1Poly.Polygraph.Homology.columnIndexOutOfRangeAbsurd
#assert_no_axioms FX1Poly.Polygraph.Homology.doubleMonoidAmalgam
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamBoundaryOfDimOne
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamBoundaryOfDimTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamComputesBoundaryDimOne
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamComputesBoundaryDimTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamIsWellFormed
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamBoundaryComposesToZero
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamChainComplex
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamAblockMatchesMonad
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamBblockMatchesMonad
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamBoundaryOfDimOneSmithCertificate
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamBoundaryOfDimOneReducesToSmith
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamBoundaryOfDimTwoSmithCertificate
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamBoundaryOfDimTwoReducesToSmith
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamSmithNormalFormOfDimOne
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamSmithNormalFormOfDimTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamDimOneCertificateProducesSmithNormalForm
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamDimTwoCertificateProducesSmithNormalForm
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamRankOfDimOne
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamRankOfDimTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamNullityOfDimOne
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamNullityOfDimOneValue
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamDegreeTwoHomologyFreeRank
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamDegreeTwoHomologyFreeRankIsZero
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamDimTwoHasNoTorsion
#assert_no_axioms FX1Poly.Polygraph.Homology.AmalgamDegreeTwoHomologyIsZeroStatement
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamDegreeTwoHomologyIsZero
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamMultiplicationDifference
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamCrossThreeCell
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamCrossCellBoundaryIsMultiplicationDifference
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamMultiplicationDifferenceIsCycle
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamationCocycle
#assert_no_axioms FX1Poly.Polygraph.Homology.partBoundaryCombinationCoordinate
#assert_no_axioms FX1Poly.Polygraph.Homology.cocycleVanishesOnPartBoundaries
#assert_no_axioms FX1Poly.Polygraph.Homology.cocycleAnnihilatesEveryPartCombination
#assert_no_axioms FX1Poly.Polygraph.Homology.cocycleDetectsCross
#assert_no_axioms FX1Poly.Polygraph.Homology.crossCycleEscapesPartBoundarySpan
#assert_no_axioms FX1Poly.Polygraph.Homology.bimonoidBoundaryOfDimOne
#assert_no_axioms FX1Poly.Polygraph.Homology.bimonoidCrossCoforkColumn
#assert_no_axioms FX1Poly.Polygraph.Homology.bimonoidCrossCoforkBoundaryIsMinusTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.bimonoidNaiveUnionFailsChainCondition
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamObstructionCocycleIsLive
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamMayerVietorisSeedIsHonest

end FX1PolyAudit
