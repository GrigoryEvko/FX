import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.AmalgamMayerVietorisComparisonMap

/-! # FX1PolyAudit/Polygraph/Homology/AmalgamMayerVietorisComparisonMap — zero-axiom gate (the
    Mayer-Vietoris comparison chain map, instance exactness at degrees `0..2`, the degree-3 cokernel
    with the connecting-element seed, and the decided parts-vs-amalgam torsion table)

Per-declaration zero-axiom gate for TOWER-MV r2 (the Mayer-Vietoris comparison round): the shared
walking-endo substructure; the local product-entry helper; the comparison map `beta`, the inclusion
`alpha`, and the direct-sum boundaries; the chain-map equations at degrees 1, 2, 3; the SES exactness
package (`beta . alpha = 0`, injectivity, surjectivity, the Smith rank-identity middle exactness); the
degree-3 cokernel `ZZ<cross>` with the connecting-element seed and the rank defect; and the decided
torsion table (part `H1 = 0`, shared `H1 = ZZ`, amalgam `H1 = 0`, no torsion).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Homology.sharedEndoPresentation
#assert_no_axioms FX1Poly.Polygraph.Homology.comparisonProductEntry
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamComparisonMapDegreeZero
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamComparisonMapDegreeOne
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamComparisonMapDegreeTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamComparisonMapDegreeThree
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamInclusionDegreeZero
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamInclusionDegreeOne
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamInclusionDegreeTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamInclusionDegreeThree
#assert_no_axioms FX1Poly.Polygraph.Homology.directSumBoundaryDimZero
#assert_no_axioms FX1Poly.Polygraph.Homology.directSumBoundaryDimOne
#assert_no_axioms FX1Poly.Polygraph.Homology.directSumBoundaryDimTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.sharedEndoBasisCensus
#assert_no_axioms FX1Poly.Polygraph.Homology.comparisonIsChainMapDegreeOne
#assert_no_axioms FX1Poly.Polygraph.Homology.comparisonIsChainMapDegreeTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.comparisonIsChainMapDegreeThree
#assert_no_axioms FX1Poly.Polygraph.Homology.comparisonAfterInclusionVanishesDegreeZero
#assert_no_axioms FX1Poly.Polygraph.Homology.comparisonAfterInclusionVanishesDegreeOne
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamInclusionLeftInverse
#assert_no_axioms FX1Poly.Polygraph.Homology.inclusionIsInjectiveDegreeZero
#assert_no_axioms FX1Poly.Polygraph.Homology.inclusionIsInjectiveDegreeOne
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamComparisonRightInverseDegreeZero
#assert_no_axioms FX1Poly.Polygraph.Homology.comparisonIsSurjectiveDegreeZero
#assert_no_axioms FX1Poly.Polygraph.Homology.comparisonIsSurjectiveDegreeOne
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamComparisonRightInverseDegreeTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamIdentityDegreeTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.comparisonIsSurjectiveDegreeTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamInclusionDegreeZeroSmithCertificate
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamInclusionDegreeZeroSmithNormalForm
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamInclusionDegreeZeroProducesSmithNormalForm
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamInclusionDegreeZeroReducesToSmith
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamComparisonMapDegreeZeroSmithCertificate
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamComparisonMapDegreeZeroSmithNormalForm
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamComparisonMapDegreeZeroProducesSmithNormalForm
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamComparisonMapDegreeZeroReducesToSmith
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamComparisonMapDegreeTwoSmithCertificate
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamComparisonMapDegreeTwoProducesSmithNormalForm
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamComparisonMapDegreeTwoReducesToSmith
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamInclusionRankLowDegree
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamInclusionRankDegreeTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamComparisonNullityLowDegree
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamComparisonNullityDegreeTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.comparisonMiddleExactnessDegreeZero
#assert_no_axioms FX1Poly.Polygraph.Homology.comparisonMiddleExactnessDegreeOne
#assert_no_axioms FX1Poly.Polygraph.Homology.comparisonMiddleExactnessDegreeTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.comparisonDegreeThreeMissesCross
#assert_no_axioms FX1Poly.Polygraph.Homology.connectingSeedIsMultiplicationDifference
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamMayerVietorisRankDefectIsCross
#assert_no_axioms FX1Poly.Polygraph.Homology.sharedEndoSmithNormalFormOfDimZero
#assert_no_axioms FX1Poly.Polygraph.Homology.sharedEndoSmithNormalFormOfDimOne
#assert_no_axioms FX1Poly.Polygraph.Homology.sharedEndoComputesBoundaryDimZero
#assert_no_axioms FX1Poly.Polygraph.Homology.sharedEndoComputesBoundaryDimOne
#assert_no_axioms FX1Poly.Polygraph.Homology.partDegreeOneHomologyFreeRank
#assert_no_axioms FX1Poly.Polygraph.Homology.partDegreeOneHomologyIsZero
#assert_no_axioms FX1Poly.Polygraph.Homology.sharedEndoDegreeOneHomologyFreeRank
#assert_no_axioms FX1Poly.Polygraph.Homology.sharedEndoDegreeOneHomologyIsFreeRankOne
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamDegreeOneHomologyFreeRank
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamDegreeOneHomologyIsZero
#assert_no_axioms FX1Poly.Polygraph.Homology.sharedEndoDegreeTwoHomologyIsZero
#assert_no_axioms FX1Poly.Polygraph.Homology.partDegreeOneHasNoTorsion
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamDegreeOneHasNoTorsion
#assert_no_axioms FX1Poly.Polygraph.Homology.AmalgamMayerVietorisTorsionTableStatement
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamMayerVietorisTorsionTable
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamComparisonChainMapIsLive
#assert_no_axioms FX1Poly.Polygraph.Homology.amalgamMayerVietorisConnectingSeedIsHonest
#assert_no_axioms FX1Poly.Polygraph.Homology.bimonoidBicomplexIsR3Bill

end FX1PolyAudit
