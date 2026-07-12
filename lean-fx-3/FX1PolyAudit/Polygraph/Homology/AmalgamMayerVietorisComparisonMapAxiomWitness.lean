import FX1Poly.Polygraph.Homology.AmalgamMayerVietorisComparisonMap

/-! # FX1PolyAudit.Polygraph.Homology.AmalgamMayerVietorisComparisonMapAxiomWitness — independent
    #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the
fuel-based `#assert_no_axioms` gate in the per-file twin) over every headline declaration of TOWER-MV
r2 — the Mayer-Vietoris comparison chain map (`comparisonIsChainMapDegree{One,Two,Three}`), the
instance-exactness package at degrees `0..2` (`comparisonAfterInclusionVanishes*`,
`inclusionIsInjective*`, `comparisonIsSurjective*`, `comparisonMiddleExactness*`), the degree-3
cokernel with the connecting-element seed (`comparisonDegreeThreeMissesCross`,
`connectingSeedIsMultiplicationDifference`, `amalgamMayerVietorisRankDefectIsCross`), the decided
torsion table (`amalgamMayerVietorisTorsionTable`), and the three round-2 markers.  Each must print
"does not depend on any axioms".  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.Homology.sharedEndoBasisCensus
#print axioms FX1Poly.Polygraph.Homology.comparisonIsChainMapDegreeOne
#print axioms FX1Poly.Polygraph.Homology.comparisonIsChainMapDegreeTwo
#print axioms FX1Poly.Polygraph.Homology.comparisonIsChainMapDegreeThree
#print axioms FX1Poly.Polygraph.Homology.comparisonAfterInclusionVanishesDegreeZero
#print axioms FX1Poly.Polygraph.Homology.comparisonAfterInclusionVanishesDegreeOne
#print axioms FX1Poly.Polygraph.Homology.inclusionIsInjectiveDegreeZero
#print axioms FX1Poly.Polygraph.Homology.inclusionIsInjectiveDegreeOne
#print axioms FX1Poly.Polygraph.Homology.comparisonIsSurjectiveDegreeZero
#print axioms FX1Poly.Polygraph.Homology.comparisonIsSurjectiveDegreeOne
#print axioms FX1Poly.Polygraph.Homology.comparisonIsSurjectiveDegreeTwo
#print axioms FX1Poly.Polygraph.Homology.amalgamInclusionDegreeZeroReducesToSmith
#print axioms FX1Poly.Polygraph.Homology.amalgamComparisonMapDegreeZeroReducesToSmith
#print axioms FX1Poly.Polygraph.Homology.amalgamComparisonMapDegreeTwoReducesToSmith
#print axioms FX1Poly.Polygraph.Homology.comparisonMiddleExactnessDegreeZero
#print axioms FX1Poly.Polygraph.Homology.comparisonMiddleExactnessDegreeOne
#print axioms FX1Poly.Polygraph.Homology.comparisonMiddleExactnessDegreeTwo
#print axioms FX1Poly.Polygraph.Homology.comparisonDegreeThreeMissesCross
#print axioms FX1Poly.Polygraph.Homology.connectingSeedIsMultiplicationDifference
#print axioms FX1Poly.Polygraph.Homology.amalgamMayerVietorisRankDefectIsCross
#print axioms FX1Poly.Polygraph.Homology.partDegreeOneHomologyIsZero
#print axioms FX1Poly.Polygraph.Homology.sharedEndoDegreeOneHomologyIsFreeRankOne
#print axioms FX1Poly.Polygraph.Homology.amalgamDegreeOneHomologyIsZero
#print axioms FX1Poly.Polygraph.Homology.sharedEndoDegreeTwoHomologyIsZero
#print axioms FX1Poly.Polygraph.Homology.amalgamMayerVietorisTorsionTable
#print axioms FX1Poly.Polygraph.Homology.amalgamComparisonChainMapIsLive
#print axioms FX1Poly.Polygraph.Homology.amalgamMayerVietorisConnectingSeedIsHonest
#print axioms FX1Poly.Polygraph.Homology.bimonoidBicomplexIsR3Bill

end FX1PolyAudit
