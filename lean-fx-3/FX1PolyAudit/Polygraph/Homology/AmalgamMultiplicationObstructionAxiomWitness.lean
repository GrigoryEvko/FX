import FX1Poly.Polygraph.Homology.AmalgamMultiplicationObstruction

/-! # FX1PolyAudit.Polygraph.Homology.AmalgamMultiplicationObstructionAxiomWitness — independent
    #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the
fuel-based `#assert_no_axioms` gate in the per-file twin) over every headline declaration of TOWER-MV
r1 — the double-monoid amalgam chain complex, its degree-`0..2` homology `H2(amalgam) = 0`, the
part-embedding Mayer-Vietoris seed, and the first machine-checked amalgamation-obstruction 2-cocycle
`crossCycleEscapesPartBoundarySpan` (with the Fubini linearity upgrade
`cocycleAnnihilatesEveryPartCombination`), plus the bimonoid `-2` no-go and the two round-1 markers.
Each must print "does not depend on any axioms".  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.Homology.doubleMonoidAmalgam
#print axioms FX1Poly.Polygraph.Homology.amalgamComputesBoundaryDimOne
#print axioms FX1Poly.Polygraph.Homology.amalgamComputesBoundaryDimTwo
#print axioms FX1Poly.Polygraph.Homology.amalgamIsWellFormed
#print axioms FX1Poly.Polygraph.Homology.amalgamBoundaryComposesToZero
#print axioms FX1Poly.Polygraph.Homology.amalgamChainComplex
#print axioms FX1Poly.Polygraph.Homology.amalgamAblockMatchesMonad
#print axioms FX1Poly.Polygraph.Homology.amalgamBblockMatchesMonad
#print axioms FX1Poly.Polygraph.Homology.amalgamBoundaryOfDimOneReducesToSmith
#print axioms FX1Poly.Polygraph.Homology.amalgamBoundaryOfDimTwoReducesToSmith
#print axioms FX1Poly.Polygraph.Homology.amalgamRankOfDimTwo
#print axioms FX1Poly.Polygraph.Homology.amalgamDegreeTwoHomologyFreeRankIsZero
#print axioms FX1Poly.Polygraph.Homology.amalgamDimTwoHasNoTorsion
#print axioms FX1Poly.Polygraph.Homology.amalgamDegreeTwoHomologyIsZero
#print axioms FX1Poly.Polygraph.Homology.amalgamCrossCellBoundaryIsMultiplicationDifference
#print axioms FX1Poly.Polygraph.Homology.amalgamMultiplicationDifferenceIsCycle
#print axioms FX1Poly.Polygraph.Homology.cocycleVanishesOnPartBoundaries
#print axioms FX1Poly.Polygraph.Homology.cocycleAnnihilatesEveryPartCombination
#print axioms FX1Poly.Polygraph.Homology.cocycleDetectsCross
#print axioms FX1Poly.Polygraph.Homology.crossCycleEscapesPartBoundarySpan
#print axioms FX1Poly.Polygraph.Homology.bimonoidCrossCoforkBoundaryIsMinusTwo
#print axioms FX1Poly.Polygraph.Homology.bimonoidNaiveUnionFailsChainCondition
#print axioms FX1Poly.Polygraph.Homology.amalgamObstructionCocycleIsLive
#print axioms FX1Poly.Polygraph.Homology.amalgamMayerVietorisSeedIsHonest

end FX1PolyAudit
