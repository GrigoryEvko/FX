import FX1Poly.Polygraph.Homology.PeriodicTowerContractingHomotopy

/-! # FX1PolyAudit.Polygraph.Homology.PeriodicTowerContractingHomotopyAxiomWitness — independent
    #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the
fuel-based `#assert_no_axioms` gate in the per-file twin) over every headline declaration of the
`ZZ/3` periodic-resolution contracting-homotopy brick — the three `d s + s d = id` identities, the
all-degrees packaging, the kernel-witness exactness (positive degrees + augmentation), the
module-side `d d = 0`, the tensor ties to the shipped tower literals, the not-`t`-equivariant
honesty probe, and the exactness package.  Each must print "does not depend on any axioms". -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.Homology.cyclicThreeHomotopyIdentityAtDegreeZero
#print axioms FX1Poly.Polygraph.Homology.cyclicThreeHomotopyIdentityAtOddDegree
#print axioms FX1Poly.Polygraph.Homology.cyclicThreeHomotopyIdentityAtEvenPositiveDegree
#print axioms FX1Poly.Polygraph.Homology.cyclicThreeHomotopyOfNormIsAugmentationSection
#print axioms FX1Poly.Polygraph.Homology.cyclicThreeContractingHomotopyIdentityAtEveryPositiveDegree
#print axioms FX1Poly.Polygraph.Homology.cyclicThreeResolutionKernelWitnessAtEveryPositiveDegree
#print axioms FX1Poly.Polygraph.Homology.cyclicThreeAugmentationKernelWitness
#print axioms FX1Poly.Polygraph.Homology.cyclicThreeAugmentationSectionSplits
#print axioms FX1Poly.Polygraph.Homology.cyclicThreeNormCycleProbeIsNonzero
#print axioms FX1Poly.Polygraph.Homology.cyclicThreeNormCycleProbeReceivesWitness
#print axioms FX1Poly.Polygraph.Homology.cyclicThreeDeepDegreeCycleProbeIsNonzero
#print axioms FX1Poly.Polygraph.Homology.cyclicThreeDeepDegreeCycleProbeReceivesWitness
#print axioms FX1Poly.Polygraph.Homology.cyclicThreeDeepDegreeCycleProbeWitnessComputes
#print axioms FX1Poly.Polygraph.Homology.cyclicThreeAugmentationKillsBoundary
#print axioms FX1Poly.Polygraph.Homology.cyclicThreeResolutionBoundaryComposesToZero
#print axioms FX1Poly.Polygraph.Homology.cyclicThreeEvenBoundaryTensorsToShippedEntry
#print axioms FX1Poly.Polygraph.Homology.cyclicThreeOddBoundaryTensorsToShippedEntry
#print axioms FX1Poly.Polygraph.Homology.cyclicThreeElementAugmentationMatchesListAugmentation
#print axioms FX1Poly.Polygraph.Homology.cyclicThreeNormOnBasisUnitIsShippedNorm
#print axioms FX1Poly.Polygraph.Homology.cyclicThreeBoundaryOnBasisUnitIsShippedBoundaryElement
#print axioms FX1Poly.Polygraph.Homology.cyclicThreeOddBoundaryCommutesWithT
#print axioms FX1Poly.Polygraph.Homology.cyclicThreeEvenBoundaryCommutesWithT
#print axioms FX1Poly.Polygraph.Homology.cyclicThreeHomotopyIsNotTEquivariant
#print axioms FX1Poly.Polygraph.Homology.cyclicThreePeriodicResolutionIsExactWithExplicitWitnesses
#print axioms FX1Poly.Polygraph.Homology.cyclicThreeResolutionContractingHomotopyIsAssembled
#print axioms FX1Poly.Polygraph.Homology.cyclicThreeResolutionExactnessScopeStaysHonest

end FX1PolyAudit
