import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.PeriodicTowerContractingHomotopy

/-! # FX1PolyAudit/Polygraph/Homology/PeriodicTowerContractingHomotopy — zero-axiom gate (the
    assembled contracting homotopy `d s + s d = id` of the `ZZ/3` 2-periodic group-ring resolution,
    the all-degrees kernel-witness exactness, the augmentation exactness, the module-side `d d = 0`,
    the tensor tie to the shipped tower literals, and the linearity/equivariance certificates)

Per-declaration zero-axiom gate for the TOWER-ANICK / TOWER-PERIODIC exactness brick: the small
`Int` cancellation kit; the dense `ZZ[ZZ/3]` record carrier with its module maps (t-action, `t - 1`,
norm, augmentation, section, both homotopy legs); the three homotopy identities (degree 0, odd,
even-positive) and the seam periodicity; the degree-indexed boundary/homotopy actions with the
all-positive-degrees identity; the kernel witnesses (positive degrees + augmentation) and the
augmentation splitting; the module-side `d d = 0` and `eps d_1 = 0`; the tensor ties to the shipped
`boundaryMatrix 0/1` entries and the Anick-telescope list-carrier bridges; the additivity and
`t`-equivariance certificates with the not-`t`-equivariant honesty probe; and the exactness package
+ the two honest-record markers.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Homology.intZeroSub
#assert_no_axioms FX1Poly.Polygraph.Homology.intSubZero
#assert_no_axioms FX1Poly.Polygraph.Homology.intAddZeroAddZero
#assert_no_axioms FX1Poly.Polygraph.Homology.intAddSubCancel
#assert_no_axioms FX1Poly.Polygraph.Homology.intNegAddAddCancel
#assert_no_axioms FX1Poly.Polygraph.Homology.intAddRotateLeft
#assert_no_axioms FX1Poly.Polygraph.Homology.intSubAddExchange
#assert_no_axioms FX1Poly.Polygraph.Homology.intThreeMulIsTripleSum
#assert_no_axioms FX1Poly.Polygraph.Homology.CyclicThreeGroupRingElement
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeElementCongr
#assert_no_axioms FX1Poly.Polygraph.Homology.addCyclicThreeElements
#assert_no_axioms FX1Poly.Polygraph.Homology.zeroCyclicThreeElement
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeBasisUnit
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeMultiplyByT
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeMultiplyByTMinusOne
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeElementAugmentation
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeMultiplyByNorm
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeAugmentationSection
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeHomotopyEvenToOdd
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeHomotopyOddToEven
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeHomotopyIdentityAtDegreeZero
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeHomotopyIdentityAtOddDegree
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeHomotopyOfNormIsAugmentationSection
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeHomotopyIdentityAtEvenPositiveDegree
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeResolutionBoundaryAction
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeContractingHomotopyAction
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeContractingHomotopyIdentityAtEveryPositiveDegree
#assert_no_axioms FX1Poly.Polygraph.Homology.addCyclicThreeElementsZeroRight
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeContractingHomotopyOfZeroIsZero
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeResolutionKernelWitnessAtEveryPositiveDegree
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeAugmentationKernelWitness
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeAugmentationSectionSplits
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeNormCycleProbe
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeNormCycleProbeIsNonzero
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeNormCycleProbeIsCycle
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeNormCycleProbeReceivesWitness
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeDeepDegreeCycleProbe
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeDeepDegreeCycleProbeIsNonzero
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeDeepDegreeCycleProbeIsCycle
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeDeepDegreeCycleProbeReceivesWitness
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeDeepDegreeCycleProbeWitnessComputes
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeAugmentationKillsBoundary
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeResolutionBoundaryComposesToZero
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeEvenBoundaryTensorsToShippedEntry
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeOddBoundaryTensorsToShippedEntry
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeElementAugmentationMatchesListAugmentation
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeNormOnBasisUnitIsShippedNorm
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeBoundaryOnBasisUnitIsShippedBoundaryElement
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeElementAugmentationIsAdditive
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeOddBoundaryIsAdditive
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeEvenBoundaryIsAdditive
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeHomotopyEvenToOddIsAdditive
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeHomotopyOddToEvenIsAdditive
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeOddBoundaryCommutesWithT
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeEvenBoundaryCommutesWithT
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeHomotopyIsNotTEquivariant
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreePeriodicResolutionIsExactWithExplicitWitnesses
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeResolutionContractingHomotopyIsAssembled
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeResolutionExactnessScopeStaysHonest

end FX1PolyAudit
