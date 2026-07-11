import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.CrossedModuleTowerHopfBridge

/-! # FX1PolyAudit/Polygraph/Homology/CrossedModuleTowerHopfBridge — zero-axiom gate (the pi2/H2 CARRIER
    bridge between the crossed-module `ker(N)` and the periodic-tower `H_odd = ZZ/3` group rings, and the
    `(t-1)`-action Hopf-shadow matrix with `det = 3`)

Per-declaration zero-axiom gate for TOWER-ANICK r6 (#2144): the data bridge (`groupRingZmod3ToList`,
`listToGroupRingZmod3`, both round trips, the generator/norm/boundary identifications), the invariant
bridge (the augmentation agreement and the shared torsion constant `3 = epsilon(N)` tying
`pi_2 ~= ker(N)` to `H_1(tower) = ZZ/3`), and the Hopf-shadow bridge (the `(t-1)`-action matrix, its
column reconstructions, and `det = epsilon(N) = 3`), plus the ledger markers.

The `#assert_no_axioms` macro is fuel-based (`DependencyAudit`); as an INDEPENDENT cross-check the
load-bearing theorems are ALSO checked with the core `#print axioms` command (which does not truncate) —
each must report "does not depend on any axioms".

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- RUNG (i): the data bridge
#assert_no_axioms FX1Poly.Polygraph.Homology.groupRingZmod3ToList
#assert_no_axioms FX1Poly.Polygraph.Homology.listToGroupRingZmod3
#assert_no_axioms FX1Poly.Polygraph.Homology.listToGroupRingZmod3CancelsToList
#assert_no_axioms FX1Poly.Polygraph.Homology.groupRingZmod3ToListCancelsFromListOnTriple
#assert_no_axioms FX1Poly.Polygraph.Homology.crossedGeneratorsMapToTowerBasis
#assert_no_axioms FX1Poly.Polygraph.Homology.towerNormIsCrossedNorm
#assert_no_axioms FX1Poly.Polygraph.Homology.towerBoundaryIsCrossedBoundary

-- RUNG (ii): the invariant bridge
#assert_no_axioms FX1Poly.Polygraph.Homology.crossedAugmentationAgreesWithTowerAugmentation
#assert_no_axioms FX1Poly.Polygraph.Homology.crossedAndTowerNormAugmentationsAgree
#assert_no_axioms FX1Poly.Polygraph.Homology.crossedNormAugmentationIsThree
#assert_no_axioms FX1Poly.Polygraph.Homology.crossedNormAugTiesTowerOddTorsion

-- RUNG (iii): the Hopf-shadow bridge
#assert_no_axioms FX1Poly.Polygraph.Homology.groupRingTMinusOneAction
#assert_no_axioms FX1Poly.Polygraph.Homology.hopfRotationGeneratorOne
#assert_no_axioms FX1Poly.Polygraph.Homology.hopfRotationGeneratorTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.hopfShadowActionOnGeneratorOne
#assert_no_axioms FX1Poly.Polygraph.Homology.hopfShadowActionOnGeneratorTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.hopfShadowActionMatrix
#assert_no_axioms FX1Poly.Polygraph.Homology.hopfShadowColumnOneReconstructsAction
#assert_no_axioms FX1Poly.Polygraph.Homology.hopfShadowColumnTwoReconstructsAction
#assert_no_axioms FX1Poly.Polygraph.Homology.hopfShadowDeterminant
#assert_no_axioms FX1Poly.Polygraph.Homology.hopfShadowDeterminantIsThree
#assert_no_axioms FX1Poly.Polygraph.Homology.hopfShadowDeterminantEqualsNormAugmentation
#assert_no_axioms FX1Poly.Polygraph.Homology.hopfShadowCokerIsZmodThreeIsNamedNode

-- the ledger
#assert_no_axioms FX1Poly.Polygraph.Homology.TowerBridgeRungStatus
#assert_no_axioms FX1Poly.Polygraph.Homology.CrossedModuleTowerBridgeLedger
#assert_no_axioms FX1Poly.Polygraph.Homology.crossedModuleTowerBridgeLedger
#assert_no_axioms FX1Poly.Polygraph.Homology.crossedModuleTowerHopfBridgeIsComplete

/-! ### Independent `#print axioms` cross-check for the load-bearing decls (not trusting the fuel-based
    macro alone) — each must report "does not depend on any axioms". -/

#print axioms FX1Poly.Polygraph.Homology.listToGroupRingZmod3CancelsToList
#print axioms FX1Poly.Polygraph.Homology.towerNormIsCrossedNorm
#print axioms FX1Poly.Polygraph.Homology.towerBoundaryIsCrossedBoundary
#print axioms FX1Poly.Polygraph.Homology.crossedAugmentationAgreesWithTowerAugmentation
#print axioms FX1Poly.Polygraph.Homology.crossedNormAugTiesTowerOddTorsion
#print axioms FX1Poly.Polygraph.Homology.hopfShadowColumnOneReconstructsAction
#print axioms FX1Poly.Polygraph.Homology.hopfShadowColumnTwoReconstructsAction
#print axioms FX1Poly.Polygraph.Homology.hopfShadowDeterminantEqualsNormAugmentation

end FX1PolyAudit
