import FX1Poly.Polygraph.Homology.PeriodicTowerCohomologyCupProduct

/-! # FX1PolyAudit.Polygraph.Homology.PeriodicTowerCohomologyCupProductAxiomWitness — independent #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the fuel-based
`#assert_no_axioms` gate in the per-file twin) over every headline declaration of the TOWER-RING (#2147)
r1 opener — the dual cochain complex + the cohomology read-off `H^0 = ZZ, H^even>0 = ZZ/n, H^odd = 0` +
the explicit even-degree diagonal + the cup product with its ring-law certificates + the torsion relation
`n·x = 0` at n = 2, 3, 4.  Each must print "does not depend on any axioms".  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.Homology.PeriodicTower.cochainCoboundaryComposesToZero
#print axioms FX1Poly.Polygraph.Homology.cyclicThreeTowerCoboundaryOfEvenDegree
#print axioms FX1Poly.Polygraph.Homology.cyclicThreeTowerCoboundaryOfOddDegree
#print axioms FX1Poly.Polygraph.Homology.cyclicThreePeriodicTowerCochainComposesToZero
#print axioms FX1Poly.Polygraph.Homology.cyclicThreeCohomEvenPositiveIsHomologyOdd
#print axioms FX1Poly.Polygraph.Homology.cyclicThreeCohomEvenPositiveDegreeIsZmodThree
#print axioms FX1Poly.Polygraph.Homology.cyclicThreeCohomOddDegreeIsZero
#print axioms FX1Poly.Polygraph.Homology.cyclicThreeCohomAtDegreeTwoIsZmodThree
#print axioms FX1Poly.Polygraph.Homology.cyclicThreeCohomDegreeTwoMatchesHomologyDegreeOne
#print axioms FX1Poly.Polygraph.Homology.cohomEvenPositiveInvariantForModulusTwo
#print axioms FX1Poly.Polygraph.Homology.cohomEvenPositiveInvariantForModulusThree
#print axioms FX1Poly.Polygraph.Homology.cohomEvenPositiveInvariantForModulusFour
#print axioms FX1Poly.Polygraph.Homology.cyclicTorsionRelationVanishesAtTwo
#print axioms FX1Poly.Polygraph.Homology.cyclicTorsionRelationVanishesAtThree
#print axioms FX1Poly.Polygraph.Homology.cyclicTorsionRelationVanishesAtFour
#print axioms FX1Poly.Polygraph.Homology.diagonalEvenShuffleLength
#print axioms FX1Poly.Polygraph.Homology.diagonalEvenShuffleSumsAtThree
#print axioms FX1Poly.Polygraph.Homology.cupGeneratorSquareIsDegreeTwoGenerator
#print axioms FX1Poly.Polygraph.Homology.cupEvenGeneratorLeftAdditive
#print axioms FX1Poly.Polygraph.Homology.cupEvenGeneratorRightAdditive
#print axioms FX1Poly.Polygraph.Homology.cupEvenPairAssociative
#print axioms FX1Poly.Polygraph.Homology.cupEvenPairGradedCommutes
#print axioms FX1Poly.Polygraph.Homology.cupRightUnit
#print axioms FX1Poly.Polygraph.Homology.cupLeftUnit
#print axioms FX1Poly.Polygraph.Homology.periodicTowerCohomologyRingLedgerIsComplete

end FX1PolyAudit
