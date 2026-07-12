import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.PeriodicTowerCohomologyCupProduct

/-! # FX1PolyAudit/Polygraph/Homology/PeriodicTowerCohomologyCupProduct — zero-axiom gate (the COHOMOLOGY
    ring of `ZZ/n` on the shipped 2-periodic tower: the dual cochain complex + the read-off `H^0 = ZZ,
    H^even>0 = ZZ/n, H^odd = 0` + the explicit even-degree diagonal + the cup product with its
    bilinearity / associativity / graded-commutativity / unit certificates + the torsion relation
    `n·x = 0` at n = 2, 3, 4)

Per-declaration zero-axiom gate for TOWER-RING (#2147, r1): the cochain complex (the coboundary, the
cochain `δ δ = 0`, the even/odd parity, the ZZ/3 corollary, the degree-8/9 probes); the cohomology
read-off (the three parity cohomology Smith data, the two dualization swap witnesses, the degree-indexed
data/invariant, the ★★ `H^even>0 = ZZ/3` at every positive even degree, `H^odd = 0`, `H^0 = ZZ`, `H^2 =
ZZ/3`, the degree-8/9/10 probes, the dimension-shift bridge to homology degree 1); the per-`n` cohomology
(the modulus family, `H^even(ZZ/n) = ZZ/n` for n = 2/3/4, the tower match, the torsion relations `n·x = 0`
at n = 2/3/4); the cup product + explicit diagonal (`cupEvenPair`/`cupEvenGenerator`, the generator/unit,
the pair bridge, the map-length helper, the shuffle + its length + the shuffle/sum probes); and the ring
certificates (the first computed products `x∪x=x²`/`x∪x²=x³`/`x²∪x²=x⁴`, the right/left unit,
graded-commutativity on pairs/generators, bilinearity left/right, associativity on pairs/generators, the
ledger marker).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Homology.PeriodicTower.cochainCoboundary
#assert_no_axioms FX1Poly.Polygraph.Homology.PeriodicTower.cochainCoboundaryComposesToZero
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeTowerCoboundaryOfEvenDegree
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeTowerCoboundaryOfOddDegree
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreePeriodicTowerCochainComposesToZero
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeTowerCoboundaryAtDegreeEight
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeTowerCoboundaryAtDegreeNine
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeCohomDegreeZeroSmithData
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeCohomOddDegreeSmithData
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeCohomEvenPositiveDegreeSmithData
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeCohomEvenPositiveIsHomologyOdd
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeCohomOddIsHomologyEvenPositive
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeCohomHomologyDataAtDegree
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeCohomInvariantAtDegree
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeCohomDegreeZeroIsIntegers
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeCohomEvenPositiveDegreeIsZmodThree
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeCohomOddDegreeIsZero
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeCohomAtDegreeTwoIsZmodThree
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeCohomAtDegreeEight
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeCohomAtDegreeNine
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeCohomAtDegreeTen
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeCohomDegreeTwoMatchesHomologyDegreeOne
#assert_no_axioms FX1Poly.Polygraph.Homology.cohomEvenPositiveDegreeSmithDataForModulus
#assert_no_axioms FX1Poly.Polygraph.Homology.cohomEvenPositiveInvariantForModulusTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.cohomEvenPositiveInvariantForModulusThree
#assert_no_axioms FX1Poly.Polygraph.Homology.cohomEvenPositiveInvariantForModulusFour
#assert_no_axioms FX1Poly.Polygraph.Homology.cohomEvenPositiveForModulusThreeMatchesTower
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicTorsionRelationVanishesAtTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicTorsionRelationVanishesAtThree
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicTorsionRelationVanishesAtFour
#assert_no_axioms FX1Poly.Polygraph.Homology.cupEvenPair
#assert_no_axioms FX1Poly.Polygraph.Homology.cupEvenGenerator
#assert_no_axioms FX1Poly.Polygraph.Homology.cohomGeneratorX
#assert_no_axioms FX1Poly.Polygraph.Homology.cohomRingUnit
#assert_no_axioms FX1Poly.Polygraph.Homology.cupEvenGeneratorIsCupEvenPair
#assert_no_axioms FX1Poly.Polygraph.Homology.natPairMapPreservesLength
#assert_no_axioms FX1Poly.Polygraph.Homology.diagonalEvenShuffle
#assert_no_axioms FX1Poly.Polygraph.Homology.diagonalEvenShuffleLength
#assert_no_axioms FX1Poly.Polygraph.Homology.diagonalEvenShuffleAtOne
#assert_no_axioms FX1Poly.Polygraph.Homology.diagonalEvenShuffleAtTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.allPairsSumTo
#assert_no_axioms FX1Poly.Polygraph.Homology.diagonalEvenShuffleSumsAtTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.diagonalEvenShuffleSumsAtThree
#assert_no_axioms FX1Poly.Polygraph.Homology.cupGeneratorSquareIsDegreeTwoGenerator
#assert_no_axioms FX1Poly.Polygraph.Homology.cupGeneratorCubeIsDegreeThreeGenerator
#assert_no_axioms FX1Poly.Polygraph.Homology.cupGeneratorFourthIsDegreeFourGenerator
#assert_no_axioms FX1Poly.Polygraph.Homology.cupRightUnit
#assert_no_axioms FX1Poly.Polygraph.Homology.cupEvenPairGradedCommutes
#assert_no_axioms FX1Poly.Polygraph.Homology.cupEvenGeneratorGradedCommutes
#assert_no_axioms FX1Poly.Polygraph.Homology.cupLeftUnit
#assert_no_axioms FX1Poly.Polygraph.Homology.cupEvenGeneratorLeftAdditive
#assert_no_axioms FX1Poly.Polygraph.Homology.cupEvenGeneratorRightAdditive
#assert_no_axioms FX1Poly.Polygraph.Homology.cupEvenPairAssociative
#assert_no_axioms FX1Poly.Polygraph.Homology.cupEvenGeneratorAssociative
#assert_no_axioms FX1Poly.Polygraph.Homology.periodicTowerCohomologyRingLedgerIsComplete

end FX1PolyAudit
