import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.PolygraphHomologyFinitenessInvariant

/-! # FX1PolyAudit/Polygraph/Homology/PolygraphHomologyFinitenessInvariant — zero-axiom gate (the
    finite `HomologyInvariant (freeRank, torsionFactors)`, the single generic Smith read-off, the
    generic finiteness bound `freeRank(H_k) ≤ C_k`, and the four-walker EXHIBITION recovering
    `H2(monad) = 0`, `H1(involution) = ZZ/2`, `H1(cyclic-3) = ZZ/3`, `H1(idempotent) = 0`)

Per-declaration zero-axiom gate for H2-SQUIER-NOGO r1 brick B1.  Every declaration must be free of
`propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Homology.HomologyInvariant
#assert_no_axioms FX1Poly.Polygraph.Homology.nonUnitInvariantFactors
#assert_no_axioms FX1Poly.Polygraph.Homology.SmithHomologyData
#assert_no_axioms FX1Poly.Polygraph.Homology.SmithHomologyData.homologyInvariant
#assert_no_axioms FX1Poly.Polygraph.Homology.homologyInvariantFreeRankBoundedByBasis
#assert_no_axioms FX1Poly.Polygraph.Homology.monadDegreeTwoSmithData
#assert_no_axioms FX1Poly.Polygraph.Homology.walkingMonadDegreeTwoHomologyInvariant
#assert_no_axioms FX1Poly.Polygraph.Homology.monadDegreeTwoSmithDataComputesInvariant
#assert_no_axioms FX1Poly.Polygraph.Homology.monadDegreeTwoSmithDataMatchesShippedFreeRank
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionDegreeOneSmithData
#assert_no_axioms FX1Poly.Polygraph.Homology.walkingInvolutionDegreeOneHomologyInvariant
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionDegreeOneSmithDataComputesInvariant
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionDegreeOneSmithDataMatchesShippedReadOff
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeDegreeOneSmithData
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeDegreeOneHomologyInvariant
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeDegreeOneSmithDataComputesInvariant
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeDegreeOneSmithDataMatchesShippedReadOff
#assert_no_axioms FX1Poly.Polygraph.Homology.idempotentSemigroupDegreeOneSmithData
#assert_no_axioms FX1Poly.Polygraph.Homology.idempotentSemigroupDegreeOneHomologyInvariant
#assert_no_axioms FX1Poly.Polygraph.Homology.idempotentSemigroupDegreeOneSmithDataComputesInvariant
#assert_no_axioms FX1Poly.Polygraph.Homology.idempotentSemigroupDegreeOneSmithDataMatchesShippedReadOff
#assert_no_axioms FX1Poly.Polygraph.Homology.walkingInvolutionInvariantDiffersFromTrivial
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionAndCyclicThreeInvariantsDiffer
#assert_no_axioms FX1Poly.Polygraph.Homology.polygraphHomologyFinitenessInvariantLedgerIsComplete

end FX1PolyAudit
