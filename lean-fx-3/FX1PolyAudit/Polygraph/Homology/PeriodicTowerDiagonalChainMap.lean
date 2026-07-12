import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.PeriodicTowerDiagonalChainMap

/-! # FX1PolyAudit/Polygraph/Homology/PeriodicTowerDiagonalChainMap — zero-axiom gate (the explicit
    Cartan-Eilenberg / Roberts diagonal `Delta : W -> W (X) W` on the `ZZ/n` periodic resolution,
    machine-checked as a chain map, and the cup product re-founded on the diagonal)

Per-declaration zero-axiom gate for TOWER-RING (#2147, r2): the tensor carrier + the group-ring boundary
coefficients + the four-parity-component diagonal (`diagonalEven` / `diagonalOdd`, the even-even <->
r1-shuffle bridge, the diagonal probes, the odd-odd counts); the Koszul tensor differential + the
diagonal-of-boundary + the normalizer + the four-parity-component chain-map equations
(`evenChainMapHolds` / `oddChainMapHolds`) with the 15 pins `n in {2,3,5}` x degree `{1..5}`; the derived
cup `cupFromDiagonal` + the pins reproducing the r1 products + the r1-agreement pins; and the GENERIC
selection lemma (`evenEvenSelectIsOne` via `pairSelectSum...`) + the generic derived-cup agreement
`cupFromDiagonalAgreesWithCupEvenPair` + graded-commutativity / associativity re-founded from r1, plus the
r3-residual named node and the r2 ledger marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Homology.TensorTerm
#assert_no_axioms FX1Poly.Polygraph.Homology.intBeq
#assert_no_axioms FX1Poly.Polygraph.Homology.intIsZero
#assert_no_axioms FX1Poly.Polygraph.Homology.keyEq
#assert_no_axioms FX1Poly.Polygraph.Homology.koszulSign
#assert_no_axioms FX1Poly.Polygraph.Homology.normElementCoeffs
#assert_no_axioms FX1Poly.Polygraph.Homology.tMinusOneCoeffs
#assert_no_axioms FX1Poly.Polygraph.Homology.generatorBoundaryCoeffs
#assert_no_axioms FX1Poly.Polygraph.Homology.liftSplitToEvenTerm
#assert_no_axioms FX1Poly.Polygraph.Homology.diagonalEvenEvenSummand
#assert_no_axioms FX1Poly.Polygraph.Homology.strictlyIncreasingPairs
#assert_no_axioms FX1Poly.Polygraph.Homology.diagonalOddOddSummand
#assert_no_axioms FX1Poly.Polygraph.Homology.diagonalEven
#assert_no_axioms FX1Poly.Polygraph.Homology.diagonalOdd
#assert_no_axioms FX1Poly.Polygraph.Homology.diagonalEvenEvenSummandIsShuffleLift
#assert_no_axioms FX1Poly.Polygraph.Homology.diagonalOddAtHalfZeroIsDegreeOneDiagonal
#assert_no_axioms FX1Poly.Polygraph.Homology.diagonalEvenAtHalfOneModulusThreeIsDegreeTwoDiagonal
#assert_no_axioms FX1Poly.Polygraph.Homology.strictlyIncreasingPairsCountModulusTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.strictlyIncreasingPairsCountModulusThree
#assert_no_axioms FX1Poly.Polygraph.Homology.strictlyIncreasingPairsCountModulusFive
#assert_no_axioms FX1Poly.Polygraph.Homology.tensorBoundaryLeft
#assert_no_axioms FX1Poly.Polygraph.Homology.tensorBoundaryRight
#assert_no_axioms FX1Poly.Polygraph.Homology.tensorBoundaryTerm
#assert_no_axioms FX1Poly.Polygraph.Homology.tensorBoundaryChain
#assert_no_axioms FX1Poly.Polygraph.Homology.rotateTerm
#assert_no_axioms FX1Poly.Polygraph.Homology.applyGroupRing
#assert_no_axioms FX1Poly.Polygraph.Homology.diagonalBoundaryEven
#assert_no_axioms FX1Poly.Polygraph.Homology.diagonalBoundaryOdd
#assert_no_axioms FX1Poly.Polygraph.Homology.canonicalizeTerm
#assert_no_axioms FX1Poly.Polygraph.Homology.insertTerm
#assert_no_axioms FX1Poly.Polygraph.Homology.collectTerms
#assert_no_axioms FX1Poly.Polygraph.Homology.dropZeroTerms
#assert_no_axioms FX1Poly.Polygraph.Homology.normalizeChain
#assert_no_axioms FX1Poly.Polygraph.Homology.chainSubsumes
#assert_no_axioms FX1Poly.Polygraph.Homology.chainAgrees
#assert_no_axioms FX1Poly.Polygraph.Homology.evenChainMapHolds
#assert_no_axioms FX1Poly.Polygraph.Homology.oddChainMapHolds
#assert_no_axioms FX1Poly.Polygraph.Homology.diagonalIsChainMapModulusTwoAtDegreeOne
#assert_no_axioms FX1Poly.Polygraph.Homology.diagonalIsChainMapModulusTwoAtDegreeTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.diagonalIsChainMapModulusTwoAtDegreeThree
#assert_no_axioms FX1Poly.Polygraph.Homology.diagonalIsChainMapModulusTwoAtDegreeFour
#assert_no_axioms FX1Poly.Polygraph.Homology.diagonalIsChainMapModulusTwoAtDegreeFive
#assert_no_axioms FX1Poly.Polygraph.Homology.diagonalIsChainMapModulusThreeAtDegreeOne
#assert_no_axioms FX1Poly.Polygraph.Homology.diagonalIsChainMapModulusThreeAtDegreeTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.diagonalIsChainMapModulusThreeAtDegreeThree
#assert_no_axioms FX1Poly.Polygraph.Homology.diagonalIsChainMapModulusThreeAtDegreeFour
#assert_no_axioms FX1Poly.Polygraph.Homology.diagonalIsChainMapModulusThreeAtDegreeFive
#assert_no_axioms FX1Poly.Polygraph.Homology.diagonalIsChainMapModulusFiveAtDegreeOne
#assert_no_axioms FX1Poly.Polygraph.Homology.diagonalIsChainMapModulusFiveAtDegreeTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.diagonalIsChainMapModulusFiveAtDegreeThree
#assert_no_axioms FX1Poly.Polygraph.Homology.diagonalIsChainMapModulusFiveAtDegreeFour
#assert_no_axioms FX1Poly.Polygraph.Homology.diagonalIsChainMapModulusFiveAtDegreeFive
#assert_no_axioms FX1Poly.Polygraph.Homology.evenEvenSelectSum
#assert_no_axioms FX1Poly.Polygraph.Homology.cupFromDiagonal
#assert_no_axioms FX1Poly.Polygraph.Homology.cupFromDiagonalSquareIsDegreeTwoGenerator
#assert_no_axioms FX1Poly.Polygraph.Homology.cupFromDiagonalCubeIsDegreeThreeGenerator
#assert_no_axioms FX1Poly.Polygraph.Homology.cupFromDiagonalFourthIsDegreeFourGenerator
#assert_no_axioms FX1Poly.Polygraph.Homology.cupFromDiagonalBilinearityProbe
#assert_no_axioms FX1Poly.Polygraph.Homology.cupFromDiagonalAgreesWithR1Square
#assert_no_axioms FX1Poly.Polygraph.Homology.cupFromDiagonalAgreesWithR1Cube
#assert_no_axioms FX1Poly.Polygraph.Homology.cupFromDiagonalAgreesWithR1Fourth
#assert_no_axioms FX1Poly.Polygraph.Homology.natBeqSelf
#assert_no_axioms FX1Poly.Polygraph.Homology.boolAndFalse
#assert_no_axioms FX1Poly.Polygraph.Homology.natBeqDouble
#assert_no_axioms FX1Poly.Polygraph.Homology.pairSelectSum
#assert_no_axioms FX1Poly.Polygraph.Homology.evenEvenSelectSumOfLift
#assert_no_axioms FX1Poly.Polygraph.Homology.pairSelectSumShiftSucc
#assert_no_axioms FX1Poly.Polygraph.Homology.pairSelectSumShiftZero
#assert_no_axioms FX1Poly.Polygraph.Homology.pairSelectSumAtLeftSum
#assert_no_axioms FX1Poly.Polygraph.Homology.pairSelectSumAtSum
#assert_no_axioms FX1Poly.Polygraph.Homology.evenEvenSelectIsOne
#assert_no_axioms FX1Poly.Polygraph.Homology.cupFromDiagonalAgreesWithCupEvenPair
#assert_no_axioms FX1Poly.Polygraph.Homology.cupFromDiagonalGradedCommutes
#assert_no_axioms FX1Poly.Polygraph.Homology.cupFromDiagonalAssociates
#assert_no_axioms FX1Poly.Polygraph.Homology.diagonalGenericChainMapIsNamedNode
#assert_no_axioms FX1Poly.Polygraph.Homology.periodicTowerDiagonalChainMapLedgerIsComplete

end FX1PolyAudit
