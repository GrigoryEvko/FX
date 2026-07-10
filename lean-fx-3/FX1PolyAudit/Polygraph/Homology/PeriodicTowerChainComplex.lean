import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.PeriodicTowerChainComplex

/-! # FX1PolyAudit/Polygraph/Homology/PeriodicTowerChainComplex — zero-axiom gate (the 2-PERIODIC
    group-homology tower of `ZZ/3`: the non-truncated `PeriodicTower` carrier + the periodicity
    certificate + the finite-check-to-infinite-conclusion `d d = 0` + the all-degrees read-off
    `H0 = ZZ, H_odd = ZZ/3, H_even>0 = 0` + the honest bridge to the Squier walker complex)

Per-declaration zero-axiom gate for TOWER-PERIODIC (#2146): the generic `PeriodicTower` structure and its
boundary function / periodicity certificate / rectangularity / scalar and windowed `d d = 0` /
augmentation obligation / ADC producer / chain-obligation corollary; the `ZZ/3` instance (the loop data,
the ONE loop check, the tower, the produced ADC, the 2-periodicity, the boundary parity over the tower,
the degree-10/11 truth probes); the SNF bridge (even/odd tower boundaries reduce to `[[0]]` / `[[3]]`);
the homology read-off (the parity Smith data, the degree-indexed data/invariant, the ★★ `H_odd = ZZ/3` at
every odd degree, `H_{even>0} = 0`, `H0 = ZZ`, the degree-9/10/11 probes, the odd-data reuse identity);
and the bridge/ledger (agreement at `H0`/`H1`/`H2`, divergence at `H3`, the non-truncation witness, the
truncation contrast at degree 4, the ledger + Squier-escape markers).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Homology.PeriodicTower
#assert_no_axioms FX1Poly.Polygraph.Homology.PeriodicTower.boundaryMatrix
#assert_no_axioms FX1Poly.Polygraph.Homology.PeriodicTower.boundaryPeriodicity
#assert_no_axioms FX1Poly.Polygraph.Homology.PeriodicTower.boundaryRectangular
#assert_no_axioms FX1Poly.Polygraph.Homology.PeriodicTower.boundaryScalarComposesToZero
#assert_no_axioms FX1Poly.Polygraph.Homology.PeriodicTower.boundaryComposesToZero
#assert_no_axioms FX1Poly.Polygraph.Homology.PeriodicTower.augmentationComposesToZero
#assert_no_axioms FX1Poly.Polygraph.Homology.PeriodicTower.toAugmentedDirectedComplex
#assert_no_axioms FX1Poly.Polygraph.Homology.PeriodicTower.chainComplexBoundaryComposesToZero
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreePeriodicLoopBoundaries
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreePeriodicLoopComposesToZero
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreePeriodicTower
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreePeriodicTowerChainComplex
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreePeriodicTowerBoundaryComposesToZero
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreePeriodicTowerBoundaryPeriodicity
#assert_no_axioms FX1Poly.Polygraph.Homology.natRemainderTwoOfDouble
#assert_no_axioms FX1Poly.Polygraph.Homology.natRemainderTwoOfDoubleSucc
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeTowerBoundaryOfEvenDegree
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeTowerBoundaryOfOddDegree
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeTowerBoundaryAtDegreeTen
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeTowerBoundaryAtDegreeEleven
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeTowerEvenBoundaryReducesToSmith
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeTowerOddBoundaryReducesToSmith
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeTowerOddDegreeSmithData
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeTowerEvenPositiveDegreeSmithData
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeTowerDegreeZeroSmithData
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeTowerHomologyDataAtDegree
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeTowerHomologyInvariantAtDegree
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeTowerOddDegreeSmithDataIsShipped
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeTowerDegreeZeroHomologyIsIntegers
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeTowerOddDegreeHomologyIsZmodThree
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeTowerEvenPositiveDegreeHomologyIsZero
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeTowerHomologyAtDegreeNine
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeTowerHomologyAtDegreeTen
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeTowerHomologyAtDegreeEleven
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreePeriodicTowerAgreesWithWalkerAtDegreeOne
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreePeriodicTowerAgreesWithWalkerAtDegreeTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeTowerHomologyAtDegreeThree
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreePeriodicTowerBasisIsNonzeroAtEveryDegree
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeWalkerCarrierTruncatesAtDegreeFour
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreePeriodicTowerIsAliveAtDegreeFour
#assert_no_axioms FX1Poly.Polygraph.Homology.towerPeriodicHomologyLedgerIsComplete
#assert_no_axioms FX1Poly.Polygraph.Homology.towerPeriodicSquierEscapeStaysScoped

end FX1PolyAudit
