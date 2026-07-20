import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Net.StationaryDistribution

/-! # FX1PolyAudit/Polygraph/Net/StationaryDistribution — zero-axiom gate
    (NET-16 brick: exact stationary distributions of finite CTMCs)

Per-declaration zero-axiom gate for the stationary-distribution solver: the matrix /
vector algebra (`stnGet`, `stnScale`, `stnAxpy`, `stnClearRows`, `stnColumn`,
`stnVecDot`, `stnMatVec`, `stnTake`, `stnDrop`, `stnHeads`, `stnTails`,
`stnTransposeAux`, `stnFirstRowLength`, `stnTranspose`, `stnSnoc`, `stnZeros`,
`stnOnes`), the augmented balance system (`stnPinRow`, `stnMapAppendZero`,
`stnNullSpaceSystem`), the structural-fuel Gaussian elimination (`stnForward`,
`stnBack`, `stnRowReduce`, `stnSolveSystem`), the stationary read-off
(`stnNullSpaceVector`, `stnNormalise`, `stnStationaryOf`), the DECIDED marker and the
three WALLS (`stnHasStationaryDistribution = true`; `stnHasInfiniteStateStationary`,
`stnHasReducibleUniqueness`, `stnHasTransientDistribution = false`) with the
Dickson-tie theorem, and every ground fire (toggle `π = [2/5, 3/5]`, cyclic
`π = [2/11, 3/11, 6/11]`, column-side balance `π Q = 0`, `Σ π = 1`).
-/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Net.StnMatrix
#assert_no_axioms FX1Poly.Polygraph.Net.stnGet
#assert_no_axioms FX1Poly.Polygraph.Net.stnScale
#assert_no_axioms FX1Poly.Polygraph.Net.stnAxpy
#assert_no_axioms FX1Poly.Polygraph.Net.stnClearRows
#assert_no_axioms FX1Poly.Polygraph.Net.stnColumn
#assert_no_axioms FX1Poly.Polygraph.Net.stnVecDot
#assert_no_axioms FX1Poly.Polygraph.Net.stnMatVec
#assert_no_axioms FX1Poly.Polygraph.Net.stnTake
#assert_no_axioms FX1Poly.Polygraph.Net.stnDrop
#assert_no_axioms FX1Poly.Polygraph.Net.stnHeads
#assert_no_axioms FX1Poly.Polygraph.Net.stnTails
#assert_no_axioms FX1Poly.Polygraph.Net.stnTransposeAux
#assert_no_axioms FX1Poly.Polygraph.Net.stnFirstRowLength
#assert_no_axioms FX1Poly.Polygraph.Net.stnTranspose
#assert_no_axioms FX1Poly.Polygraph.Net.stnSnoc
#assert_no_axioms FX1Poly.Polygraph.Net.stnZeros
#assert_no_axioms FX1Poly.Polygraph.Net.stnOnes
#assert_no_axioms FX1Poly.Polygraph.Net.stnPinRow
#assert_no_axioms FX1Poly.Polygraph.Net.stnMapAppendZero
#assert_no_axioms FX1Poly.Polygraph.Net.stnNullSpaceSystem
#assert_no_axioms FX1Poly.Polygraph.Net.stnForward
#assert_no_axioms FX1Poly.Polygraph.Net.stnBack
#assert_no_axioms FX1Poly.Polygraph.Net.stnRowReduce
#assert_no_axioms FX1Poly.Polygraph.Net.stnSolveSystem
#assert_no_axioms FX1Poly.Polygraph.Net.stnNullSpaceVector
#assert_no_axioms FX1Poly.Polygraph.Net.stnNormalise
#assert_no_axioms FX1Poly.Polygraph.Net.stnStationaryOf
#assert_no_axioms FX1Poly.Polygraph.Net.stnHasStationaryDistribution
#assert_no_axioms FX1Poly.Polygraph.Net.stnHasInfiniteStateStationary
#assert_no_axioms FX1Poly.Polygraph.Net.stnHasReducibleUniqueness
#assert_no_axioms FX1Poly.Polygraph.Net.stnHasTransientDistribution
#assert_no_axioms FX1Poly.Polygraph.Net.stnInfiniteWallEqualsUnbounded
#assert_no_axioms FX1Poly.Polygraph.Net.stnToggleGen
#assert_no_axioms FX1Poly.Polygraph.Net.stnCycleGen
#assert_no_axioms FX1Poly.Polygraph.Net.stnTwoFifths
#assert_no_axioms FX1Poly.Polygraph.Net.stnThreeFifths
#assert_no_axioms FX1Poly.Polygraph.Net.stnThreeHalves
#assert_no_axioms FX1Poly.Polygraph.Net.stnTwoElevenths
#assert_no_axioms FX1Poly.Polygraph.Net.stnThreeElevenths
#assert_no_axioms FX1Poly.Polygraph.Net.stnSixElevenths
#assert_no_axioms FX1Poly.Polygraph.Net.stnToggleTransposeShape
#assert_no_axioms FX1Poly.Polygraph.Net.stnToggleRowReduce
#assert_no_axioms FX1Poly.Polygraph.Net.stnToggleNullVector
#assert_no_axioms FX1Poly.Polygraph.Net.stnToggleStationary
#assert_no_axioms FX1Poly.Polygraph.Net.stnToggleSumsToOne
#assert_no_axioms FX1Poly.Polygraph.Net.stnToggleBalanceColumnZero
#assert_no_axioms FX1Poly.Polygraph.Net.stnToggleBalanceColumnOne
#assert_no_axioms FX1Poly.Polygraph.Net.stnCycleStationary
#assert_no_axioms FX1Poly.Polygraph.Net.stnCycleSumsToOne
#assert_no_axioms FX1Poly.Polygraph.Net.stnCycleBalanceColumnZero
#assert_no_axioms FX1Poly.Polygraph.Net.stnCycleBalanceColumnOne
#assert_no_axioms FX1Poly.Polygraph.Net.stnCycleBalanceColumnTwo
#assert_no_axioms FX1Poly.Polygraph.Net.stnInfiniteStateStationaryIsFalse
#assert_no_axioms FX1Poly.Polygraph.Net.stnReducibleUniquenessIsFalse
#assert_no_axioms FX1Poly.Polygraph.Net.stnTransientDistributionIsFalse
#assert_no_axioms FX1Poly.Polygraph.Net.stnStationaryDistributionIsTrue

end FX1PolyAudit
