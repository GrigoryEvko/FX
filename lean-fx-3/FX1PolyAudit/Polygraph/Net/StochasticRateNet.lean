import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Net.StochasticRateNet

/-! # FX1PolyAudit/Polygraph/Net/StochasticRateNet — zero-axiom gate
    (NET-15 brick: stochastic rate nets → CTMC generator extraction)

Per-declaration zero-axiom gate for the stochastic-rate-net kit: the rated carrier
(`SrnTransition`/`SrnNet`) and firing (`srnFireEnabled`/`srnFireTarget`), the
structural-fuel reachable-set BFS (`srnSuccessors`, `srnMarkingMem`,
`srnInsertMarking`/`srnInsertAll`, `srnExpandRound`, `srnReachSaturate`,
`srnReachableMarkings`, `srnMarkingIndex`), the exit rate (`srnExitRate`), the CTMC
generator (`srnGeneratorOffDiag`, `srnGeneratorEntry`, `srnGeneratorRow`,
`srnGeneratorMatrixAux`/`srnGeneratorMatrix`), the row-sum fold with its append law
(`srnRowSum`, `srnQnfConcat`, `srnRowSumCat`), the embedded jump chain
(`srnEmbeddedJumpEntry`, `srnExitRatePositive`), the CROWN row-sum-zero soundness
(`srnBalancedRowSumsToZero`), the walls, and the ground fires.

The unbounded-state-space and stationary-distribution claims are WALLED
(`srnHasUnboundedStateSpace = false`, `srnHasStationaryDistribution = false`): the
finite-state enumeration of an unbounded net needs the Petri-net coverability
well-quasi-order — the NET-4 impossibility
`FX1Poly.ComputerAlgebra.fxNet4_dicksonWall` (`WellFounded.fix`) — and the
steady-state solve `π Q = 0` is the distinct NET-16 Gaussian-elimination rung.
`srnUnboundedWallEqualsDickson` equates the marker to the Dickson wall by `rfl`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`, `funext`, `WellFounded.fix`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Net.SrnTransition
#assert_no_axioms FX1Poly.Polygraph.Net.SrnTransition.mk
#assert_no_axioms FX1Poly.Polygraph.Net.SrnNet
#assert_no_axioms FX1Poly.Polygraph.Net.SrnNet.mk
#assert_no_axioms FX1Poly.Polygraph.Net.srnFireEnabled
#assert_no_axioms FX1Poly.Polygraph.Net.srnFireTarget
#assert_no_axioms FX1Poly.Polygraph.Net.srnSuccessors
#assert_no_axioms FX1Poly.Polygraph.Net.srnMarkingMem
#assert_no_axioms FX1Poly.Polygraph.Net.srnInsertMarking
#assert_no_axioms FX1Poly.Polygraph.Net.srnInsertAll
#assert_no_axioms FX1Poly.Polygraph.Net.srnExpandRound
#assert_no_axioms FX1Poly.Polygraph.Net.srnReachSaturate
#assert_no_axioms FX1Poly.Polygraph.Net.srnReachableMarkings
#assert_no_axioms FX1Poly.Polygraph.Net.srnMarkingIndex
#assert_no_axioms FX1Poly.Polygraph.Net.srnExitRate
#assert_no_axioms FX1Poly.Polygraph.Net.srnGeneratorOffDiag
#assert_no_axioms FX1Poly.Polygraph.Net.srnGeneratorEntry
#assert_no_axioms FX1Poly.Polygraph.Net.srnGeneratorRow
#assert_no_axioms FX1Poly.Polygraph.Net.srnGeneratorMatrixAux
#assert_no_axioms FX1Poly.Polygraph.Net.srnGeneratorMatrix
#assert_no_axioms FX1Poly.Polygraph.Net.srnRowSum
#assert_no_axioms FX1Poly.Polygraph.Net.srnQnfConcat
#assert_no_axioms FX1Poly.Polygraph.Net.srnRowSumCat
#assert_no_axioms FX1Poly.Polygraph.Net.srnEmbeddedJumpEntry
#assert_no_axioms FX1Poly.Polygraph.Net.srnExitRatePositive
#assert_no_axioms FX1Poly.Polygraph.Net.srnBalancedRowSumsToZero
#assert_no_axioms FX1Poly.Polygraph.Net.srnHasUnboundedStateSpace
#assert_no_axioms FX1Poly.Polygraph.Net.srnHasStationaryDistribution
#assert_no_axioms FX1Poly.Polygraph.Net.srnUnboundedWallEqualsDickson
#assert_no_axioms FX1Poly.Polygraph.Net.srnHasGeneratorExtraction
#assert_no_axioms FX1Poly.Polygraph.Net.srnHasRowSumZeroSoundness
#assert_no_axioms FX1Poly.Polygraph.Net.srnHalf
#assert_no_axioms FX1Poly.Polygraph.Net.srnThird
#assert_no_axioms FX1Poly.Polygraph.Net.srnSixth
#assert_no_axioms FX1Poly.Polygraph.Net.srnMoveAB
#assert_no_axioms FX1Poly.Polygraph.Net.srnMoveBA
#assert_no_axioms FX1Poly.Polygraph.Net.srnToggleNet
#assert_no_axioms FX1Poly.Polygraph.Net.srnCycleA
#assert_no_axioms FX1Poly.Polygraph.Net.srnCycleB
#assert_no_axioms FX1Poly.Polygraph.Net.srnCycleC
#assert_no_axioms FX1Poly.Polygraph.Net.srnCycleNet
#assert_no_axioms FX1Poly.Polygraph.Net.srnFireEnabledToggle
#assert_no_axioms FX1Poly.Polygraph.Net.srnFireTargetToggle
#assert_no_axioms FX1Poly.Polygraph.Net.srnFireDisabledToggle
#assert_no_axioms FX1Poly.Polygraph.Net.srnExitRateToggle
#assert_no_axioms FX1Poly.Polygraph.Net.srnExitRateDisabledSkips
#assert_no_axioms FX1Poly.Polygraph.Net.srnMarkingIndexToggle
#assert_no_axioms FX1Poly.Polygraph.Net.srnReachableToggle
#assert_no_axioms FX1Poly.Polygraph.Net.srnReachableCycle
#assert_no_axioms FX1Poly.Polygraph.Net.srnGeneratorRowToggleSumsZero
#assert_no_axioms FX1Poly.Polygraph.Net.srnGeneratorRowToggleSumsZeroOther
#assert_no_axioms FX1Poly.Polygraph.Net.srnGeneratorRowCycleSumsZero
#assert_no_axioms FX1Poly.Polygraph.Net.srnEmbeddedJumpToggleOne

end FX1PolyAudit
