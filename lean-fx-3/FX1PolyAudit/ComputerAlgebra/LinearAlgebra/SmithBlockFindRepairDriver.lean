import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithBlockFindRepairDriver

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithBlockFindRepairDriver — zero-axiom gate
    (H2-SMITH r45, #2261 — the corrected whole-block find repair + the find-none ⟺ block-divisibility
    bridge fires the r44 keystone at the corrected landing)

Per-declaration zero-axiom gate for the r45 corrected total driver: the whole-block find
(`smithFindNonDividingInBlock` + its scan helpers + the found-row range), the LOAD-BEARING bridge
`smithFindNonDividingInBlockNoneIffDivisibleWithin`, the corrected repair WORD
(`smithRepairPositionSweepClearingInBlock`) + its boundedness + r43 content invariance, the state-local
landing at the corrected driver (`smithRepairInBlockLandedFindNoneAbsEqInputMinorGcd`), the two KILLER
PINS, the corrected full driver, and the two r46-deferred residual Props named (uninhabited).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`.  Both the fuel-based `#assert_no_axioms` AND the independent (non-fuel) `#print axioms` are run
on every declaration (the project macro is fuel-based — not trusted alone). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.smithScanRowNonDividingInBlock
#assert_no_axioms FX1Poly.ComputerAlgebra.smithScanBlockNonDividing
#assert_no_axioms FX1Poly.ComputerAlgebra.smithFindNonDividingInBlock
#assert_no_axioms FX1Poly.ComputerAlgebra.smithScanBlockNonDividingSucc
#assert_no_axioms FX1Poly.ComputerAlgebra.smithScanRowNonDividingInBlockFoundRow
#assert_no_axioms FX1Poly.ComputerAlgebra.smithScanBlockNonDividingRowGe
#assert_no_axioms FX1Poly.ComputerAlgebra.smithFindNonDividingInBlockSomeRowGe
#assert_no_axioms FX1Poly.ComputerAlgebra.smithScanRowNonDividingInBlockNoneOfAllDivide
#assert_no_axioms FX1Poly.ComputerAlgebra.smithScanBlockNonDividingNoneOfAllDivide
#assert_no_axioms FX1Poly.ComputerAlgebra.smithScanRowNonDividingInBlockNoneAll
#assert_no_axioms FX1Poly.ComputerAlgebra.smithScanBlockNonDividingNoneAll
#assert_no_axioms FX1Poly.ComputerAlgebra.smithFindNonDividingInBlockNoneIffDivisibleWithin
#assert_no_axioms FX1Poly.ComputerAlgebra.smithRepairPositionSweepClearingInBlock
#assert_no_axioms FX1Poly.ComputerAlgebra.smithRepairPositionSweepClearingInBlockSucc
#assert_no_axioms FX1Poly.ComputerAlgebra.smithRepairPositionSweepClearingInBlockBoundedBelow
#assert_no_axioms FX1Poly.ComputerAlgebra.smithRepairInBlockPreservesMinorGcd
#assert_no_axioms FX1Poly.ComputerAlgebra.smithRepairInBlockLandedFindNoneAbsEqInputMinorGcd
#assert_no_axioms FX1Poly.ComputerAlgebra.blockFindKillerA
#assert_no_axioms FX1Poly.ComputerAlgebra.blockFindKillerAIsRectangular
#assert_no_axioms FX1Poly.ComputerAlgebra.blockKillerACorrectedLandsMinorGcd
#assert_no_axioms FX1Poly.ComputerAlgebra.blockKillerACorrectedLandsTwo
#assert_no_axioms FX1Poly.ComputerAlgebra.blockFindKillerB
#assert_no_axioms FX1Poly.ComputerAlgebra.blockFindKillerBIsRectangular
#assert_no_axioms FX1Poly.ComputerAlgebra.blockKillerBCorrectedLandsMinorGcd
#assert_no_axioms FX1Poly.ComputerAlgebra.blockKillerBCorrectedLandsOne
#assert_no_axioms FX1Poly.ComputerAlgebra.smithDivisibilityRepairSweepClearingInBlock
#assert_no_axioms FX1Poly.ComputerAlgebra.smithReduceCompleteInBlock
#assert_no_axioms FX1Poly.ComputerAlgebra.SmithReduceCompleteInBlockDriverStatement
#assert_no_axioms FX1Poly.ComputerAlgebra.SmithBlockRepairReachesFindNone

-- Independent (non-fuel) axiom prints on every declaration.
#print axioms FX1Poly.ComputerAlgebra.smithScanRowNonDividingInBlock
#print axioms FX1Poly.ComputerAlgebra.smithScanBlockNonDividing
#print axioms FX1Poly.ComputerAlgebra.smithFindNonDividingInBlock
#print axioms FX1Poly.ComputerAlgebra.smithScanBlockNonDividingSucc
#print axioms FX1Poly.ComputerAlgebra.smithScanRowNonDividingInBlockFoundRow
#print axioms FX1Poly.ComputerAlgebra.smithScanBlockNonDividingRowGe
#print axioms FX1Poly.ComputerAlgebra.smithFindNonDividingInBlockSomeRowGe
#print axioms FX1Poly.ComputerAlgebra.smithScanRowNonDividingInBlockNoneOfAllDivide
#print axioms FX1Poly.ComputerAlgebra.smithScanBlockNonDividingNoneOfAllDivide
#print axioms FX1Poly.ComputerAlgebra.smithScanRowNonDividingInBlockNoneAll
#print axioms FX1Poly.ComputerAlgebra.smithScanBlockNonDividingNoneAll
#print axioms FX1Poly.ComputerAlgebra.smithFindNonDividingInBlockNoneIffDivisibleWithin
#print axioms FX1Poly.ComputerAlgebra.smithRepairPositionSweepClearingInBlock
#print axioms FX1Poly.ComputerAlgebra.smithRepairPositionSweepClearingInBlockSucc
#print axioms FX1Poly.ComputerAlgebra.smithRepairPositionSweepClearingInBlockBoundedBelow
#print axioms FX1Poly.ComputerAlgebra.smithRepairInBlockPreservesMinorGcd
#print axioms FX1Poly.ComputerAlgebra.smithRepairInBlockLandedFindNoneAbsEqInputMinorGcd
#print axioms FX1Poly.ComputerAlgebra.blockFindKillerA
#print axioms FX1Poly.ComputerAlgebra.blockFindKillerAIsRectangular
#print axioms FX1Poly.ComputerAlgebra.blockKillerACorrectedLandsMinorGcd
#print axioms FX1Poly.ComputerAlgebra.blockKillerACorrectedLandsTwo
#print axioms FX1Poly.ComputerAlgebra.blockFindKillerB
#print axioms FX1Poly.ComputerAlgebra.blockFindKillerBIsRectangular
#print axioms FX1Poly.ComputerAlgebra.blockKillerBCorrectedLandsMinorGcd
#print axioms FX1Poly.ComputerAlgebra.blockKillerBCorrectedLandsOne
#print axioms FX1Poly.ComputerAlgebra.smithDivisibilityRepairSweepClearingInBlock
#print axioms FX1Poly.ComputerAlgebra.smithReduceCompleteInBlock
#print axioms FX1Poly.ComputerAlgebra.SmithReduceCompleteInBlockDriverStatement
#print axioms FX1Poly.ComputerAlgebra.SmithBlockRepairReachesFindNone

end FX1PolyAudit
