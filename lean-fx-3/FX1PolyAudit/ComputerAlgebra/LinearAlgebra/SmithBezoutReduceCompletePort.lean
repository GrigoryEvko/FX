import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithBezoutReduceCompletePort

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithBezoutReduceCompletePort — zero-axiom gate
    (H2-SMITH r48, #2261 — the Bezout-drop mandate scaffolding; the mandate stays honestly UNINHABITED)

Per-declaration zero-axiom gate for the r48 Bezout-drop reduce-complete port: the fuel domination
(`pivotMagnitudeWithinLeMinorAbsSum`), the cross-clean maintenance
(`smithBezoutRepairRoundAtFoundReEstablishesCrossClean`), the boundedness + content invariance
(`smithBezoutRepairRoundWordAtFoundBoundedBelow`, `smithBezoutRepairPositionSweepBoundedBelow`,
`smithBezoutRepairPositionSweepPreservesMinorGcd`), the single-position K2
(`smithBezoutLandedFindNoneAbsEqInputMinorGcd`), the reduction port (`smithReduceCompleteBezoutApplied`,
`smithReduceCompleteBezoutDiagonalNonneg`, `smithReduceCompleteBezoutDriverOfRepairInvariants`), the r49
gate reducer (`smithReduceCompleteBezoutMandateReducesToInvariants` over the uninhabited
`SmithBezoutRepairInvariantsStatement`), and the fuel-adequacy residual Prop
(`SmithBezoutRepairPositionSweepReachesFindNoneStatement`).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`.  Both the fuel-based `#assert_no_axioms` AND the independent (non-fuel) `#print axioms` are run
on every declaration (the project macro is fuel-based — not trusted alone). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.pivotMagnitudeWithinLeMinorAbsSum
#assert_no_axioms FX1Poly.ComputerAlgebra.smithBezoutRepairRoundAtFoundReEstablishesCrossClean
#assert_no_axioms FX1Poly.ComputerAlgebra.smithBezoutRepairRoundWordAtFoundBoundedBelow
#assert_no_axioms FX1Poly.ComputerAlgebra.smithBezoutRepairPositionSweepBoundedBelow
#assert_no_axioms FX1Poly.ComputerAlgebra.smithBezoutRepairPositionSweepPreservesMinorGcd
#assert_no_axioms FX1Poly.ComputerAlgebra.smithBezoutLandedFindNoneAbsEqInputMinorGcd
#assert_no_axioms FX1Poly.ComputerAlgebra.smithReduceCompleteBezoutApplied
#assert_no_axioms FX1Poly.ComputerAlgebra.smithReduceCompleteBezoutDiagonalNonneg
#assert_no_axioms FX1Poly.ComputerAlgebra.smithReduceCompleteBezoutDriverOfRepairInvariants
#assert_no_axioms FX1Poly.ComputerAlgebra.SmithBezoutRepairInvariantsStatement
#assert_no_axioms FX1Poly.ComputerAlgebra.smithReduceCompleteBezoutMandateReducesToInvariants
#assert_no_axioms FX1Poly.ComputerAlgebra.SmithBezoutRepairPositionSweepReachesFindNoneStatement

-- Independent (non-fuel) axiom prints on every declaration.
#print axioms FX1Poly.ComputerAlgebra.pivotMagnitudeWithinLeMinorAbsSum
#print axioms FX1Poly.ComputerAlgebra.smithBezoutRepairRoundAtFoundReEstablishesCrossClean
#print axioms FX1Poly.ComputerAlgebra.smithBezoutRepairRoundWordAtFoundBoundedBelow
#print axioms FX1Poly.ComputerAlgebra.smithBezoutRepairPositionSweepBoundedBelow
#print axioms FX1Poly.ComputerAlgebra.smithBezoutRepairPositionSweepPreservesMinorGcd
#print axioms FX1Poly.ComputerAlgebra.smithBezoutLandedFindNoneAbsEqInputMinorGcd
#print axioms FX1Poly.ComputerAlgebra.smithReduceCompleteBezoutApplied
#print axioms FX1Poly.ComputerAlgebra.smithReduceCompleteBezoutDiagonalNonneg
#print axioms FX1Poly.ComputerAlgebra.smithReduceCompleteBezoutDriverOfRepairInvariants
#print axioms FX1Poly.ComputerAlgebra.SmithBezoutRepairInvariantsStatement
#print axioms FX1Poly.ComputerAlgebra.smithReduceCompleteBezoutMandateReducesToInvariants
#print axioms FX1Poly.ComputerAlgebra.SmithBezoutRepairPositionSweepReachesFindNoneStatement

end FX1PolyAudit
