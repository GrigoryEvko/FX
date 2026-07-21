import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithBezoutReduceCompletePort

/-! # Smith-Bezout reduce-complete port -- zero-axiom gate

Per-declaration zero-axiom gate for the Bezout-drop reduce-complete port: fuel domination, cross-clean
maintenance, boundedness and content invariance, the single-position landed characterization, the
reduction port, the invariants-gate reducer over the uninhabited `SmithBezoutRepairInvariantsStatement`,
and the fuel-adequacy residual Prop. Every declaration must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. Both the fuel-based `#assert_no_axioms` and the
independent `#print axioms` run on every declaration. -/

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
