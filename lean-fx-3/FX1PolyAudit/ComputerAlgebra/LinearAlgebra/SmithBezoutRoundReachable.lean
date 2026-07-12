import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithBezoutRoundReachable

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithBezoutRoundReachable — zero-axiom gate
    (H2-SMITH r47, #2261 — the Bezout-drop sibling round's per-round strict descent K1)

Per-declaration zero-axiom gate for the Bezout-drop round: the magnitude/sign bridges, the whole-block
find-`some` property extraction, the divides-zero/self facts, the strictly-interior-offender lemma, the
Bezout-drop round defs, the K1 strict-descent headline
(`smithBezoutRoundStrictlyDescendsOnCleanCross`), the sibling driver
(`smithReduceCompleteBezout`), and the uninhabited sibling mandate Prop
(`SmithReduceCompleteBezoutDriverStatement`).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`.  Both the fuel-based `#assert_no_axioms` AND the independent (non-fuel)
`#print axioms` are run on every declaration (the project macro is fuel-based — not trusted alone). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.smithPivotCrossClean
#assert_no_axioms FX1Poly.ComputerAlgebra.intMagnitudeRemainderOnNatAbs
#assert_no_axioms FX1Poly.ComputerAlgebra.intMagnitudeRemainderNatAbsCongr
#assert_no_axioms FX1Poly.ComputerAlgebra.smithPivotDividesEntryNatAbsCongr
#assert_no_axioms FX1Poly.ComputerAlgebra.smithSignNormalizeOpsPreservesRowMagnitude
#assert_no_axioms FX1Poly.ComputerAlgebra.smithScanRowNonDividingInBlockFound
#assert_no_axioms FX1Poly.ComputerAlgebra.smithScanBlockNonDividingFound
#assert_no_axioms FX1Poly.ComputerAlgebra.smithFindNonDividingInBlockSomeProperties
#assert_no_axioms FX1Poly.ComputerAlgebra.smithPivotDividesEntryZero
#assert_no_axioms FX1Poly.ComputerAlgebra.smithPivotDividesEntrySelf
#assert_no_axioms FX1Poly.ComputerAlgebra.smithBezoutOffenderInterior
#assert_no_axioms FX1Poly.ComputerAlgebra.smithBezoutRepairRoundAtFound
#assert_no_axioms FX1Poly.ComputerAlgebra.smithBezoutRepairRound
#assert_no_axioms FX1Poly.ComputerAlgebra.smithBezoutRepairRoundAtFoundStrictlyDescends
#assert_no_axioms FX1Poly.ComputerAlgebra.smithBezoutRoundStrictlyDescendsOnCleanCross
#assert_no_axioms FX1Poly.ComputerAlgebra.smithBezoutRepairRoundWordAtFound
#assert_no_axioms FX1Poly.ComputerAlgebra.smithBezoutRepairPositionSweep
#assert_no_axioms FX1Poly.ComputerAlgebra.smithBezoutDivisibilityRepairSweep
#assert_no_axioms FX1Poly.ComputerAlgebra.smithReduceCompleteBezout
#assert_no_axioms FX1Poly.ComputerAlgebra.SmithReduceCompleteBezoutDriverStatement

-- Independent (non-fuel) axiom prints on every declaration.
#print axioms FX1Poly.ComputerAlgebra.smithPivotCrossClean
#print axioms FX1Poly.ComputerAlgebra.intMagnitudeRemainderOnNatAbs
#print axioms FX1Poly.ComputerAlgebra.intMagnitudeRemainderNatAbsCongr
#print axioms FX1Poly.ComputerAlgebra.smithPivotDividesEntryNatAbsCongr
#print axioms FX1Poly.ComputerAlgebra.smithSignNormalizeOpsPreservesRowMagnitude
#print axioms FX1Poly.ComputerAlgebra.smithScanRowNonDividingInBlockFound
#print axioms FX1Poly.ComputerAlgebra.smithScanBlockNonDividingFound
#print axioms FX1Poly.ComputerAlgebra.smithFindNonDividingInBlockSomeProperties
#print axioms FX1Poly.ComputerAlgebra.smithPivotDividesEntryZero
#print axioms FX1Poly.ComputerAlgebra.smithPivotDividesEntrySelf
#print axioms FX1Poly.ComputerAlgebra.smithBezoutOffenderInterior
#print axioms FX1Poly.ComputerAlgebra.smithBezoutRepairRoundAtFound
#print axioms FX1Poly.ComputerAlgebra.smithBezoutRepairRound
#print axioms FX1Poly.ComputerAlgebra.smithBezoutRepairRoundAtFoundStrictlyDescends
#print axioms FX1Poly.ComputerAlgebra.smithBezoutRoundStrictlyDescendsOnCleanCross
#print axioms FX1Poly.ComputerAlgebra.smithBezoutRepairRoundWordAtFound
#print axioms FX1Poly.ComputerAlgebra.smithBezoutRepairPositionSweep
#print axioms FX1Poly.ComputerAlgebra.smithBezoutDivisibilityRepairSweep
#print axioms FX1Poly.ComputerAlgebra.smithReduceCompleteBezout
#print axioms FX1Poly.ComputerAlgebra.SmithReduceCompleteBezoutDriverStatement

end FX1PolyAudit
