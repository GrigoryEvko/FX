import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithFoldDescentRefuted

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithFoldDescentRefuted — zero-axiom gate
    (H2-SMITH r31, #2261 — the single-fold descent obligation is FALSE)

Per-declaration zero-axiom gate for the r31 refutation of `SmithFoldDescendsOnNonzeroPivot`
(`smithFoldDescendsOnNonzeroPivotIsRefuted`, the headline negative theorem), its counterexample
precondition facts, the boundary hinge `smithFoldAfterFoldPivotEqOfFoundColumnZero`, and the
driver-reachable dirty-found-column witness `smithDirtyFoundColumnIsFindSomeReachable`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`.  Both the fuel-based `#assert_no_axioms` AND the independent (non-fuel)
`#print axioms` are run on every declaration (the project macro is fuel-based — not trusted alone). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.smithFoldDescentCounterexampleIsRectangular
#assert_no_axioms FX1Poly.ComputerAlgebra.smithFoldDescentCounterexamplePivotPositive
#assert_no_axioms FX1Poly.ComputerAlgebra.smithFoldDescentCounterexampleFindsSome
#assert_no_axioms FX1Poly.ComputerAlgebra.smithFoldStepRaisesPivotOnCounterexample
#assert_no_axioms FX1Poly.ComputerAlgebra.smithFoldDescendsOnNonzeroPivotIsRefuted
#assert_no_axioms FX1Poly.ComputerAlgebra.smithFoldAfterFoldPivotEqOfFoundColumnZero
#assert_no_axioms FX1Poly.ComputerAlgebra.smithDirtyFoundColumnIsFindSomeReachable

-- Independent (non-fuel) axiom prints on every declaration.
#print axioms FX1Poly.ComputerAlgebra.smithFoldDescentCounterexampleIsRectangular
#print axioms FX1Poly.ComputerAlgebra.smithFoldDescentCounterexamplePivotPositive
#print axioms FX1Poly.ComputerAlgebra.smithFoldDescentCounterexampleFindsSome
#print axioms FX1Poly.ComputerAlgebra.smithFoldStepRaisesPivotOnCounterexample
#print axioms FX1Poly.ComputerAlgebra.smithFoldDescendsOnNonzeroPivotIsRefuted
#print axioms FX1Poly.ComputerAlgebra.smithFoldAfterFoldPivotEqOfFoundColumnZero
#print axioms FX1Poly.ComputerAlgebra.smithDirtyFoundColumnIsFindSomeReachable

end FX1PolyAudit
