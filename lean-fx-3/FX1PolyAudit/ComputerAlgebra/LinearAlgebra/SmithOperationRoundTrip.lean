import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithOperationRoundTrip

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithOperationRoundTrip — zero-axiom gate
    (H2-SMITH reconnection, Part B — the operation-inversion kit)

Per-declaration zero-axiom gate for the operation round-trip kit: the Bool identities, the generic
`listReplaceAt` algebra atoms, the pair-swap self-inverse, the six per-constructor matrix round-trips,
the whole-word fold round-trip, and the B2 boundedness transport.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

/- Bool identities (hand-rolled by `cases`). -/
#assert_no_axioms FX1Poly.ComputerAlgebra.boolAndTrueRight
#assert_no_axioms FX1Poly.ComputerAlgebra.boolTrueAndLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.boolAndCommute
#assert_no_axioms FX1Poly.ComputerAlgebra.boolAndAssociate

/- Generic `listReplaceAt` / `listModifyAt` / `mapAllRows` algebra atoms. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.listReplaceAtCollapse
#assert_no_axioms FX1Poly.ComputerAlgebra.listReplaceAtCommute
#assert_no_axioms FX1Poly.ComputerAlgebra.listReplaceAtIdentity
#assert_no_axioms FX1Poly.ComputerAlgebra.listModifyAtCancelAt
#assert_no_axioms FX1Poly.ComputerAlgebra.mapAllRowsCancel
#assert_no_axioms FX1Poly.ComputerAlgebra.intMatrixEqOfRowsEq

/- The pair-swap self-inverse (shared by row and column swaps). -/
#assert_no_axioms FX1Poly.ComputerAlgebra.listPairSwap
#assert_no_axioms FX1Poly.ComputerAlgebra.listPairSwapExpand
#assert_no_axioms FX1Poly.ComputerAlgebra.listPairSwapSame
#assert_no_axioms FX1Poly.ComputerAlgebra.listPairSwapSelfInverse
#assert_no_axioms FX1Poly.ComputerAlgebra.swapRowsRowsEq
#assert_no_axioms FX1Poly.ComputerAlgebra.swapRowsSelfInverse
#assert_no_axioms FX1Poly.ComputerAlgebra.swapEntriesWithinRowEq
#assert_no_axioms FX1Poly.ComputerAlgebra.swapColumnsSelfInverse

/- The negate-column involutivity. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.negateColumnInvolutive

/- The transvection cancels (row and column). -/
#assert_no_axioms FX1Poly.ComputerAlgebra.intTransvectionCancel
#assert_no_axioms FX1Poly.ComputerAlgebra.addRowMultipleExpand
#assert_no_axioms FX1Poly.ComputerAlgebra.addRowMultipleRoundTrip
#assert_no_axioms FX1Poly.ComputerAlgebra.addScaledEntryWithinRowCancel
#assert_no_axioms FX1Poly.ComputerAlgebra.addColumnMultipleRoundTrip

/- The single-operation dispatch and THE FOLD ROUND-TRIP (the ℤ-equivalence witness). -/
#assert_no_axioms FX1Poly.ComputerAlgebra.applyOperationInverseRoundTrip
#assert_no_axioms FX1Poly.ComputerAlgebra.applyOperationsReverseRoundTrip

/- The B2 transport-fit — the reverse word is confined exactly where the forward word is. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.inverseOperationBoundedBelow
#assert_no_axioms FX1Poly.ComputerAlgebra.allOpsBoundedBelowAppendEq
#assert_no_axioms FX1Poly.ComputerAlgebra.reverseOperationWordBoundedBelow

end FX1PolyAudit
