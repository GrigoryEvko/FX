import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.IntMatrix

/-! # FX1PolyAudit/ComputerAlgebra/IntMatrix — zero-axiom gate (the ComputerAlgebra/ substrate, brick 1)

Per-declaration zero-axiom gate for the exact-integer-matrix carrier, the list substrate, the
unimodular row/column operation alphabet, the certificate applier, and the Smith-normal-form
predicates.  First gate of the `ComputerAlgebra/` layer (Init-only by the dependency-spine rule).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.listGetWithDefault
#assert_no_axioms FX1Poly.ComputerAlgebra.listReplaceAt
#assert_no_axioms FX1Poly.ComputerAlgebra.listModifyAt
#assert_no_axioms FX1Poly.ComputerAlgebra.mapAllRows
#assert_no_axioms FX1Poly.ComputerAlgebra.dividesExactly
#assert_no_axioms FX1Poly.ComputerAlgebra.IntMatrix
#assert_no_axioms FX1Poly.ComputerAlgebra.IntMatrix.rowsAllHaveWidth
#assert_no_axioms FX1Poly.ComputerAlgebra.IntMatrix.IsRectangular
#assert_no_axioms FX1Poly.ComputerAlgebra.IntMatrix.entryAt
#assert_no_axioms FX1Poly.ComputerAlgebra.IntMatrix.diagonalEntryAt
#assert_no_axioms FX1Poly.ComputerAlgebra.IntMatrix.swapRows
#assert_no_axioms FX1Poly.ComputerAlgebra.IntMatrix.negateRow
#assert_no_axioms FX1Poly.ComputerAlgebra.IntMatrix.addScaledEntries
#assert_no_axioms FX1Poly.ComputerAlgebra.IntMatrix.addRowMultiple
#assert_no_axioms FX1Poly.ComputerAlgebra.IntMatrix.swapEntriesWithinRow
#assert_no_axioms FX1Poly.ComputerAlgebra.IntMatrix.swapColumns
#assert_no_axioms FX1Poly.ComputerAlgebra.IntMatrix.negateColumn
#assert_no_axioms FX1Poly.ComputerAlgebra.IntMatrix.addScaledEntryWithinRow
#assert_no_axioms FX1Poly.ComputerAlgebra.IntMatrix.addColumnMultiple
#assert_no_axioms FX1Poly.ComputerAlgebra.ElementaryRowOperation
#assert_no_axioms FX1Poly.ComputerAlgebra.ElementaryColumnOperation
#assert_no_axioms FX1Poly.ComputerAlgebra.ElementaryOperation
#assert_no_axioms FX1Poly.ComputerAlgebra.IntMatrix.applyRowOperation
#assert_no_axioms FX1Poly.ComputerAlgebra.IntMatrix.applyColumnOperation
#assert_no_axioms FX1Poly.ComputerAlgebra.IntMatrix.applyOperation
#assert_no_axioms FX1Poly.ComputerAlgebra.IntMatrix.applyOperations
#assert_no_axioms FX1Poly.ComputerAlgebra.IntMatrix.IsSmithNormalFormWithin
#assert_no_axioms FX1Poly.ComputerAlgebra.IntMatrix.SmithReductionCertificate
#assert_no_axioms FX1Poly.ComputerAlgebra.IntMatrix.SmithReductionCertificate.reducesToSmithForm

end FX1PolyAudit
