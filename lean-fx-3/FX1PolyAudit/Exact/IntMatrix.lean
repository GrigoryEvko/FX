import FX1PolyAudit.DependencyAudit
import FX1Poly.Exact.IntMatrix

/-! # FX1PolyAudit/Exact/IntMatrix — zero-axiom gate (the Exact/ substrate, brick 1)

Per-declaration zero-axiom gate for the exact-integer-matrix carrier, the list substrate, the
unimodular row/column operation alphabet, the certificate applier, and the Smith-normal-form
predicates.  First gate of the `Exact/` layer (Init-only by the dependency-spine rule).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Exact.listGetWithDefault
#assert_no_axioms FX1Poly.Exact.listReplaceAt
#assert_no_axioms FX1Poly.Exact.listModifyAt
#assert_no_axioms FX1Poly.Exact.mapAllRows
#assert_no_axioms FX1Poly.Exact.dividesExactly
#assert_no_axioms FX1Poly.Exact.IntMatrix
#assert_no_axioms FX1Poly.Exact.IntMatrix.rowsAllHaveWidth
#assert_no_axioms FX1Poly.Exact.IntMatrix.IsRectangular
#assert_no_axioms FX1Poly.Exact.IntMatrix.entryAt
#assert_no_axioms FX1Poly.Exact.IntMatrix.diagonalEntryAt
#assert_no_axioms FX1Poly.Exact.IntMatrix.swapRows
#assert_no_axioms FX1Poly.Exact.IntMatrix.negateRow
#assert_no_axioms FX1Poly.Exact.IntMatrix.addScaledEntries
#assert_no_axioms FX1Poly.Exact.IntMatrix.addRowMultiple
#assert_no_axioms FX1Poly.Exact.IntMatrix.swapEntriesWithinRow
#assert_no_axioms FX1Poly.Exact.IntMatrix.swapColumns
#assert_no_axioms FX1Poly.Exact.IntMatrix.negateColumn
#assert_no_axioms FX1Poly.Exact.IntMatrix.addScaledEntryWithinRow
#assert_no_axioms FX1Poly.Exact.IntMatrix.addColumnMultiple
#assert_no_axioms FX1Poly.Exact.ElementaryRowOperation
#assert_no_axioms FX1Poly.Exact.ElementaryColumnOperation
#assert_no_axioms FX1Poly.Exact.ElementaryOperation
#assert_no_axioms FX1Poly.Exact.IntMatrix.applyRowOperation
#assert_no_axioms FX1Poly.Exact.IntMatrix.applyColumnOperation
#assert_no_axioms FX1Poly.Exact.IntMatrix.applyOperation
#assert_no_axioms FX1Poly.Exact.IntMatrix.applyOperations
#assert_no_axioms FX1Poly.Exact.IntMatrix.IsSmithNormalFormWithin
#assert_no_axioms FX1Poly.Exact.IntMatrix.SmithReductionCertificate
#assert_no_axioms FX1Poly.Exact.IntMatrix.SmithReductionCertificate.reducesToSmithForm

end FX1PolyAudit
