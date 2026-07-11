import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.BlockDiagonalCertificateLifting

/-! # FX1PolyAudit/Polygraph/Homology/BlockDiagonalCertificateLifting — zero-axiom gate (the fully
    cert-free block-lifting: the block constructor, the six single-op block-inertness lemmas, the
    boundedness predicate, and `liftedBaseCertAgreesOnBlock`)

Per-declaration zero-axiom gate for H2-SQUIER-NOGO r5 brick B1 (#2139).  Every declaration must be free of
`propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Homology.mapAllRowsLength
#assert_no_axioms FX1Poly.Polygraph.Homology.mapAllRowsAppend
#assert_no_axioms FX1Poly.Polygraph.Homology.listReplaceAtLength
#assert_no_axioms FX1Poly.Polygraph.Homology.listReplaceAtAppendLeft
#assert_no_axioms FX1Poly.Polygraph.Homology.listModifyAtAppendLeft
#assert_no_axioms FX1Poly.Polygraph.Homology.listReplaceAtMapAllRows
#assert_no_axioms FX1Poly.Polygraph.Homology.listGetWithDefaultAppendLeft'
#assert_no_axioms FX1Poly.Polygraph.Homology.getMapAllRowsInRange
#assert_no_axioms FX1Poly.Polygraph.Homology.extendRow
#assert_no_axioms FX1Poly.Polygraph.Homology.freshUnitRow
#assert_no_axioms FX1Poly.Polygraph.Homology.blockDiagWithFreshUnit
#assert_no_axioms FX1Poly.Polygraph.Homology.rowsAllHaveWidthGet
#assert_no_axioms FX1Poly.Polygraph.Homology.addScaledEntriesAppend
#assert_no_axioms FX1Poly.Polygraph.Homology.mapNegExtendRow
#assert_no_axioms FX1Poly.Polygraph.Homology.addScaledEntriesExtendRow
#assert_no_axioms FX1Poly.Polygraph.Homology.listModifyAtMapAllRowsUnderWidth
#assert_no_axioms FX1Poly.Polygraph.Homology.blockDiagNegateRowInert
#assert_no_axioms FX1Poly.Polygraph.Homology.appendSingletonLength
#assert_no_axioms FX1Poly.Polygraph.Homology.blockDiagRowsLength
#assert_no_axioms FX1Poly.Polygraph.Homology.swapRowsOfBounded
#assert_no_axioms FX1Poly.Polygraph.Homology.addRowMultipleSelfIdent
#assert_no_axioms FX1Poly.Polygraph.Homology.addRowMultipleOfBounded
#assert_no_axioms FX1Poly.Polygraph.Homology.blockDiagSwapRowsInert
#assert_no_axioms FX1Poly.Polygraph.Homology.blockDiagAddRowMultipleInert
#assert_no_axioms FX1Poly.Polygraph.Homology.listReplaceAtGetSelf
#assert_no_axioms FX1Poly.Polygraph.Homology.listModifyAtFixed
#assert_no_axioms FX1Poly.Polygraph.Homology.freshUnitRowLength
#assert_no_axioms FX1Poly.Polygraph.Homology.freshRowLowEntryZero
#assert_no_axioms FX1Poly.Polygraph.Homology.freshReplaceZeroInert
#assert_no_axioms FX1Poly.Polygraph.Homology.swapEntriesWithinRowOfBounded
#assert_no_axioms FX1Poly.Polygraph.Homology.addScaledEntryWithinRowOfBounded
#assert_no_axioms FX1Poly.Polygraph.Homology.addColumnMultipleSelfIdent
#assert_no_axioms FX1Poly.Polygraph.Homology.addColumnMultipleOfBounded
#assert_no_axioms FX1Poly.Polygraph.Homology.swapEntriesWithinRowFreshInert
#assert_no_axioms FX1Poly.Polygraph.Homology.negateColumnFreshInert
#assert_no_axioms FX1Poly.Polygraph.Homology.addScaledEntryWithinRowFreshInert
#assert_no_axioms FX1Poly.Polygraph.Homology.swapEntriesWithinRowExtendRow
#assert_no_axioms FX1Poly.Polygraph.Homology.negateColumnExtendRow
#assert_no_axioms FX1Poly.Polygraph.Homology.addScaledEntryWithinRowExtendRow
#assert_no_axioms FX1Poly.Polygraph.Homology.mapAllRowsColumnFuse
#assert_no_axioms FX1Poly.Polygraph.Homology.columnOpBlockInert
#assert_no_axioms FX1Poly.Polygraph.Homology.blockDiagSwapColumnsInert
#assert_no_axioms FX1Poly.Polygraph.Homology.blockDiagNegateColumnInert
#assert_no_axioms FX1Poly.Polygraph.Homology.blockDiagAddColumnMultipleInert
#assert_no_axioms FX1Poly.Polygraph.Homology.listModifyAtLength
#assert_no_axioms FX1Poly.Polygraph.Homology.listMapNegLength
#assert_no_axioms FX1Poly.Polygraph.Homology.addScaledEntriesLength
#assert_no_axioms FX1Poly.Polygraph.Homology.swapEntriesWithinRowLengthUnderWidth
#assert_no_axioms FX1Poly.Polygraph.Homology.addScaledEntryWithinRowLengthUnderWidth
#assert_no_axioms FX1Poly.Polygraph.Homology.rowsAllHaveWidthListReplaceAt
#assert_no_axioms FX1Poly.Polygraph.Homology.rowsAllHaveWidthListModifyAt
#assert_no_axioms FX1Poly.Polygraph.Homology.rowsAllHaveWidthMapAllRows
#assert_no_axioms FX1Poly.Polygraph.Homology.opIsBounded
#assert_no_axioms FX1Poly.Polygraph.Homology.allOpsBounded
#assert_no_axioms FX1Poly.Polygraph.Homology.boolAndTrueLeft
#assert_no_axioms FX1Poly.Polygraph.Homology.boolAndTrueRight
#assert_no_axioms FX1Poly.Polygraph.Homology.applyOperationBlockInert
#assert_no_axioms FX1Poly.Polygraph.Homology.applyOperationPreservesRect
#assert_no_axioms FX1Poly.Polygraph.Homology.liftedBaseCertAgreesOnBlock
#assert_no_axioms FX1Poly.Polygraph.Homology.applyOperationsAppend
#assert_no_axioms FX1Poly.Polygraph.Homology.blockRecipeReducesToBlockDiag
#assert_no_axioms FX1Poly.Polygraph.Homology.blockDiagDiagonalBelow
#assert_no_axioms FX1Poly.Polygraph.Homology.listGetAtLeftLengthReadsRightHead
#assert_no_axioms FX1Poly.Polygraph.Homology.freshRowPivotEntry
#assert_no_axioms FX1Poly.Polygraph.Homology.blockDiagDiagonalAtFreshSquare

end FX1PolyAudit
