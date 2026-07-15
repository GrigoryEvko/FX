import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.LafontProp.MatrixNormalForm

/-! # FX1PolyAudit.Polygraph.Omega.LafontProp.MatrixNormalForm — zero-axiom gate
(LAFONT-PROP r2, brick A: THE NORMAL FORM + ITS SOUNDNESS)

Per-declaration zero-axiom gate for the canonical-form machine: the greenfield Nat
comparison/subtraction/multiplication kit, the structural-sum support lemmas, the direct-sum
block lemmas, the pointwise/Bool rectangle-agreement bridge, the canonical-diagram construction
(`scaleWire` / `scaleThenSwapGadget` / `mergeColumnFan` / `zeroVectorDiagram` /
`canonicalDiagramOfEntries` / `normalFormOfDiagram`), THE SOUNDNESS OF THE NORMAL FORM
(pointwise and Bool forms), rectangle extensionality (`equalMatricesGiveEqualNormalForms`),
the named residual `canonicalReductionStatement`, THE REDUCTION THEOREM
(`completenessReducesToCanonicalReduction`), and the closed-instance fires.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`,
`WellFounded.fix`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.beqSelfIsTrue
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.eqOfBeqIsTrue
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.beqIsFalseOfNe
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.bleIsTrueOfLe
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.leOfBleIsTrue
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.bltIsTrueOfLt
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.ltOfBltIsTrue
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.bltIsFalseOfGe
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.noLtOfEq
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.ltOrEqOfLtSucc
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.succSubSucc
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.addSubCancelLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.mulOneIsSelf
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.oneMulIsSelf
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.zeroMulIsZero
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sumBelowOfAllZeroIsZero
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sumBelowOfSingleSupport
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.identityEntryOnDiagonal
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.identityEntryOffDiagonal
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.directSumEntryInTopBlock
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.directSumEntryInBottomBlock
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.directSumEntryInTopRightBlock
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.directSumEntryInBottomLeftBlock
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.leftIsTrueOfAndTrue
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.rightIsTrueOfAndTrue
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.agreeOnRowOfPointwise
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.pointwiseOfAgreeOnRow
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.agreeOnRowsOfPointwise
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.pointwiseOfAgreeOnRows
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.agreeUpToOfPointwise
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.pointwiseOfAgreeUpTo
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.scaleWire
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.scaleThenSwapGadget
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.mergeColumnFan
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.zeroVectorDiagram
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.canonicalDiagramOfEntries
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.normalFormOfDiagram
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.scaleWireDenotesScalar
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.gadgetEntryZeroZero
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.gadgetEntryZeroOne
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.gadgetEntryOneZero
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.gadgetEntryOneOne
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.mergeColumnFanEntries
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.mergeRecursionStageEntries
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.mergeGadgetStageEntries
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.mergeColumnFanDenotesWithin
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.canonicalRecursionStageEntries
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.canonicalDiagramDenotesEntriesWithin
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.canonicalFormIsSoundOverMatrices
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.normalFormPreservesDenotation
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.mergeColumnFanRespectsColumnAgreement
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.canonicalDiagramRespectsRectangleAgreement
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.equalMatricesGiveEqualNormalForms
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.canonicalReductionStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.completenessReducesToCanonicalReduction
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.canonicalFormOfSwapMatrixIsSound
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.canonicalFormOfDoublingMatrixIsSound
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.normalFormOfBimonoidSquareLeftSideIsSound

end FX1PolyAudit
