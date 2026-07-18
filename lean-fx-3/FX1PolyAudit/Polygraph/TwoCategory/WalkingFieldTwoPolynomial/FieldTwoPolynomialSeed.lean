import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingFieldTwoPolynomial.FieldTwoPolynomialSeed

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingFieldTwoPolynomial.FieldTwoPolynomialSeed — zero-axiom gate (the FULLY DECIDED walking free commutative F2-algebra F2[X])

Per-declaration zero-axiom gate for the walking free commutative F2-algebra on `ℕ` — the polynomial ring
`F2[X]`, decided by canonical normal form.  The NON-idempotent cousin of the Boolean-ring rung: monomials are
variable MULTISETS built with the imported non-dedup `insertMany` (so `x·x = x²` is a genuine degree-two
monomial with `x² ≠ x` — the whole difference from the Boolean ring, which imposes `x·x = x`).  F2 coefficients
are carried as `Bool` in the NO-DROP discipline; since F2 addition is its own inverse (`x + x = 0`) NEGATION IS
THE IDENTITY and the difference `A − B` is simply `A + B`.  Covers the F2 `Bool` coefficient algebra
(`ftpCoeffXor` / `ftpCoeffAnd` / `ftpCoeffIsZero`), the multiset monomial layer (`ftpMonoMul` multiset-union,
`ftpMonoFixpoint`, `ftpMonoMulComm` / `ftpMonoMulAssoc`), the normal-form machinery (`ftpInsertTerm` with the
crux commutation `ftpInsertTermComm`, `ftpMergeXor`, the convolution `ftpMulConvolve` with annihilation /
distributivity / associativity / commutativity / unit), the `ftpEvalCross` semantic model with the all-absent
cancellation `ftpMergeXorAllZeroCancel` and the F2 self-inverse `ftpMergeXorSelfAllZero`, the decision
equivalence `ftpNFEq`, the `FtpTree` carrier, `ftpNormalize`, the `FieldTwoPolyTreeConv` convertibility (the F2
self-inverse `xorSelf`, and NO `andIdem`), soundness (`ftpNormalize_respects`), the rebuild `ftpCombOfNF` with
the repeat-preserving reification (`ftpMonoToTreeInsertSorted`), completeness (`ftpConv_of_normalizeEq`), and
THE DECISION (`ftpDecideConv` / `fieldTwoPolyTreeConv_iff_normalForm` / the `Decidable` instance
`instDecidableFieldTwoPolyTreeConv`) plus its marker.  Every landed declaration must be free of `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, and all other non-Init axioms — verified below by an
independent per-declaration `#assert_no_axioms`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.ftpCoeffXor
#assert_no_axioms FX1Poly.Polygraph.ftpCoeffAnd
#assert_no_axioms FX1Poly.Polygraph.ftpCoeffIsZero
#assert_no_axioms FX1Poly.Polygraph.ftpCoeffXorComm
#assert_no_axioms FX1Poly.Polygraph.ftpCoeffXorAssoc
#assert_no_axioms FX1Poly.Polygraph.ftpCoeffXorFalseRight
#assert_no_axioms FX1Poly.Polygraph.ftpCoeffXorFalseLeft
#assert_no_axioms FX1Poly.Polygraph.ftpCoeffXorRightComm
#assert_no_axioms FX1Poly.Polygraph.ftpCoeffXorSwap13
#assert_no_axioms FX1Poly.Polygraph.ftpCoeffAndComm
#assert_no_axioms FX1Poly.Polygraph.ftpCoeffAndTrueRight
#assert_no_axioms FX1Poly.Polygraph.ftpCoeffAndAssoc
#assert_no_axioms FX1Poly.Polygraph.ftpCoeffAndXorRight
#assert_no_axioms FX1Poly.Polygraph.ftpCoeffXorAndRight
#assert_no_axioms FX1Poly.Polygraph.ftpCoeffXorSelfZero
#assert_no_axioms FX1Poly.Polygraph.ftpCoeffXorZeroValued
#assert_no_axioms FX1Poly.Polygraph.ftpCoeffAndZeroValuedLeft
#assert_no_axioms FX1Poly.Polygraph.ftpCoeffAndZeroValuedRight
#assert_no_axioms FX1Poly.Polygraph.ftpCoeffXorCancelZero
#assert_no_axioms FX1Poly.Polygraph.ftpMonoMul
#assert_no_axioms FX1Poly.Polygraph.ftpMonoMulNilRight
#assert_no_axioms FX1Poly.Polygraph.ftpMonoMulAssoc
#assert_no_axioms FX1Poly.Polygraph.ftpMonoBelow
#assert_no_axioms FX1Poly.Polygraph.ftpMonoSorted
#assert_no_axioms FX1Poly.Polygraph.ftpMonoBelowNil
#assert_no_axioms FX1Poly.Polygraph.ftpMonoBelowCons
#assert_no_axioms FX1Poly.Polygraph.ftpMonoSortedCons
#assert_no_axioms FX1Poly.Polygraph.ftpMonoBelowInsert
#assert_no_axioms FX1Poly.Polygraph.ftpInsertSortedPreservesMonoSorted
#assert_no_axioms FX1Poly.Polygraph.ftpInsertManyPreservesMonoSorted
#assert_no_axioms FX1Poly.Polygraph.ftpMonoMulSorted
#assert_no_axioms FX1Poly.Polygraph.ftpMonoInsertFront
#assert_no_axioms FX1Poly.Polygraph.ftpMonoFixpoint
#assert_no_axioms FX1Poly.Polygraph.ftpMonoMulComm
#assert_no_axioms FX1Poly.Polygraph.FtpNF
#assert_no_axioms FX1Poly.Polygraph.ftpInsertTerm
#assert_no_axioms FX1Poly.Polygraph.ftpInsertTermNil
#assert_no_axioms FX1Poly.Polygraph.ftpInsertTermEqE
#assert_no_axioms FX1Poly.Polygraph.ftpInsertTermLtE
#assert_no_axioms FX1Poly.Polygraph.ftpInsertTermGtE
#assert_no_axioms FX1Poly.Polygraph.ftpInsertTermComm
#assert_no_axioms FX1Poly.Polygraph.ftpMergeXor
#assert_no_axioms FX1Poly.Polygraph.ftpMergeXorNilLeft
#assert_no_axioms FX1Poly.Polygraph.ftpMergeXorCons
#assert_no_axioms FX1Poly.Polygraph.ftpInsertTerm_mergeXor
#assert_no_axioms FX1Poly.Polygraph.ftpInsertTermMergeSame
#assert_no_axioms FX1Poly.Polygraph.ftpMergeXorInsertTermLeft
#assert_no_axioms FX1Poly.Polygraph.ftpMergeXorAssoc
#assert_no_axioms FX1Poly.Polygraph.ftpMergeXorSwap
#assert_no_axioms FX1Poly.Polygraph.ftpBelowHead
#assert_no_axioms FX1Poly.Polygraph.ftpNFSorted
#assert_no_axioms FX1Poly.Polygraph.ftpBelowHeadNil
#assert_no_axioms FX1Poly.Polygraph.ftpBelowHeadConsTrue
#assert_no_axioms FX1Poly.Polygraph.ftpBelowHeadConsLt
#assert_no_axioms FX1Poly.Polygraph.ftpNFSortedCons
#assert_no_axioms FX1Poly.Polygraph.ftpBelowHeadInsert
#assert_no_axioms FX1Poly.Polygraph.ftpInsertPreservesSorted
#assert_no_axioms FX1Poly.Polygraph.ftpInsertFront
#assert_no_axioms FX1Poly.Polygraph.ftpMergeXorNilRight
#assert_no_axioms FX1Poly.Polygraph.ftpMergeXorComm
#assert_no_axioms FX1Poly.Polygraph.ftpMergeXorPreservesSorted
#assert_no_axioms FX1Poly.Polygraph.ftpTermMul
#assert_no_axioms FX1Poly.Polygraph.ftpMulConvolve
#assert_no_axioms FX1Poly.Polygraph.ftpTermMulNil
#assert_no_axioms FX1Poly.Polygraph.ftpTermMulCons
#assert_no_axioms FX1Poly.Polygraph.ftpMulConvolveNil
#assert_no_axioms FX1Poly.Polygraph.ftpMulConvolveCons
#assert_no_axioms FX1Poly.Polygraph.ftpTermMulSorted
#assert_no_axioms FX1Poly.Polygraph.ftpMulConvolveSorted
#assert_no_axioms FX1Poly.Polygraph.ftpTermMul_insertTerm
#assert_no_axioms FX1Poly.Polygraph.ftpTermMul_merge
#assert_no_axioms FX1Poly.Polygraph.ftpMulConvolveAnnihil
#assert_no_axioms FX1Poly.Polygraph.ftpMergeXor4Swap
#assert_no_axioms FX1Poly.Polygraph.ftpMulConvolve_leftDistrib
#assert_no_axioms FX1Poly.Polygraph.ftpTermMul_coeffXor
#assert_no_axioms FX1Poly.Polygraph.ftpConvolve_insertTermLeft
#assert_no_axioms FX1Poly.Polygraph.ftpMulConvolve_rightDistrib
#assert_no_axioms FX1Poly.Polygraph.ftpTermMul_compose
#assert_no_axioms FX1Poly.Polygraph.ftpTermMul_convolve
#assert_no_axioms FX1Poly.Polygraph.ftpMulConvolveAssoc
#assert_no_axioms FX1Poly.Polygraph.ftpNFMonoSorted
#assert_no_axioms FX1Poly.Polygraph.ftpNFMonoSortedCons
#assert_no_axioms FX1Poly.Polygraph.ftpInsertTermMonoSorted
#assert_no_axioms FX1Poly.Polygraph.ftpMergeXorMonoSorted
#assert_no_axioms FX1Poly.Polygraph.ftpTermMulMonoSorted
#assert_no_axioms FX1Poly.Polygraph.ftpMulConvolveMonoSorted
#assert_no_axioms FX1Poly.Polygraph.ftpTermMulEqConvolveSingle
#assert_no_axioms FX1Poly.Polygraph.ftpMulConvolveComm
#assert_no_axioms FX1Poly.Polygraph.ftpMulConvolveUnit
#assert_no_axioms FX1Poly.Polygraph.ftpNFAllZero
#assert_no_axioms FX1Poly.Polygraph.ftpNFAllZeroCons
#assert_no_axioms FX1Poly.Polygraph.ftpInsertTermAllZero
#assert_no_axioms FX1Poly.Polygraph.ftpMergeXorAllZero
#assert_no_axioms FX1Poly.Polygraph.ftpCondCoeff
#assert_no_axioms FX1Poly.Polygraph.ftpCondCoeffTrue
#assert_no_axioms FX1Poly.Polygraph.ftpCondCoeffFalse
#assert_no_axioms FX1Poly.Polygraph.ftpCondCoeffZero
#assert_no_axioms FX1Poly.Polygraph.ftpMonoEqFalseOfLt
#assert_no_axioms FX1Poly.Polygraph.ftpEvalCross
#assert_no_axioms FX1Poly.Polygraph.ftpEvalCrossNil
#assert_no_axioms FX1Poly.Polygraph.ftpEvalCrossCons
#assert_no_axioms FX1Poly.Polygraph.ftpEvalCross_insertTerm
#assert_no_axioms FX1Poly.Polygraph.ftpEvalCross_mergeXor
#assert_no_axioms FX1Poly.Polygraph.ftpAllZero_evalZero
#assert_no_axioms FX1Poly.Polygraph.ftpEvalBelowZero
#assert_no_axioms FX1Poly.Polygraph.ftpSortedEvalZero_allZero
#assert_no_axioms FX1Poly.Polygraph.ftpMergeXorAllZeroCancel
#assert_no_axioms FX1Poly.Polygraph.ftpMergeXorSelfAllZero
#assert_no_axioms FX1Poly.Polygraph.ftpTermMulCoeffZeroAllZero
#assert_no_axioms FX1Poly.Polygraph.ftpTermMulRightAllZero
#assert_no_axioms FX1Poly.Polygraph.ftpMulConvolveLeftAllZero
#assert_no_axioms FX1Poly.Polygraph.ftpMulConvolveRightAllZero
#assert_no_axioms FX1Poly.Polygraph.ftpNFEq
#assert_no_axioms FX1Poly.Polygraph.ftpNFEqRefl
#assert_no_axioms FX1Poly.Polygraph.ftpNFEqOfEq
#assert_no_axioms FX1Poly.Polygraph.ftpNFEqSymm
#assert_no_axioms FX1Poly.Polygraph.ftpNFEqTrans
#assert_no_axioms FX1Poly.Polygraph.ftpNFEqMergeCongr
#assert_no_axioms FX1Poly.Polygraph.ftpNFEqMulCongr
#assert_no_axioms FX1Poly.Polygraph.ftpNFEqNil
#assert_no_axioms FX1Poly.Polygraph.FtpTree
#assert_no_axioms FX1Poly.Polygraph.ftpNormalize
#assert_no_axioms FX1Poly.Polygraph.ftpNormalize_zero_smoke
#assert_no_axioms FX1Poly.Polygraph.ftpNormalize_one_smoke
#assert_no_axioms FX1Poly.Polygraph.ftpNormalize_gen_smoke
#assert_no_axioms FX1Poly.Polygraph.ftpNormalizeSorted
#assert_no_axioms FX1Poly.Polygraph.ftpNormalizeMonoSorted
#assert_no_axioms FX1Poly.Polygraph.FieldTwoPolyTreeConv
#assert_no_axioms FX1Poly.Polygraph.ftpNormalize_respects
#assert_no_axioms FX1Poly.Polygraph.ftpConvXorZeroLeft
#assert_no_axioms FX1Poly.Polygraph.ftpConvAndOneLeft
#assert_no_axioms FX1Poly.Polygraph.ftpConvAnnihilLeft
#assert_no_axioms FX1Poly.Polygraph.ftpConvDistribRight
#assert_no_axioms FX1Poly.Polygraph.ftpConvXorSwap13
#assert_no_axioms FX1Poly.Polygraph.ftpConvAndSwap13
#assert_no_axioms FX1Poly.Polygraph.ftpMonoToTree
#assert_no_axioms FX1Poly.Polygraph.ftpMonoToTreeInsertSorted
#assert_no_axioms FX1Poly.Polygraph.ftpMonoToTreeInsertMany
#assert_no_axioms FX1Poly.Polygraph.ftpMonoToTreeMonoMul
#assert_no_axioms FX1Poly.Polygraph.ftpTermToTree
#assert_no_axioms FX1Poly.Polygraph.ftpTermToTreeXor
#assert_no_axioms FX1Poly.Polygraph.ftpTermToTreeMul
#assert_no_axioms FX1Poly.Polygraph.ftpTermToTreeZero
#assert_no_axioms FX1Poly.Polygraph.ftpCombOfNF
#assert_no_axioms FX1Poly.Polygraph.ftpCombOfNFCons
#assert_no_axioms FX1Poly.Polygraph.ftpCombInsertTerm
#assert_no_axioms FX1Poly.Polygraph.ftpCombMergeXor
#assert_no_axioms FX1Poly.Polygraph.ftpCombTermMul
#assert_no_axioms FX1Poly.Polygraph.ftpCombMulConvolve
#assert_no_axioms FX1Poly.Polygraph.ftpCombAllZero
#assert_no_axioms FX1Poly.Polygraph.ftpTreeReifies
#assert_no_axioms FX1Poly.Polygraph.ftpConvOfXorZero
#assert_no_axioms FX1Poly.Polygraph.ftpCombOfNFEqConv
#assert_no_axioms FX1Poly.Polygraph.ftpConv_of_normalizeEq
#assert_no_axioms FX1Poly.Polygraph.ftpDecideConv
#assert_no_axioms FX1Poly.Polygraph.fieldTwoPolyTreeConv_iff_normalForm
#assert_no_axioms FX1Poly.Polygraph.instDecidableFieldTwoPolyTreeConv
#assert_no_axioms FX1Poly.Polygraph.fxWalkingFieldTwoPolynomial_hasNormalFormDecision

end FX1PolyAudit
