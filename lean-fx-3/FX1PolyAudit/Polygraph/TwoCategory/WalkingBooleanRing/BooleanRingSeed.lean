import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingBooleanRing.BooleanRingSeed

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingBooleanRing.BooleanRingSeed — zero-axiom gate (the FULLY DECIDED walking free Boolean ring on ℕ)

Per-declaration zero-axiom gate for the walking free Boolean ring on `ℕ` — the Zhegalkin decision for
`F2[X]/(x²=x)`.  Monomials are idempotent variable SETS reusing the imported finite-set kit `insertManySet`
(so `x·x = x`); F2 coefficients are carried as `Bool` in the NO-DROP discipline of the `ℤ[X]` ring, and since
F2 addition is its own inverse (`x + x = 0`) NEGATION IS THE IDENTITY (the whole negate layer is gone), so the
difference `A − B` is simply `A + B`.  Covers the F2 `Bool` coefficient algebra (`brCoeffXor` / `brCoeffAnd` /
`brCoeffIsZero` with all laws by finite case analysis), the idempotent monomial layer (`brMonoMul` set-union
with strict-sorted preservation, `brMonoFixpoint`, `brMonoMulComm` / `brMonoMulAssoc` / the singleton
idempotence `brMonoMulSelfSingleton`), the Zhegalkin normal-form machinery (`brInsertTerm` with the crux
commutation `brInsertTermComm`, `brMergeXor`, the convolution `brMulConvolve` with annihilation / distributivity
/ associativity / commutativity / unit), the `brEvalCross` semantic model with the all-absent cancellation
`brMergeXorAllZeroCancel` and the F2 self-inverse `brMergeXorSelfAllZero`, the decision equivalence `brNFEq`
with its full equivalence + congruence structure, the `BrTree` carrier, `brNormalize`, the
`BooleanRingTreeConv` convertibility (generator idempotence `andIdemGen`, the F2 self-inverse `xorSelf`),
soundness (`brNormalize_respects`), the rebuild `brCombOfNF` with the dedup-consumes-idempotence reification
(`brMonoToTreeInsertSortedSet`), completeness (`brConv_of_normalizeEq`), and THE DECISION (`brDecideConv` /
`booleanRingTreeConv_iff_normalForm` / the `Decidable` instance `instDecidableBooleanRingTreeConv`) plus its
marker.  Every landed declaration must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, and all other non-Init axioms — verified below by an independent per-declaration
`#assert_no_axioms`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.brCoeffXor
#assert_no_axioms FX1Poly.Polygraph.brCoeffAnd
#assert_no_axioms FX1Poly.Polygraph.brCoeffIsZero
#assert_no_axioms FX1Poly.Polygraph.brCoeffXorComm
#assert_no_axioms FX1Poly.Polygraph.brCoeffXorAssoc
#assert_no_axioms FX1Poly.Polygraph.brCoeffXorFalseRight
#assert_no_axioms FX1Poly.Polygraph.brCoeffXorFalseLeft
#assert_no_axioms FX1Poly.Polygraph.brCoeffXorRightComm
#assert_no_axioms FX1Poly.Polygraph.brCoeffXorSwap13
#assert_no_axioms FX1Poly.Polygraph.brCoeffAndComm
#assert_no_axioms FX1Poly.Polygraph.brCoeffAndTrueRight
#assert_no_axioms FX1Poly.Polygraph.brCoeffAndAssoc
#assert_no_axioms FX1Poly.Polygraph.brCoeffAndXorRight
#assert_no_axioms FX1Poly.Polygraph.brCoeffXorAndRight
#assert_no_axioms FX1Poly.Polygraph.brCoeffXorSelfZero
#assert_no_axioms FX1Poly.Polygraph.brCoeffXorZeroValued
#assert_no_axioms FX1Poly.Polygraph.brCoeffAndZeroValuedLeft
#assert_no_axioms FX1Poly.Polygraph.brCoeffAndZeroValuedRight
#assert_no_axioms FX1Poly.Polygraph.brCoeffXorCancelZero
#assert_no_axioms FX1Poly.Polygraph.brMonoBelow
#assert_no_axioms FX1Poly.Polygraph.brMonoSorted
#assert_no_axioms FX1Poly.Polygraph.brMonoBelowNil
#assert_no_axioms FX1Poly.Polygraph.brMonoSortedCons
#assert_no_axioms FX1Poly.Polygraph.brMonoBelowConsTrue
#assert_no_axioms FX1Poly.Polygraph.brMonoBelowConsLt
#assert_no_axioms FX1Poly.Polygraph.brMonoInsertFront
#assert_no_axioms FX1Poly.Polygraph.brMonoBelowInsertSortedSet
#assert_no_axioms FX1Poly.Polygraph.brInsertSortedSetPreservesMonoSorted
#assert_no_axioms FX1Poly.Polygraph.brInsertManySetPreservesMonoSorted
#assert_no_axioms FX1Poly.Polygraph.brMonoFixpoint
#assert_no_axioms FX1Poly.Polygraph.brMonoMul
#assert_no_axioms FX1Poly.Polygraph.brMonoMulNilRight
#assert_no_axioms FX1Poly.Polygraph.brMonoMulAssoc
#assert_no_axioms FX1Poly.Polygraph.brMonoMulComm
#assert_no_axioms FX1Poly.Polygraph.brMonoMulSorted
#assert_no_axioms FX1Poly.Polygraph.brMonoMulSelfSingleton
#assert_no_axioms FX1Poly.Polygraph.BrNF
#assert_no_axioms FX1Poly.Polygraph.brInsertTerm
#assert_no_axioms FX1Poly.Polygraph.brInsertTermNil
#assert_no_axioms FX1Poly.Polygraph.brInsertTermEqE
#assert_no_axioms FX1Poly.Polygraph.brInsertTermLtE
#assert_no_axioms FX1Poly.Polygraph.brInsertTermGtE
#assert_no_axioms FX1Poly.Polygraph.brInsertTermComm
#assert_no_axioms FX1Poly.Polygraph.brMergeXor
#assert_no_axioms FX1Poly.Polygraph.brMergeXorNilLeft
#assert_no_axioms FX1Poly.Polygraph.brMergeXorCons
#assert_no_axioms FX1Poly.Polygraph.brInsertTerm_mergeXor
#assert_no_axioms FX1Poly.Polygraph.brInsertTermMergeSame
#assert_no_axioms FX1Poly.Polygraph.brMergeXorInsertTermLeft
#assert_no_axioms FX1Poly.Polygraph.brMergeXorAssoc
#assert_no_axioms FX1Poly.Polygraph.brMergeXorSwap
#assert_no_axioms FX1Poly.Polygraph.brBelowHead
#assert_no_axioms FX1Poly.Polygraph.brNFSorted
#assert_no_axioms FX1Poly.Polygraph.brBelowHeadNil
#assert_no_axioms FX1Poly.Polygraph.brBelowHeadConsTrue
#assert_no_axioms FX1Poly.Polygraph.brBelowHeadConsLt
#assert_no_axioms FX1Poly.Polygraph.brNFSortedCons
#assert_no_axioms FX1Poly.Polygraph.brBelowHeadInsert
#assert_no_axioms FX1Poly.Polygraph.brInsertPreservesSorted
#assert_no_axioms FX1Poly.Polygraph.brInsertFront
#assert_no_axioms FX1Poly.Polygraph.brMergeXorNilRight
#assert_no_axioms FX1Poly.Polygraph.brMergeXorComm
#assert_no_axioms FX1Poly.Polygraph.brMergeXorPreservesSorted
#assert_no_axioms FX1Poly.Polygraph.brTermMul
#assert_no_axioms FX1Poly.Polygraph.brMulConvolve
#assert_no_axioms FX1Poly.Polygraph.brTermMulNil
#assert_no_axioms FX1Poly.Polygraph.brTermMulCons
#assert_no_axioms FX1Poly.Polygraph.brMulConvolveNil
#assert_no_axioms FX1Poly.Polygraph.brMulConvolveCons
#assert_no_axioms FX1Poly.Polygraph.brTermMulSorted
#assert_no_axioms FX1Poly.Polygraph.brMulConvolveSorted
#assert_no_axioms FX1Poly.Polygraph.brTermMul_insertTerm
#assert_no_axioms FX1Poly.Polygraph.brTermMul_merge
#assert_no_axioms FX1Poly.Polygraph.brMulConvolveAnnihil
#assert_no_axioms FX1Poly.Polygraph.brMergeXor4Swap
#assert_no_axioms FX1Poly.Polygraph.brMulConvolve_leftDistrib
#assert_no_axioms FX1Poly.Polygraph.brTermMul_coeffXor
#assert_no_axioms FX1Poly.Polygraph.brConvolve_insertTermLeft
#assert_no_axioms FX1Poly.Polygraph.brMulConvolve_rightDistrib
#assert_no_axioms FX1Poly.Polygraph.brTermMul_compose
#assert_no_axioms FX1Poly.Polygraph.brTermMul_convolve
#assert_no_axioms FX1Poly.Polygraph.brMulConvolveAssoc
#assert_no_axioms FX1Poly.Polygraph.brNFMonoSorted
#assert_no_axioms FX1Poly.Polygraph.brNFMonoSortedCons
#assert_no_axioms FX1Poly.Polygraph.brInsertTermMonoSorted
#assert_no_axioms FX1Poly.Polygraph.brMergeXorMonoSorted
#assert_no_axioms FX1Poly.Polygraph.brTermMulMonoSorted
#assert_no_axioms FX1Poly.Polygraph.brMulConvolveMonoSorted
#assert_no_axioms FX1Poly.Polygraph.brTermMulEqConvolveSingle
#assert_no_axioms FX1Poly.Polygraph.brMulConvolveComm
#assert_no_axioms FX1Poly.Polygraph.brMulConvolveUnit
#assert_no_axioms FX1Poly.Polygraph.brNFAllZero
#assert_no_axioms FX1Poly.Polygraph.brNFAllZeroCons
#assert_no_axioms FX1Poly.Polygraph.brInsertTermAllZero
#assert_no_axioms FX1Poly.Polygraph.brMergeXorAllZero
#assert_no_axioms FX1Poly.Polygraph.brCondCoeff
#assert_no_axioms FX1Poly.Polygraph.brCondCoeffTrue
#assert_no_axioms FX1Poly.Polygraph.brCondCoeffFalse
#assert_no_axioms FX1Poly.Polygraph.brCondCoeffZero
#assert_no_axioms FX1Poly.Polygraph.brMonoEqFalseOfLt
#assert_no_axioms FX1Poly.Polygraph.brEvalCross
#assert_no_axioms FX1Poly.Polygraph.brEvalCrossNil
#assert_no_axioms FX1Poly.Polygraph.brEvalCrossCons
#assert_no_axioms FX1Poly.Polygraph.brEvalCross_insertTerm
#assert_no_axioms FX1Poly.Polygraph.brEvalCross_mergeXor
#assert_no_axioms FX1Poly.Polygraph.brAllZero_evalZero
#assert_no_axioms FX1Poly.Polygraph.brEvalBelowZero
#assert_no_axioms FX1Poly.Polygraph.brSortedEvalZero_allZero
#assert_no_axioms FX1Poly.Polygraph.brMergeXorAllZeroCancel
#assert_no_axioms FX1Poly.Polygraph.brMergeXorSelfAllZero
#assert_no_axioms FX1Poly.Polygraph.brTermMulCoeffZeroAllZero
#assert_no_axioms FX1Poly.Polygraph.brTermMulRightAllZero
#assert_no_axioms FX1Poly.Polygraph.brMulConvolveLeftAllZero
#assert_no_axioms FX1Poly.Polygraph.brMulConvolveRightAllZero
#assert_no_axioms FX1Poly.Polygraph.brNFEq
#assert_no_axioms FX1Poly.Polygraph.brNFEqRefl
#assert_no_axioms FX1Poly.Polygraph.brNFEqOfEq
#assert_no_axioms FX1Poly.Polygraph.brNFEqSymm
#assert_no_axioms FX1Poly.Polygraph.brNFEqTrans
#assert_no_axioms FX1Poly.Polygraph.brNFEqMergeCongr
#assert_no_axioms FX1Poly.Polygraph.brNFEqMulCongr
#assert_no_axioms FX1Poly.Polygraph.brNFEqNil
#assert_no_axioms FX1Poly.Polygraph.BrTree
#assert_no_axioms FX1Poly.Polygraph.brNormalize
#assert_no_axioms FX1Poly.Polygraph.brNormalize_zero_smoke
#assert_no_axioms FX1Poly.Polygraph.brNormalize_one_smoke
#assert_no_axioms FX1Poly.Polygraph.brNormalize_gen_smoke
#assert_no_axioms FX1Poly.Polygraph.brNormalizeSorted
#assert_no_axioms FX1Poly.Polygraph.brNormalizeMonoSorted
#assert_no_axioms FX1Poly.Polygraph.brNormalizeAndIdemGen
#assert_no_axioms FX1Poly.Polygraph.BooleanRingTreeConv
#assert_no_axioms FX1Poly.Polygraph.brNormalize_respects
#assert_no_axioms FX1Poly.Polygraph.brConvXorZeroLeft
#assert_no_axioms FX1Poly.Polygraph.brConvAndOneLeft
#assert_no_axioms FX1Poly.Polygraph.brConvAnnihilLeft
#assert_no_axioms FX1Poly.Polygraph.brConvDistribRight
#assert_no_axioms FX1Poly.Polygraph.brConvXorSwap13
#assert_no_axioms FX1Poly.Polygraph.brConvAndSwap13
#assert_no_axioms FX1Poly.Polygraph.brMonoToTree
#assert_no_axioms FX1Poly.Polygraph.brMonoToTreeInsertSortedSet
#assert_no_axioms FX1Poly.Polygraph.brMonoToTreeInsertManySet
#assert_no_axioms FX1Poly.Polygraph.brMonoToTreeMonoMul
#assert_no_axioms FX1Poly.Polygraph.brTermToTree
#assert_no_axioms FX1Poly.Polygraph.brTermToTreeXor
#assert_no_axioms FX1Poly.Polygraph.brTermToTreeMul
#assert_no_axioms FX1Poly.Polygraph.brTermToTreeZero
#assert_no_axioms FX1Poly.Polygraph.brCombOfNF
#assert_no_axioms FX1Poly.Polygraph.brCombOfNFCons
#assert_no_axioms FX1Poly.Polygraph.brCombInsertTerm
#assert_no_axioms FX1Poly.Polygraph.brCombMergeXor
#assert_no_axioms FX1Poly.Polygraph.brCombTermMul
#assert_no_axioms FX1Poly.Polygraph.brCombMulConvolve
#assert_no_axioms FX1Poly.Polygraph.brCombAllZero
#assert_no_axioms FX1Poly.Polygraph.brTreeReifies
#assert_no_axioms FX1Poly.Polygraph.brConvOfXorZero
#assert_no_axioms FX1Poly.Polygraph.brCombOfNFEqConv
#assert_no_axioms FX1Poly.Polygraph.brConv_of_normalizeEq
#assert_no_axioms FX1Poly.Polygraph.brDecideConv
#assert_no_axioms FX1Poly.Polygraph.booleanRingTreeConv_iff_normalForm
#assert_no_axioms FX1Poly.Polygraph.instDecidableBooleanRingTreeConv
#assert_no_axioms FX1Poly.Polygraph.fxWalkingBooleanRing_hasNormalFormDecision

end FX1PolyAudit
