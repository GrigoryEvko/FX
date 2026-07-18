import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingCommutativeRing.CommutativeRingSeed

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingCommutativeRing.CommutativeRingSeed — zero-axiom gate (the FULLY DECIDED walking free commutative ring on ℕ)

Per-declaration zero-axiom gate for the walking free commutative ring on `ℕ` — the polynomial ring `ℤ[X]`
decision.  Integer coefficients are subtraction-free `(pos, neg)` ℕ-pairs (mirroring the `ColourAbelianGroup`
winding representation), so no `Int` and no `Nat.sub` appear.  Covers the coefficient ring algebra
(`fcrCoeffAdd` / `fcrCoeffMul` / `fcrCoeffNeg` / `fcrCoeffEq` with add/mul comm/assoc/unit/zero/distributivity
up to `fcrCoeffEq`, and the hand-proved clean `Nat` kit `fcrNatMulAssoc` / `fcrNatAddMul` /
`fcrNatAddRightCancel` replacing the propext-leaky `Nat.mul_assoc` / `Nat.add_mul`), the pair-coefficient
normal-form machinery (`fcrInsertTerm` with the crux commutation `fcrInsertTermComm`, `fcrMergeAdd`, the
convolution `fcrMulConvolve` with annihilation / distributivity / associativity / commutativity / unit),
`fcrNegate`, the `fcrEvalCross` semantic model with the all-zero cancellation `fcrMergeAddAllZeroCancel` and
the crux `fcrMergeAdd_selfNeg` (`fcrMergeAddSelfNegAllZero`), the decision equivalence `fcrNFEq` with its full
equivalence + congruence structure, the `FcrTree` carrier with `negOp`, `fcrNormalize`, the `CommRingTreeConv`
convertibility, soundness (`fcrNormalize_respects`), the rebuild `fcrCombOfNF` with the negation-through-mul
reification (`fcrTermToTreeMul`), completeness (`fcrConv_of_normalizeEq`), and THE DECISION
(`fcrDecideConv` / `commRingTreeConv_iff_normalForm` / the `Decidable` instance `fcrDecidableConv`) plus its
marker.  Every landed declaration must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega` — the ordering is the imported structural `natBle`, integer coefficients are `(pos,
neg)` ℕ-pairs (no `Int`, no `Nat.sub`), the list plumbing is cons-only, and no `List.append` (`++`) /
`Nat.le` / `Nat.ble` lemma / `Nat.mul_assoc` / `Nat.add_mul` is used. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.fcrNatMulAssoc
#assert_no_axioms FX1Poly.Polygraph.fcrNatAddMul
#assert_no_axioms FX1Poly.Polygraph.fcrNatAddRightCancel
#assert_no_axioms FX1Poly.Polygraph.fcrCoeffAdd
#assert_no_axioms FX1Poly.Polygraph.fcrCoeffMul
#assert_no_axioms FX1Poly.Polygraph.fcrCoeffNeg
#assert_no_axioms FX1Poly.Polygraph.fcrCoeffEq
#assert_no_axioms FX1Poly.Polygraph.fcrCoeffIsZero
#assert_no_axioms FX1Poly.Polygraph.fcrCoeffAddComm
#assert_no_axioms FX1Poly.Polygraph.fcrCoeffAddAssoc
#assert_no_axioms FX1Poly.Polygraph.fcrCoeffAddZeroRight
#assert_no_axioms FX1Poly.Polygraph.fcrCoeffAddZeroLeft
#assert_no_axioms FX1Poly.Polygraph.fcrCoeffNegAdd
#assert_no_axioms FX1Poly.Polygraph.fcrCoeffNegNeg
#assert_no_axioms FX1Poly.Polygraph.fcrCoeffAddNegIsZero
#assert_no_axioms FX1Poly.Polygraph.fcrCoeffAddZeroValued
#assert_no_axioms FX1Poly.Polygraph.fcrCoeffNegIsZero
#assert_no_axioms FX1Poly.Polygraph.fcrCoeffAddCancelZero
#assert_no_axioms FX1Poly.Polygraph.fcrNatAddMiddleFour
#assert_no_axioms FX1Poly.Polygraph.fcrCoeffMulComm
#assert_no_axioms FX1Poly.Polygraph.fcrCoeffMulOne
#assert_no_axioms FX1Poly.Polygraph.fcrCoeffMulZeroRight
#assert_no_axioms FX1Poly.Polygraph.fcrCoeffMulAddRight
#assert_no_axioms FX1Poly.Polygraph.fcrCoeffAddMulRight
#assert_no_axioms FX1Poly.Polygraph.fcrCoeffNegMulLeft
#assert_no_axioms FX1Poly.Polygraph.fcrCoeffMulAssoc
#assert_no_axioms FX1Poly.Polygraph.fcrCoeffEqRefl
#assert_no_axioms FX1Poly.Polygraph.fcrCoeffEqSymm
#assert_no_axioms FX1Poly.Polygraph.FcrNF
#assert_no_axioms FX1Poly.Polygraph.fcrInsertTerm
#assert_no_axioms FX1Poly.Polygraph.fcrInsertTermNil
#assert_no_axioms FX1Poly.Polygraph.fcrInsertTermEqE
#assert_no_axioms FX1Poly.Polygraph.fcrInsertTermLtE
#assert_no_axioms FX1Poly.Polygraph.fcrInsertTermGtE
#assert_no_axioms FX1Poly.Polygraph.fcrCoeffAddRightComm
#assert_no_axioms FX1Poly.Polygraph.fcrInsertTermComm
#assert_no_axioms FX1Poly.Polygraph.fcrMergeAdd
#assert_no_axioms FX1Poly.Polygraph.fcrMergeAddNilLeft
#assert_no_axioms FX1Poly.Polygraph.fcrMergeAddCons
#assert_no_axioms FX1Poly.Polygraph.fcrInsertTerm_mergeAdd
#assert_no_axioms FX1Poly.Polygraph.fcrInsertTermMergeSame
#assert_no_axioms FX1Poly.Polygraph.fcrMergeAddInsertTermLeft
#assert_no_axioms FX1Poly.Polygraph.fcrMergeAddAssoc
#assert_no_axioms FX1Poly.Polygraph.fcrMergeAddSwap
#assert_no_axioms FX1Poly.Polygraph.fcrBelowHead
#assert_no_axioms FX1Poly.Polygraph.fcrNFSorted
#assert_no_axioms FX1Poly.Polygraph.fcrBelowHeadNil
#assert_no_axioms FX1Poly.Polygraph.fcrBelowHeadConsTrue
#assert_no_axioms FX1Poly.Polygraph.fcrBelowHeadConsLt
#assert_no_axioms FX1Poly.Polygraph.fcrNFSortedCons
#assert_no_axioms FX1Poly.Polygraph.fcrBelowHeadInsert
#assert_no_axioms FX1Poly.Polygraph.fcrInsertPreservesSorted
#assert_no_axioms FX1Poly.Polygraph.fcrInsertFront
#assert_no_axioms FX1Poly.Polygraph.fcrMergeAddNilRight
#assert_no_axioms FX1Poly.Polygraph.fcrMergeAddComm
#assert_no_axioms FX1Poly.Polygraph.fcrMergeAddPreservesSorted
#assert_no_axioms FX1Poly.Polygraph.fcrTermMul
#assert_no_axioms FX1Poly.Polygraph.fcrMulConvolve
#assert_no_axioms FX1Poly.Polygraph.fcrTermMulNil
#assert_no_axioms FX1Poly.Polygraph.fcrTermMulCons
#assert_no_axioms FX1Poly.Polygraph.fcrMulConvolveNil
#assert_no_axioms FX1Poly.Polygraph.fcrMulConvolveCons
#assert_no_axioms FX1Poly.Polygraph.fcrTermMulSorted
#assert_no_axioms FX1Poly.Polygraph.fcrMulConvolveSorted
#assert_no_axioms FX1Poly.Polygraph.fcrTermMul_insertTerm
#assert_no_axioms FX1Poly.Polygraph.fcrTermMul_merge
#assert_no_axioms FX1Poly.Polygraph.fcrMulConvolveAnnihil
#assert_no_axioms FX1Poly.Polygraph.fcrMergeAdd4Swap
#assert_no_axioms FX1Poly.Polygraph.fcrMulConvolve_leftDistrib
#assert_no_axioms FX1Poly.Polygraph.fcrTermMul_coeffAdd
#assert_no_axioms FX1Poly.Polygraph.fcrConvolve_insertTermLeft
#assert_no_axioms FX1Poly.Polygraph.fcrMulConvolve_rightDistrib
#assert_no_axioms FX1Poly.Polygraph.fcrTermMul_compose
#assert_no_axioms FX1Poly.Polygraph.fcrTermMul_convolve
#assert_no_axioms FX1Poly.Polygraph.fcrMulConvolveAssoc
#assert_no_axioms FX1Poly.Polygraph.fcrNFMonoSorted
#assert_no_axioms FX1Poly.Polygraph.fcrNFMonoSortedCons
#assert_no_axioms FX1Poly.Polygraph.fcrInsertTermMonoSorted
#assert_no_axioms FX1Poly.Polygraph.fcrMergeAddMonoSorted
#assert_no_axioms FX1Poly.Polygraph.fcrTermMulMonoSorted
#assert_no_axioms FX1Poly.Polygraph.fcrMulConvolveMonoSorted
#assert_no_axioms FX1Poly.Polygraph.fcrTermMulEqConvolveSingle
#assert_no_axioms FX1Poly.Polygraph.fcrMulConvolveComm
#assert_no_axioms FX1Poly.Polygraph.fcrMulConvolveUnit
#assert_no_axioms FX1Poly.Polygraph.fcrNegate
#assert_no_axioms FX1Poly.Polygraph.fcrNegateCons
#assert_no_axioms FX1Poly.Polygraph.fcrNegateBelowHead
#assert_no_axioms FX1Poly.Polygraph.fcrNegateSorted
#assert_no_axioms FX1Poly.Polygraph.fcrNegateInvol
#assert_no_axioms FX1Poly.Polygraph.fcrNegate_insertTerm
#assert_no_axioms FX1Poly.Polygraph.fcrNegate_mergeAdd
#assert_no_axioms FX1Poly.Polygraph.fcrNFAllZero
#assert_no_axioms FX1Poly.Polygraph.fcrNFAllZeroCons
#assert_no_axioms FX1Poly.Polygraph.fcrNegatePreservesAllZero
#assert_no_axioms FX1Poly.Polygraph.fcrInsertTermAllZero
#assert_no_axioms FX1Poly.Polygraph.fcrMergeAddAllZero
#assert_no_axioms FX1Poly.Polygraph.fcrCondCoeff
#assert_no_axioms FX1Poly.Polygraph.fcrCondCoeffTrue
#assert_no_axioms FX1Poly.Polygraph.fcrCondCoeffFalse
#assert_no_axioms FX1Poly.Polygraph.fcrCondCoeffZero
#assert_no_axioms FX1Poly.Polygraph.fcrCoeffAddSwap13
#assert_no_axioms FX1Poly.Polygraph.fcrCoeffNegAddIsZero
#assert_no_axioms FX1Poly.Polygraph.fcrNatListEqFalseOfLt
#assert_no_axioms FX1Poly.Polygraph.fcrEvalCross
#assert_no_axioms FX1Poly.Polygraph.fcrEvalCrossNil
#assert_no_axioms FX1Poly.Polygraph.fcrEvalCrossCons
#assert_no_axioms FX1Poly.Polygraph.fcrEvalCross_insertTerm
#assert_no_axioms FX1Poly.Polygraph.fcrEvalCross_mergeAdd
#assert_no_axioms FX1Poly.Polygraph.fcrAllZero_evalZero
#assert_no_axioms FX1Poly.Polygraph.fcrEvalBelowZero
#assert_no_axioms FX1Poly.Polygraph.fcrSortedEvalZero_allZero
#assert_no_axioms FX1Poly.Polygraph.fcrMergeAddAllZeroCancel
#assert_no_axioms FX1Poly.Polygraph.fcrCondCoeffNeg
#assert_no_axioms FX1Poly.Polygraph.fcrEvalCross_negate
#assert_no_axioms FX1Poly.Polygraph.fcrMergeAddSelfNegAllZero
#assert_no_axioms FX1Poly.Polygraph.fcrCoeffMulZeroValuedLeft
#assert_no_axioms FX1Poly.Polygraph.fcrCoeffMulZeroValuedRight
#assert_no_axioms FX1Poly.Polygraph.fcrCoeffNegMulRight
#assert_no_axioms FX1Poly.Polygraph.fcrTermMulCoeffZeroAllZero
#assert_no_axioms FX1Poly.Polygraph.fcrTermMulRightAllZero
#assert_no_axioms FX1Poly.Polygraph.fcrMulConvolveLeftAllZero
#assert_no_axioms FX1Poly.Polygraph.fcrMulConvolveRightAllZero
#assert_no_axioms FX1Poly.Polygraph.fcrNegate_termMulLeft
#assert_no_axioms FX1Poly.Polygraph.fcrNegate_termMulRight
#assert_no_axioms FX1Poly.Polygraph.fcrNegate_mulConvolveLeft
#assert_no_axioms FX1Poly.Polygraph.fcrNegate_mulConvolveRight
#assert_no_axioms FX1Poly.Polygraph.fcrNFEq
#assert_no_axioms FX1Poly.Polygraph.fcrNFEqRefl
#assert_no_axioms FX1Poly.Polygraph.fcrNFEqOfEq
#assert_no_axioms FX1Poly.Polygraph.fcrNFEqSymm
#assert_no_axioms FX1Poly.Polygraph.fcrNFEqTrans
#assert_no_axioms FX1Poly.Polygraph.fcrNFEqMergeCongr
#assert_no_axioms FX1Poly.Polygraph.fcrNFEqMulCongr
#assert_no_axioms FX1Poly.Polygraph.fcrNFEqNegCongr
#assert_no_axioms FX1Poly.Polygraph.fcrNFEqNil
#assert_no_axioms FX1Poly.Polygraph.FcrTree
#assert_no_axioms FX1Poly.Polygraph.fcrNormalize
#assert_no_axioms FX1Poly.Polygraph.fcrNormalize_gen
#assert_no_axioms FX1Poly.Polygraph.fcrNegateMonoSorted
#assert_no_axioms FX1Poly.Polygraph.fcrNormalizeSorted
#assert_no_axioms FX1Poly.Polygraph.fcrNormalizeMonoSorted
#assert_no_axioms FX1Poly.Polygraph.fcrNormalize_zero_smoke
#assert_no_axioms FX1Poly.Polygraph.fcrNormalize_one_smoke
#assert_no_axioms FX1Poly.Polygraph.fcrNormalize_negGen_smoke
#assert_no_axioms FX1Poly.Polygraph.CommRingTreeConv
#assert_no_axioms FX1Poly.Polygraph.fcrNormalize_respects
#assert_no_axioms FX1Poly.Polygraph.fcrConvAddZeroLeft
#assert_no_axioms FX1Poly.Polygraph.fcrConvMulOneLeft
#assert_no_axioms FX1Poly.Polygraph.fcrConvAnnihilLeft
#assert_no_axioms FX1Poly.Polygraph.fcrConvDistribRight
#assert_no_axioms FX1Poly.Polygraph.fcrConvAddSwap13
#assert_no_axioms FX1Poly.Polygraph.fcrConvMulSwap13
#assert_no_axioms FX1Poly.Polygraph.fcrConvAddMiddleFour
#assert_no_axioms FX1Poly.Polygraph.fcrConvAddNegInverseLeft
#assert_no_axioms FX1Poly.Polygraph.fcrConvInvUnique
#assert_no_axioms FX1Poly.Polygraph.fcrConvNegZero
#assert_no_axioms FX1Poly.Polygraph.fcrConvNegNeg
#assert_no_axioms FX1Poly.Polygraph.fcrConvMulNegRight
#assert_no_axioms FX1Poly.Polygraph.fcrConvMulNegLeft
#assert_no_axioms FX1Poly.Polygraph.fcrConvMulNegNeg
#assert_no_axioms FX1Poly.Polygraph.fcrConvNegAdd
#assert_no_axioms FX1Poly.Polygraph.fcrConvMulAddAdd
#assert_no_axioms FX1Poly.Polygraph.fcrScaleTree
#assert_no_axioms FX1Poly.Polygraph.fcrScaleTreeCongr
#assert_no_axioms FX1Poly.Polygraph.fcrScaleAdd
#assert_no_axioms FX1Poly.Polygraph.fcrScaleTreeMulLeft
#assert_no_axioms FX1Poly.Polygraph.fcrScaleTreeMulRight
#assert_no_axioms FX1Poly.Polygraph.fcrScaleTreeMulCoeff
#assert_no_axioms FX1Poly.Polygraph.fcrScaleTreeMulBoth
#assert_no_axioms FX1Poly.Polygraph.fcrMonoToTree
#assert_no_axioms FX1Poly.Polygraph.fcrMonoToTreeInsertSorted
#assert_no_axioms FX1Poly.Polygraph.fcrMonoToTreeInsertMany
#assert_no_axioms FX1Poly.Polygraph.fcrMonoToTreeMonoMul
#assert_no_axioms FX1Poly.Polygraph.fcrTermToTree
#assert_no_axioms FX1Poly.Polygraph.fcrTermToTreeEq
#assert_no_axioms FX1Poly.Polygraph.fcrTermToTreeAdd
#assert_no_axioms FX1Poly.Polygraph.fcrTermToTreeMul
#assert_no_axioms FX1Poly.Polygraph.fcrCombOfNF
#assert_no_axioms FX1Poly.Polygraph.fcrCombOfNFCons
#assert_no_axioms FX1Poly.Polygraph.fcrCombInsertTerm
#assert_no_axioms FX1Poly.Polygraph.fcrCombMergeAdd
#assert_no_axioms FX1Poly.Polygraph.fcrCombTermMul
#assert_no_axioms FX1Poly.Polygraph.fcrCombMulConvolve
#assert_no_axioms FX1Poly.Polygraph.fcrScaleTreeNeg
#assert_no_axioms FX1Poly.Polygraph.fcrTermToTreeNeg
#assert_no_axioms FX1Poly.Polygraph.fcrCombNegate
#assert_no_axioms FX1Poly.Polygraph.fcrScaleTreeNegCancel
#assert_no_axioms FX1Poly.Polygraph.fcrTermToTreeZero
#assert_no_axioms FX1Poly.Polygraph.fcrCombAllZero
#assert_no_axioms FX1Poly.Polygraph.fcrMonoToTreeTermOne
#assert_no_axioms FX1Poly.Polygraph.fcrTreeReifies
#assert_no_axioms FX1Poly.Polygraph.fcrConvOfSubZero
#assert_no_axioms FX1Poly.Polygraph.fcrCombOfNFEqConv
#assert_no_axioms FX1Poly.Polygraph.fcrConv_of_normalizeEq
#assert_no_axioms FX1Poly.Polygraph.fcrDecideConv
#assert_no_axioms FX1Poly.Polygraph.commRingTreeConv_iff_normalForm
#assert_no_axioms FX1Poly.Polygraph.fcrDecidableConv
#assert_no_axioms FX1Poly.Polygraph.fxWalkingCommutativeRing_hasNormalFormDecision

end FX1PolyAudit
