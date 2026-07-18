import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingRing.RingSeed

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingRing.RingSeed — zero-axiom gate (the FULLY DECIDED walking free non-commutative ring on ℕ)

Per-declaration zero-axiom gate for the walking free NON-COMMUTATIVE ring on `ℕ` — the polynomial ring `ℤ⟨X⟩`
decision (the mechanical merge of the `ℕ⟨X⟩` word semiring and the `ℤ[X]` integer-coefficient ring).  Monomials
are order-significant WORDS with monomial product = cons-only word CONCATENATION `frWordCat` (never
`List.append`); the total word order is the imported structural `csrCompare`.  Integer coefficients are
subtraction-free `(pos, neg)` ℕ-pairs, so no `Int` and no `Nat.sub` appear.  Covers the coefficient ring
algebra (`frCoeffAdd` / `frCoeffMul` / `frCoeffNeg` / `frCoeffEq` with the clean `Nat` kit `frNatMulAssoc` /
`frNatAddMul` / `frNatAddRightCancel` / `frNatOneMul` replacing the propext-leaky `Nat.mul_assoc` /
`Nat.add_mul`), the pair-coefficient normal-form machinery (`frInsertTermComm`, `frMergeAdd`, the word
convolution `frMulConvolve` with BOTH annihilations / BOTH distributivities / associativity / BOTH units — no
convolution commutativity), `frNegate`, the `frEvalCross` model with the all-zero cancellation
`frMergeAddAllZeroCancel` and the crux `frMergeAddSelfNegAllZero`, the decision equivalence `frNFEq`, the
`FrTree` carrier with `negOp`, `frNormalize`, the `RingTreeConv` convertibility, soundness
(`frNormalize_respects`), the rebuild `frCombOfNF` with the negation-through-mul word reification
(`frTermToTreeMul` / `frMonoToTreeWordCat`), completeness (`frConv_of_normalizeEq`), and THE DECISION
(`frDecideConv` / `ringTreeConv_iff_normalForm` / the `Decidable` instance `frDecidableConv`) plus its marker.
Every landed declaration must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`,
`omega` — the word order is the imported structural `csrCompare` (built on `natBle`), word concatenation is the
cons-only `frWordCat`, integer coefficients are `(pos, neg)` ℕ-pairs (no `Int`, no `Nat.sub`), and no
`List.append` (`++`) / `Nat.le` / `Nat.ble` lemma / `Nat.mul_assoc` / `Nat.add_mul` is used. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.frWordCat
#assert_no_axioms FX1Poly.Polygraph.frWordCatNilLeft
#assert_no_axioms FX1Poly.Polygraph.frWordCatNilRight
#assert_no_axioms FX1Poly.Polygraph.frWordCatAssoc
#assert_no_axioms FX1Poly.Polygraph.frNatMulAssoc
#assert_no_axioms FX1Poly.Polygraph.frNatAddMul
#assert_no_axioms FX1Poly.Polygraph.frNatAddRightCancel
#assert_no_axioms FX1Poly.Polygraph.frNatOneMul
#assert_no_axioms FX1Poly.Polygraph.frCoeffAdd
#assert_no_axioms FX1Poly.Polygraph.frCoeffMul
#assert_no_axioms FX1Poly.Polygraph.frCoeffNeg
#assert_no_axioms FX1Poly.Polygraph.frCoeffEq
#assert_no_axioms FX1Poly.Polygraph.frCoeffIsZero
#assert_no_axioms FX1Poly.Polygraph.frCoeffAddComm
#assert_no_axioms FX1Poly.Polygraph.frCoeffAddAssoc
#assert_no_axioms FX1Poly.Polygraph.frCoeffAddZeroRight
#assert_no_axioms FX1Poly.Polygraph.frCoeffAddZeroLeft
#assert_no_axioms FX1Poly.Polygraph.frCoeffNegAdd
#assert_no_axioms FX1Poly.Polygraph.frCoeffNegNeg
#assert_no_axioms FX1Poly.Polygraph.frCoeffAddNegIsZero
#assert_no_axioms FX1Poly.Polygraph.frCoeffAddZeroValued
#assert_no_axioms FX1Poly.Polygraph.frCoeffNegIsZero
#assert_no_axioms FX1Poly.Polygraph.frCoeffAddCancelZero
#assert_no_axioms FX1Poly.Polygraph.frNatAddMiddleFour
#assert_no_axioms FX1Poly.Polygraph.frCoeffMulComm
#assert_no_axioms FX1Poly.Polygraph.frCoeffMulOne
#assert_no_axioms FX1Poly.Polygraph.frCoeffOneMul
#assert_no_axioms FX1Poly.Polygraph.frCoeffMulZeroRight
#assert_no_axioms FX1Poly.Polygraph.frCoeffMulAddRight
#assert_no_axioms FX1Poly.Polygraph.frCoeffAddMulRight
#assert_no_axioms FX1Poly.Polygraph.frCoeffNegMulLeft
#assert_no_axioms FX1Poly.Polygraph.frCoeffMulAssoc
#assert_no_axioms FX1Poly.Polygraph.frCoeffEqRefl
#assert_no_axioms FX1Poly.Polygraph.frCoeffEqSymm
#assert_no_axioms FX1Poly.Polygraph.FrNF
#assert_no_axioms FX1Poly.Polygraph.frInsertTerm
#assert_no_axioms FX1Poly.Polygraph.frInsertTermNil
#assert_no_axioms FX1Poly.Polygraph.frInsertTermEqE
#assert_no_axioms FX1Poly.Polygraph.frInsertTermLtE
#assert_no_axioms FX1Poly.Polygraph.frInsertTermGtE
#assert_no_axioms FX1Poly.Polygraph.frCoeffAddRightComm
#assert_no_axioms FX1Poly.Polygraph.frInsertTermComm
#assert_no_axioms FX1Poly.Polygraph.frMergeAdd
#assert_no_axioms FX1Poly.Polygraph.frMergeAddNilLeft
#assert_no_axioms FX1Poly.Polygraph.frMergeAddCons
#assert_no_axioms FX1Poly.Polygraph.frInsertTerm_mergeAdd
#assert_no_axioms FX1Poly.Polygraph.frInsertTermMergeSame
#assert_no_axioms FX1Poly.Polygraph.frMergeAddInsertTermLeft
#assert_no_axioms FX1Poly.Polygraph.frMergeAddAssoc
#assert_no_axioms FX1Poly.Polygraph.frMergeAddSwap
#assert_no_axioms FX1Poly.Polygraph.frBelowHead
#assert_no_axioms FX1Poly.Polygraph.frNFSorted
#assert_no_axioms FX1Poly.Polygraph.frBelowHeadNil
#assert_no_axioms FX1Poly.Polygraph.frBelowHeadConsTrue
#assert_no_axioms FX1Poly.Polygraph.frBelowHeadConsLt
#assert_no_axioms FX1Poly.Polygraph.frNFSortedCons
#assert_no_axioms FX1Poly.Polygraph.frBelowHeadInsert
#assert_no_axioms FX1Poly.Polygraph.frInsertPreservesSorted
#assert_no_axioms FX1Poly.Polygraph.frInsertFront
#assert_no_axioms FX1Poly.Polygraph.frMergeAddNilRight
#assert_no_axioms FX1Poly.Polygraph.frMergeAddComm
#assert_no_axioms FX1Poly.Polygraph.frMergeAddPreservesSorted
#assert_no_axioms FX1Poly.Polygraph.frTermMul
#assert_no_axioms FX1Poly.Polygraph.frMulConvolve
#assert_no_axioms FX1Poly.Polygraph.frTermMulNil
#assert_no_axioms FX1Poly.Polygraph.frTermMulCons
#assert_no_axioms FX1Poly.Polygraph.frMulConvolveNil
#assert_no_axioms FX1Poly.Polygraph.frMulConvolveCons
#assert_no_axioms FX1Poly.Polygraph.frTermMulSorted
#assert_no_axioms FX1Poly.Polygraph.frMulConvolveSorted
#assert_no_axioms FX1Poly.Polygraph.frTermMul_insertTerm
#assert_no_axioms FX1Poly.Polygraph.frTermMul_merge
#assert_no_axioms FX1Poly.Polygraph.frMulConvolveAnnihil
#assert_no_axioms FX1Poly.Polygraph.frMergeAdd4Swap
#assert_no_axioms FX1Poly.Polygraph.frMulConvolve_leftDistrib
#assert_no_axioms FX1Poly.Polygraph.frTermMul_coeffAdd
#assert_no_axioms FX1Poly.Polygraph.frConvolve_insertTermLeft
#assert_no_axioms FX1Poly.Polygraph.frMulConvolve_rightDistrib
#assert_no_axioms FX1Poly.Polygraph.frTermMul_compose
#assert_no_axioms FX1Poly.Polygraph.frTermMul_convolve
#assert_no_axioms FX1Poly.Polygraph.frMulConvolveAssoc
#assert_no_axioms FX1Poly.Polygraph.frTermMulIdent
#assert_no_axioms FX1Poly.Polygraph.frMulConvolveUnitLeft
#assert_no_axioms FX1Poly.Polygraph.frMulConvolveUnitRight
#assert_no_axioms FX1Poly.Polygraph.frNegate
#assert_no_axioms FX1Poly.Polygraph.frNegateCons
#assert_no_axioms FX1Poly.Polygraph.frNegateBelowHead
#assert_no_axioms FX1Poly.Polygraph.frNegateSorted
#assert_no_axioms FX1Poly.Polygraph.frNegateInvol
#assert_no_axioms FX1Poly.Polygraph.frNegate_insertTerm
#assert_no_axioms FX1Poly.Polygraph.frNegate_mergeAdd
#assert_no_axioms FX1Poly.Polygraph.frNFAllZero
#assert_no_axioms FX1Poly.Polygraph.frNFAllZeroCons
#assert_no_axioms FX1Poly.Polygraph.frNegatePreservesAllZero
#assert_no_axioms FX1Poly.Polygraph.frInsertTermAllZero
#assert_no_axioms FX1Poly.Polygraph.frMergeAddAllZero
#assert_no_axioms FX1Poly.Polygraph.frCondCoeff
#assert_no_axioms FX1Poly.Polygraph.frCondCoeffTrue
#assert_no_axioms FX1Poly.Polygraph.frCondCoeffFalse
#assert_no_axioms FX1Poly.Polygraph.frCondCoeffZero
#assert_no_axioms FX1Poly.Polygraph.frCoeffAddSwap13
#assert_no_axioms FX1Poly.Polygraph.frCoeffNegAddIsZero
#assert_no_axioms FX1Poly.Polygraph.frNatListEqFalseOfLt
#assert_no_axioms FX1Poly.Polygraph.frEvalCross
#assert_no_axioms FX1Poly.Polygraph.frEvalCrossNil
#assert_no_axioms FX1Poly.Polygraph.frEvalCrossCons
#assert_no_axioms FX1Poly.Polygraph.frEvalCross_insertTerm
#assert_no_axioms FX1Poly.Polygraph.frEvalCross_mergeAdd
#assert_no_axioms FX1Poly.Polygraph.frAllZero_evalZero
#assert_no_axioms FX1Poly.Polygraph.frEvalBelowZero
#assert_no_axioms FX1Poly.Polygraph.frSortedEvalZero_allZero
#assert_no_axioms FX1Poly.Polygraph.frMergeAddAllZeroCancel
#assert_no_axioms FX1Poly.Polygraph.frCondCoeffNeg
#assert_no_axioms FX1Poly.Polygraph.frEvalCross_negate
#assert_no_axioms FX1Poly.Polygraph.frMergeAddSelfNegAllZero
#assert_no_axioms FX1Poly.Polygraph.frCoeffMulZeroValuedLeft
#assert_no_axioms FX1Poly.Polygraph.frCoeffMulZeroValuedRight
#assert_no_axioms FX1Poly.Polygraph.frCoeffNegMulRight
#assert_no_axioms FX1Poly.Polygraph.frTermMulCoeffZeroAllZero
#assert_no_axioms FX1Poly.Polygraph.frTermMulRightAllZero
#assert_no_axioms FX1Poly.Polygraph.frMulConvolveLeftAllZero
#assert_no_axioms FX1Poly.Polygraph.frMulConvolveRightAllZero
#assert_no_axioms FX1Poly.Polygraph.frNegate_termMulLeft
#assert_no_axioms FX1Poly.Polygraph.frNegate_termMulRight
#assert_no_axioms FX1Poly.Polygraph.frNegate_mulConvolveLeft
#assert_no_axioms FX1Poly.Polygraph.frNegate_mulConvolveRight
#assert_no_axioms FX1Poly.Polygraph.frNFEq
#assert_no_axioms FX1Poly.Polygraph.frNFEqRefl
#assert_no_axioms FX1Poly.Polygraph.frNFEqOfEq
#assert_no_axioms FX1Poly.Polygraph.frNFEqSymm
#assert_no_axioms FX1Poly.Polygraph.frNFEqTrans
#assert_no_axioms FX1Poly.Polygraph.frNFEqMergeCongr
#assert_no_axioms FX1Poly.Polygraph.frNFEqMulCongr
#assert_no_axioms FX1Poly.Polygraph.frNFEqNegCongr
#assert_no_axioms FX1Poly.Polygraph.frNFEqNil
#assert_no_axioms FX1Poly.Polygraph.FrTree
#assert_no_axioms FX1Poly.Polygraph.frNormalize
#assert_no_axioms FX1Poly.Polygraph.frNormalize_gen
#assert_no_axioms FX1Poly.Polygraph.frNormalizeSorted
#assert_no_axioms FX1Poly.Polygraph.frNormalize_zero_smoke
#assert_no_axioms FX1Poly.Polygraph.frNormalize_one_smoke
#assert_no_axioms FX1Poly.Polygraph.frNormalize_negGen_smoke
#assert_no_axioms FX1Poly.Polygraph.RingTreeConv
#assert_no_axioms FX1Poly.Polygraph.frNormalize_respects
#assert_no_axioms FX1Poly.Polygraph.frConvAddZeroLeft
#assert_no_axioms FX1Poly.Polygraph.frConvAddSwap13
#assert_no_axioms FX1Poly.Polygraph.frConvAddMiddleFour
#assert_no_axioms FX1Poly.Polygraph.frConvAddNegInverseLeft
#assert_no_axioms FX1Poly.Polygraph.frConvInvUnique
#assert_no_axioms FX1Poly.Polygraph.frConvNegZero
#assert_no_axioms FX1Poly.Polygraph.frConvNegNeg
#assert_no_axioms FX1Poly.Polygraph.frConvMulNegRight
#assert_no_axioms FX1Poly.Polygraph.frConvMulNegLeft
#assert_no_axioms FX1Poly.Polygraph.frConvMulNegNeg
#assert_no_axioms FX1Poly.Polygraph.frConvNegAdd
#assert_no_axioms FX1Poly.Polygraph.frConvMulAddAdd
#assert_no_axioms FX1Poly.Polygraph.frScaleTree
#assert_no_axioms FX1Poly.Polygraph.frScaleTreeCongr
#assert_no_axioms FX1Poly.Polygraph.frScaleAdd
#assert_no_axioms FX1Poly.Polygraph.frScaleTreeMulLeft
#assert_no_axioms FX1Poly.Polygraph.frScaleTreeMulRight
#assert_no_axioms FX1Poly.Polygraph.frScaleTreeMulCoeff
#assert_no_axioms FX1Poly.Polygraph.frScaleTreeMulBoth
#assert_no_axioms FX1Poly.Polygraph.frMonoToTree
#assert_no_axioms FX1Poly.Polygraph.frMonoToTreeWordCat
#assert_no_axioms FX1Poly.Polygraph.frTermToTree
#assert_no_axioms FX1Poly.Polygraph.frTermToTreeEq
#assert_no_axioms FX1Poly.Polygraph.frTermToTreeAdd
#assert_no_axioms FX1Poly.Polygraph.frTermToTreeMul
#assert_no_axioms FX1Poly.Polygraph.frCombOfNF
#assert_no_axioms FX1Poly.Polygraph.frCombOfNFCons
#assert_no_axioms FX1Poly.Polygraph.frCombInsertTerm
#assert_no_axioms FX1Poly.Polygraph.frCombMergeAdd
#assert_no_axioms FX1Poly.Polygraph.frCombTermMul
#assert_no_axioms FX1Poly.Polygraph.frCombMulConvolve
#assert_no_axioms FX1Poly.Polygraph.frScaleTreeNeg
#assert_no_axioms FX1Poly.Polygraph.frTermToTreeNeg
#assert_no_axioms FX1Poly.Polygraph.frCombNegate
#assert_no_axioms FX1Poly.Polygraph.frScaleTreeNegCancel
#assert_no_axioms FX1Poly.Polygraph.frTermToTreeZero
#assert_no_axioms FX1Poly.Polygraph.frCombAllZero
#assert_no_axioms FX1Poly.Polygraph.frMonoToTreeTermOne
#assert_no_axioms FX1Poly.Polygraph.frTreeReifies
#assert_no_axioms FX1Poly.Polygraph.frConvOfSubZero
#assert_no_axioms FX1Poly.Polygraph.frCombOfNFEqConv
#assert_no_axioms FX1Poly.Polygraph.frConv_of_normalizeEq
#assert_no_axioms FX1Poly.Polygraph.frDecideConv
#assert_no_axioms FX1Poly.Polygraph.ringTreeConv_iff_normalForm
#assert_no_axioms FX1Poly.Polygraph.frDecidableConv
#assert_no_axioms FX1Poly.Polygraph.fxWalkingRing_hasNormalFormDecision

end FX1PolyAudit
