import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingCommutativeSemiring.CommutativeSemiringSeed

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingCommutativeSemiring.CommutativeSemiringSeed — zero-axiom gate (the FULLY DECIDED walking free commutative semiring on ℕ)

Per-declaration zero-axiom gate for the walking free commutative semiring on `ℕ` — the polynomial `ℕ[X]`
decision.  Covers the monomial order kit (`csrMonoBle` length-first-then-lex with total / trans / antisym),
the structural list/Nat equality helpers, the clean structural `Nat` multiplication kit (`csrNatMulAssoc` /
`csrNatAddMul`, replacing the propext-leaky `Nat.mul_assoc` / `Nat.add_mul`), the 3-way compare `csrCompare`,
the term-insertion `csrInsertTerm` with the crux commutation `csrInsertTermComm`, the additive commutative
monoid (`csrMergeAdd` associative / commutative / unit on the `csrNFSorted` invariant), the monomial
multiplication `csrMonoMul` with the monomial-sortedness kit, the convolution `csrMulConvolve` with
annihilation / left+right distributivity / associativity / commutativity / unit, the `CsrTree` carrier, the
`csrNormalize` normal form with its sortedness invariants, the `SemiringTreeConv` convertibility, soundness
(`csrNormalize_respects`), the tree-rebuild reification (`csrCombOfNF` / `csrTreeReifies` and the scale-tree /
monomial reification algebra), completeness (`csrConv_of_normalizeEq`), and THE DECISION
(`csrDecideConv` / `semiringTreeConv_iff_normalForm` / the `Decidable` instance `csrDecidableConv`) plus its
marker.  Every landed declaration must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega` — the ordering is the imported structural `natBle`, the list plumbing is cons-only,
no `List.append` (`++`) / `Nat.le` / `Nat.ble` lemma / `Int` is used, and coefficient arithmetic uses only the
clean add lemmas plus the hand-proved multiplication kit. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.CsrNF
#assert_no_axioms FX1Poly.Polygraph.csrLen
#assert_no_axioms FX1Poly.Polygraph.csrLexBle
#assert_no_axioms FX1Poly.Polygraph.csrMonoBle
#assert_no_axioms FX1Poly.Polygraph.csrNatListEq
#assert_no_axioms FX1Poly.Polygraph.csrMonoBleFF
#assert_no_axioms FX1Poly.Polygraph.csrMonoBleTF
#assert_no_axioms FX1Poly.Polygraph.csrMonoBleTT
#assert_no_axioms FX1Poly.Polygraph.csrLexConsTF
#assert_no_axioms FX1Poly.Polygraph.csrLexConsTT
#assert_no_axioms FX1Poly.Polygraph.csrLexConsFF
#assert_no_axioms FX1Poly.Polygraph.csrLexBleTotalEqLen
#assert_no_axioms FX1Poly.Polygraph.csrLexBleAntisymmEqLen
#assert_no_axioms FX1Poly.Polygraph.csrLexBleTransEqLen
#assert_no_axioms FX1Poly.Polygraph.csrMonoBleTotal
#assert_no_axioms FX1Poly.Polygraph.csrMonoBleAntisymm
#assert_no_axioms FX1Poly.Polygraph.csrMonoBleTrans
#assert_no_axioms FX1Poly.Polygraph.csrNatBeqRefl
#assert_no_axioms FX1Poly.Polygraph.csrNatBeqSymm
#assert_no_axioms FX1Poly.Polygraph.csrNatEqOfBeq
#assert_no_axioms FX1Poly.Polygraph.csrNatListEqRefl
#assert_no_axioms FX1Poly.Polygraph.csrNatListEqSymm
#assert_no_axioms FX1Poly.Polygraph.csrNatListEq_eq
#assert_no_axioms FX1Poly.Polygraph.csrNatListEqOfEq
#assert_no_axioms FX1Poly.Polygraph.csrNatMulAssoc
#assert_no_axioms FX1Poly.Polygraph.csrNatAddMul
#assert_no_axioms FX1Poly.Polygraph.CsrMonoOrd
#assert_no_axioms FX1Poly.Polygraph.csrCompare
#assert_no_axioms FX1Poly.Polygraph.csrCompareEqExpand
#assert_no_axioms FX1Poly.Polygraph.csrCompareLtExpand
#assert_no_axioms FX1Poly.Polygraph.csrCompareGtExpand
#assert_no_axioms FX1Poly.Polygraph.csrCompareRefl
#assert_no_axioms FX1Poly.Polygraph.csrCompareOfEq
#assert_no_axioms FX1Poly.Polygraph.csrCompareEq_of
#assert_no_axioms FX1Poly.Polygraph.csrCompareSwapLt
#assert_no_axioms FX1Poly.Polygraph.csrCompareSwapGt
#assert_no_axioms FX1Poly.Polygraph.csrCompareTransLt
#assert_no_axioms FX1Poly.Polygraph.csrInsertTerm
#assert_no_axioms FX1Poly.Polygraph.csrInsertTermNil
#assert_no_axioms FX1Poly.Polygraph.csrInsertTermEqE
#assert_no_axioms FX1Poly.Polygraph.csrInsertTermLtE
#assert_no_axioms FX1Poly.Polygraph.csrInsertTermGtE
#assert_no_axioms FX1Poly.Polygraph.csrAddRightComm
#assert_no_axioms FX1Poly.Polygraph.csrInsertTermComm
#assert_no_axioms FX1Poly.Polygraph.csrAndTrueLeft
#assert_no_axioms FX1Poly.Polygraph.csrAndTrueRight
#assert_no_axioms FX1Poly.Polygraph.csrAndIntro
#assert_no_axioms FX1Poly.Polygraph.csrMergeAdd
#assert_no_axioms FX1Poly.Polygraph.csrMergeAddNilLeft
#assert_no_axioms FX1Poly.Polygraph.csrMergeAddCons
#assert_no_axioms FX1Poly.Polygraph.csrInsertTerm_mergeAdd
#assert_no_axioms FX1Poly.Polygraph.csrInsertTermMergeSame
#assert_no_axioms FX1Poly.Polygraph.csrMergeAddInsertTermLeft
#assert_no_axioms FX1Poly.Polygraph.csrMergeAddAssoc
#assert_no_axioms FX1Poly.Polygraph.csrMergeAddSwap
#assert_no_axioms FX1Poly.Polygraph.csrBelowHead
#assert_no_axioms FX1Poly.Polygraph.csrNFSorted
#assert_no_axioms FX1Poly.Polygraph.csrBelowHeadNil
#assert_no_axioms FX1Poly.Polygraph.csrBelowHeadConsTrue
#assert_no_axioms FX1Poly.Polygraph.csrBelowHeadConsLt
#assert_no_axioms FX1Poly.Polygraph.csrNFSortedCons
#assert_no_axioms FX1Poly.Polygraph.csrBelowHeadInsert
#assert_no_axioms FX1Poly.Polygraph.csrInsertPreservesSorted
#assert_no_axioms FX1Poly.Polygraph.csrInsertFront
#assert_no_axioms FX1Poly.Polygraph.csrMergeAddNilRight
#assert_no_axioms FX1Poly.Polygraph.csrMergeAddComm
#assert_no_axioms FX1Poly.Polygraph.csrMergeAddPreservesSorted
#assert_no_axioms FX1Poly.Polygraph.csrMonoMul
#assert_no_axioms FX1Poly.Polygraph.csrMonoMulNilRight
#assert_no_axioms FX1Poly.Polygraph.csrMonoMulAssoc
#assert_no_axioms FX1Poly.Polygraph.csrMonoBelow
#assert_no_axioms FX1Poly.Polygraph.csrMonoSorted
#assert_no_axioms FX1Poly.Polygraph.csrMonoBelowNil
#assert_no_axioms FX1Poly.Polygraph.csrMonoBelowCons
#assert_no_axioms FX1Poly.Polygraph.csrMonoSortedCons
#assert_no_axioms FX1Poly.Polygraph.csrMonoSortedSingleton
#assert_no_axioms FX1Poly.Polygraph.csrMonoBelowInsert
#assert_no_axioms FX1Poly.Polygraph.csrInsertSortedPreservesSorted
#assert_no_axioms FX1Poly.Polygraph.csrInsertManyPreservesSorted
#assert_no_axioms FX1Poly.Polygraph.csrMonoMulSorted
#assert_no_axioms FX1Poly.Polygraph.csrMonoInsertFront
#assert_no_axioms FX1Poly.Polygraph.csrMonoFixpoint
#assert_no_axioms FX1Poly.Polygraph.csrMonoMulComm
#assert_no_axioms FX1Poly.Polygraph.csrTermMul
#assert_no_axioms FX1Poly.Polygraph.csrMulConvolve
#assert_no_axioms FX1Poly.Polygraph.csrTermMulNil
#assert_no_axioms FX1Poly.Polygraph.csrTermMulCons
#assert_no_axioms FX1Poly.Polygraph.csrMulConvolveNil
#assert_no_axioms FX1Poly.Polygraph.csrMulConvolveCons
#assert_no_axioms FX1Poly.Polygraph.csrTermMulSorted
#assert_no_axioms FX1Poly.Polygraph.csrMulConvolveSorted
#assert_no_axioms FX1Poly.Polygraph.csrTermMul_insertTerm
#assert_no_axioms FX1Poly.Polygraph.csrTermMul_merge
#assert_no_axioms FX1Poly.Polygraph.csrMulConvolveAnnihil
#assert_no_axioms FX1Poly.Polygraph.csrMergeAdd4Swap
#assert_no_axioms FX1Poly.Polygraph.csrMulConvolve_leftDistrib
#assert_no_axioms FX1Poly.Polygraph.csrTermMul_coeffAdd
#assert_no_axioms FX1Poly.Polygraph.csrConvolve_insertTermLeft
#assert_no_axioms FX1Poly.Polygraph.csrMulConvolve_rightDistrib
#assert_no_axioms FX1Poly.Polygraph.csrTermMul_compose
#assert_no_axioms FX1Poly.Polygraph.csrTermMul_convolve
#assert_no_axioms FX1Poly.Polygraph.csrMulConvolveAssoc
#assert_no_axioms FX1Poly.Polygraph.csrNFMonoSorted
#assert_no_axioms FX1Poly.Polygraph.csrNFMonoSortedCons
#assert_no_axioms FX1Poly.Polygraph.csrInsertTermMonoSorted
#assert_no_axioms FX1Poly.Polygraph.csrMergeAddMonoSorted
#assert_no_axioms FX1Poly.Polygraph.csrTermMulMonoSorted
#assert_no_axioms FX1Poly.Polygraph.csrMulConvolveMonoSorted
#assert_no_axioms FX1Poly.Polygraph.csrTermMulEqConvolveSingle
#assert_no_axioms FX1Poly.Polygraph.csrMulConvolveComm
#assert_no_axioms FX1Poly.Polygraph.csrMulConvolveUnit
#assert_no_axioms FX1Poly.Polygraph.CsrTree
#assert_no_axioms FX1Poly.Polygraph.csrNormalize
#assert_no_axioms FX1Poly.Polygraph.csrNormalize_gen
#assert_no_axioms FX1Poly.Polygraph.csrNormalizeSorted
#assert_no_axioms FX1Poly.Polygraph.csrNormalizeMonoSorted
#assert_no_axioms FX1Poly.Polygraph.csrNormalize_zero_smoke
#assert_no_axioms FX1Poly.Polygraph.csrNormalize_one_smoke
#assert_no_axioms FX1Poly.Polygraph.csrNormalize_distrib_smoke
#assert_no_axioms FX1Poly.Polygraph.SemiringTreeConv
#assert_no_axioms FX1Poly.Polygraph.csrNormalize_respects
#assert_no_axioms FX1Poly.Polygraph.csrConvAddZeroLeft
#assert_no_axioms FX1Poly.Polygraph.csrConvMulOneLeft
#assert_no_axioms FX1Poly.Polygraph.csrConvAnnihilLeft
#assert_no_axioms FX1Poly.Polygraph.csrConvDistribRight
#assert_no_axioms FX1Poly.Polygraph.csrConvAddSwap13
#assert_no_axioms FX1Poly.Polygraph.csrConvMulSwap13
#assert_no_axioms FX1Poly.Polygraph.csrScaleTree
#assert_no_axioms FX1Poly.Polygraph.csrScaleTreeCongr
#assert_no_axioms FX1Poly.Polygraph.csrScaleAdd
#assert_no_axioms FX1Poly.Polygraph.csrScaleTreeMulLeft
#assert_no_axioms FX1Poly.Polygraph.csrScaleTreeMulRight
#assert_no_axioms FX1Poly.Polygraph.csrScaleTreeMulCoeff
#assert_no_axioms FX1Poly.Polygraph.csrMonoToTree
#assert_no_axioms FX1Poly.Polygraph.csrMonoToTreeInsertSorted
#assert_no_axioms FX1Poly.Polygraph.csrMonoToTreeInsertMany
#assert_no_axioms FX1Poly.Polygraph.csrMonoToTreeMonoMul
#assert_no_axioms FX1Poly.Polygraph.csrTermToTree
#assert_no_axioms FX1Poly.Polygraph.csrTermToTreeMul
#assert_no_axioms FX1Poly.Polygraph.csrCombOfNF
#assert_no_axioms FX1Poly.Polygraph.csrCombOfNFCons
#assert_no_axioms FX1Poly.Polygraph.csrCombInsertTerm
#assert_no_axioms FX1Poly.Polygraph.csrCombMergeAdd
#assert_no_axioms FX1Poly.Polygraph.csrCombTermMul
#assert_no_axioms FX1Poly.Polygraph.csrCombMulConvolve
#assert_no_axioms FX1Poly.Polygraph.csrTreeReifies
#assert_no_axioms FX1Poly.Polygraph.csrConv_of_normalizeEq
#assert_no_axioms FX1Poly.Polygraph.csrNFEq
#assert_no_axioms FX1Poly.Polygraph.csrNFEqRefl
#assert_no_axioms FX1Poly.Polygraph.csrNFEq_eq
#assert_no_axioms FX1Poly.Polygraph.csrDecideConv
#assert_no_axioms FX1Poly.Polygraph.semiringTreeConv_iff_normalForm
#assert_no_axioms FX1Poly.Polygraph.csrDecidableConv
#assert_no_axioms FX1Poly.Polygraph.fxWalkingCommutativeSemiring_hasNormalFormDecision

end FX1PolyAudit
