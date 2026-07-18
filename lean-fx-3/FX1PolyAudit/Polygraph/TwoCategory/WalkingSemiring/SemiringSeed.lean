import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingSemiring.SemiringSeed

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingSemiring.SemiringSeed — zero-axiom gate (the FULLY DECIDED walking free NON-commutative semiring on ℕ)

Per-declaration zero-axiom gate for the walking free non-commutative semiring on `ℕ` — the polynomial `ℕ⟨X⟩`
decision.  Covers the word order kit (`ncsrWordBle` length-first-then-lex with total / trans / antisym), the
structural list/Nat equality helpers, the clean structural `Nat` multiplication kit (`ncsrNatMulAssoc` /
`ncsrNatAddMul` / `ncsrNatOneMul`, replacing the propext-leaky `Nat.mul_assoc` / `Nat.add_mul`), the 3-way
compare `ncsrCompare`, the term-insertion `ncsrInsertTerm` with the commutation `ncsrInsertTermComm`, the
additive commutative monoid (`ncsrMergeAdd` associative / commutative / unit on the `ncsrNFSorted` invariant),
WORD CONCATENATION `ncsrWordCat` (cons-only, with left/right unit and associativity), the convolution
`ncsrMulConvolve` with both annihilations / left+right distributivity / associativity / both units (NO
commutativity), the `NcsrTree` carrier, the `ncsrNormalize` normal form with its sortedness invariant, the
`NoncommSemiringTreeConv` convertibility, soundness (`ncsrNormalize_respects`), the tree-rebuild reification
(`ncsrCombOfNF` / `ncsrTreeReifies` and the scale-tree / word reification `ncsrMonoToTreeWordCat`),
completeness (`ncsrConv_of_normalizeEq`), and THE DECISION (`ncsrDecideConv` /
`noncommSemiringTreeConv_iff_normalForm` / the `Decidable` instance `ncsrDecidableConv`) plus its marker.
Every landed declaration must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`,
`omega` — the ordering is the imported structural `natBle`, word concatenation is the cons-only `ncsrWordCat`
(never `List.append` / `++`), no `Nat.le` / `Nat.ble` lemma / `Int` is used, and coefficient arithmetic uses
only the clean add lemmas plus the hand-proved multiplication kit. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.ncsrLen
#assert_no_axioms FX1Poly.Polygraph.ncsrLexBle
#assert_no_axioms FX1Poly.Polygraph.ncsrWordBle
#assert_no_axioms FX1Poly.Polygraph.ncsrWordEq
#assert_no_axioms FX1Poly.Polygraph.ncsrWordBleFF
#assert_no_axioms FX1Poly.Polygraph.ncsrWordBleTF
#assert_no_axioms FX1Poly.Polygraph.ncsrWordBleTT
#assert_no_axioms FX1Poly.Polygraph.ncsrLexConsTF
#assert_no_axioms FX1Poly.Polygraph.ncsrLexConsTT
#assert_no_axioms FX1Poly.Polygraph.ncsrLexConsFF
#assert_no_axioms FX1Poly.Polygraph.ncsrLexBleTotalEqLen
#assert_no_axioms FX1Poly.Polygraph.ncsrLexBleAntisymmEqLen
#assert_no_axioms FX1Poly.Polygraph.ncsrLexBleTransEqLen
#assert_no_axioms FX1Poly.Polygraph.ncsrWordBleTotal
#assert_no_axioms FX1Poly.Polygraph.ncsrWordBleAntisymm
#assert_no_axioms FX1Poly.Polygraph.ncsrWordBleTrans
#assert_no_axioms FX1Poly.Polygraph.ncsrNatBeqRefl
#assert_no_axioms FX1Poly.Polygraph.ncsrNatBeqSymm
#assert_no_axioms FX1Poly.Polygraph.ncsrNatEqOfBeq
#assert_no_axioms FX1Poly.Polygraph.ncsrWordEqRefl
#assert_no_axioms FX1Poly.Polygraph.ncsrWordEqSymm
#assert_no_axioms FX1Poly.Polygraph.ncsrWordEq_eq
#assert_no_axioms FX1Poly.Polygraph.ncsrWordEqOfEq
#assert_no_axioms FX1Poly.Polygraph.ncsrNatMulAssoc
#assert_no_axioms FX1Poly.Polygraph.ncsrNatAddMul
#assert_no_axioms FX1Poly.Polygraph.ncsrNatOneMul
#assert_no_axioms FX1Poly.Polygraph.NcsrWordOrd
#assert_no_axioms FX1Poly.Polygraph.ncsrCompare
#assert_no_axioms FX1Poly.Polygraph.ncsrCompareEqExpand
#assert_no_axioms FX1Poly.Polygraph.ncsrCompareLtExpand
#assert_no_axioms FX1Poly.Polygraph.ncsrCompareGtExpand
#assert_no_axioms FX1Poly.Polygraph.ncsrCompareRefl
#assert_no_axioms FX1Poly.Polygraph.ncsrCompareOfEq
#assert_no_axioms FX1Poly.Polygraph.ncsrCompareEq_of
#assert_no_axioms FX1Poly.Polygraph.ncsrCompareSwapLt
#assert_no_axioms FX1Poly.Polygraph.ncsrCompareSwapGt
#assert_no_axioms FX1Poly.Polygraph.ncsrCompareTransLt
#assert_no_axioms FX1Poly.Polygraph.NcsrNF
#assert_no_axioms FX1Poly.Polygraph.ncsrInsertTerm
#assert_no_axioms FX1Poly.Polygraph.ncsrInsertTermNil
#assert_no_axioms FX1Poly.Polygraph.ncsrInsertTermEqE
#assert_no_axioms FX1Poly.Polygraph.ncsrInsertTermLtE
#assert_no_axioms FX1Poly.Polygraph.ncsrInsertTermGtE
#assert_no_axioms FX1Poly.Polygraph.ncsrAddRightComm
#assert_no_axioms FX1Poly.Polygraph.ncsrInsertTermComm
#assert_no_axioms FX1Poly.Polygraph.ncsrAndTrueLeft
#assert_no_axioms FX1Poly.Polygraph.ncsrAndTrueRight
#assert_no_axioms FX1Poly.Polygraph.ncsrAndIntro
#assert_no_axioms FX1Poly.Polygraph.ncsrMergeAdd
#assert_no_axioms FX1Poly.Polygraph.ncsrMergeAddNilLeft
#assert_no_axioms FX1Poly.Polygraph.ncsrMergeAddCons
#assert_no_axioms FX1Poly.Polygraph.ncsrInsertTerm_mergeAdd
#assert_no_axioms FX1Poly.Polygraph.ncsrInsertTermMergeSame
#assert_no_axioms FX1Poly.Polygraph.ncsrMergeAddInsertTermLeft
#assert_no_axioms FX1Poly.Polygraph.ncsrMergeAddAssoc
#assert_no_axioms FX1Poly.Polygraph.ncsrMergeAddSwap
#assert_no_axioms FX1Poly.Polygraph.ncsrBelowHead
#assert_no_axioms FX1Poly.Polygraph.ncsrNFSorted
#assert_no_axioms FX1Poly.Polygraph.ncsrBelowHeadNil
#assert_no_axioms FX1Poly.Polygraph.ncsrBelowHeadConsTrue
#assert_no_axioms FX1Poly.Polygraph.ncsrBelowHeadConsLt
#assert_no_axioms FX1Poly.Polygraph.ncsrNFSortedCons
#assert_no_axioms FX1Poly.Polygraph.ncsrBelowHeadInsert
#assert_no_axioms FX1Poly.Polygraph.ncsrInsertPreservesSorted
#assert_no_axioms FX1Poly.Polygraph.ncsrInsertFront
#assert_no_axioms FX1Poly.Polygraph.ncsrMergeAddNilRight
#assert_no_axioms FX1Poly.Polygraph.ncsrMergeAddComm
#assert_no_axioms FX1Poly.Polygraph.ncsrMergeAddPreservesSorted
#assert_no_axioms FX1Poly.Polygraph.ncsrWordCat
#assert_no_axioms FX1Poly.Polygraph.ncsrWordCatNilLeft
#assert_no_axioms FX1Poly.Polygraph.ncsrWordCatNilRight
#assert_no_axioms FX1Poly.Polygraph.ncsrWordCatAssoc
#assert_no_axioms FX1Poly.Polygraph.ncsrTermMul
#assert_no_axioms FX1Poly.Polygraph.ncsrMulConvolve
#assert_no_axioms FX1Poly.Polygraph.ncsrTermMulNil
#assert_no_axioms FX1Poly.Polygraph.ncsrTermMulCons
#assert_no_axioms FX1Poly.Polygraph.ncsrMulConvolveNil
#assert_no_axioms FX1Poly.Polygraph.ncsrMulConvolveCons
#assert_no_axioms FX1Poly.Polygraph.ncsrTermMulSorted
#assert_no_axioms FX1Poly.Polygraph.ncsrMulConvolveSorted
#assert_no_axioms FX1Poly.Polygraph.ncsrTermMul_insertTerm
#assert_no_axioms FX1Poly.Polygraph.ncsrTermMul_merge
#assert_no_axioms FX1Poly.Polygraph.ncsrMulConvolveAnnihil
#assert_no_axioms FX1Poly.Polygraph.ncsrMergeAdd4Swap
#assert_no_axioms FX1Poly.Polygraph.ncsrMulConvolve_leftDistrib
#assert_no_axioms FX1Poly.Polygraph.ncsrTermMul_coeffAdd
#assert_no_axioms FX1Poly.Polygraph.ncsrConvolve_insertTermLeft
#assert_no_axioms FX1Poly.Polygraph.ncsrMulConvolve_rightDistrib
#assert_no_axioms FX1Poly.Polygraph.ncsrTermMul_compose
#assert_no_axioms FX1Poly.Polygraph.ncsrTermMul_convolve
#assert_no_axioms FX1Poly.Polygraph.ncsrMulConvolveAssoc
#assert_no_axioms FX1Poly.Polygraph.ncsrTermMulIdent
#assert_no_axioms FX1Poly.Polygraph.ncsrMulConvolveUnitLeft
#assert_no_axioms FX1Poly.Polygraph.ncsrMulConvolveUnitRight
#assert_no_axioms FX1Poly.Polygraph.NcsrTree
#assert_no_axioms FX1Poly.Polygraph.ncsrNormalize
#assert_no_axioms FX1Poly.Polygraph.ncsrNormalize_gen
#assert_no_axioms FX1Poly.Polygraph.ncsrNormalizeSorted
#assert_no_axioms FX1Poly.Polygraph.ncsrNormalize_zero_smoke
#assert_no_axioms FX1Poly.Polygraph.ncsrNormalize_one_smoke
#assert_no_axioms FX1Poly.Polygraph.ncsrNormalize_distribRight_smoke
#assert_no_axioms FX1Poly.Polygraph.NoncommSemiringTreeConv
#assert_no_axioms FX1Poly.Polygraph.ncsrNormalize_respects
#assert_no_axioms FX1Poly.Polygraph.ncsrConvAddZeroLeft
#assert_no_axioms FX1Poly.Polygraph.ncsrConvAddSwap13
#assert_no_axioms FX1Poly.Polygraph.ncsrScaleTree
#assert_no_axioms FX1Poly.Polygraph.ncsrScaleTreeCongr
#assert_no_axioms FX1Poly.Polygraph.ncsrScaleAdd
#assert_no_axioms FX1Poly.Polygraph.ncsrScaleTreeMulLeft
#assert_no_axioms FX1Poly.Polygraph.ncsrScaleTreeMulRight
#assert_no_axioms FX1Poly.Polygraph.ncsrScaleTreeMulCoeff
#assert_no_axioms FX1Poly.Polygraph.ncsrMonoToTree
#assert_no_axioms FX1Poly.Polygraph.ncsrMonoToTreeWordCat
#assert_no_axioms FX1Poly.Polygraph.ncsrTermToTree
#assert_no_axioms FX1Poly.Polygraph.ncsrTermToTreeMul
#assert_no_axioms FX1Poly.Polygraph.ncsrCombOfNF
#assert_no_axioms FX1Poly.Polygraph.ncsrCombOfNFCons
#assert_no_axioms FX1Poly.Polygraph.ncsrCombInsertTerm
#assert_no_axioms FX1Poly.Polygraph.ncsrCombMergeAdd
#assert_no_axioms FX1Poly.Polygraph.ncsrCombTermMul
#assert_no_axioms FX1Poly.Polygraph.ncsrCombMulConvolve
#assert_no_axioms FX1Poly.Polygraph.ncsrTreeReifies
#assert_no_axioms FX1Poly.Polygraph.ncsrConv_of_normalizeEq
#assert_no_axioms FX1Poly.Polygraph.ncsrNFEq
#assert_no_axioms FX1Poly.Polygraph.ncsrNFEqRefl
#assert_no_axioms FX1Poly.Polygraph.ncsrNFEq_eq
#assert_no_axioms FX1Poly.Polygraph.ncsrDecideConv
#assert_no_axioms FX1Poly.Polygraph.noncommSemiringTreeConv_iff_normalForm
#assert_no_axioms FX1Poly.Polygraph.ncsrDecidableConv
#assert_no_axioms FX1Poly.Polygraph.fxWalkingSemiring_hasNormalFormDecision

end FX1PolyAudit
