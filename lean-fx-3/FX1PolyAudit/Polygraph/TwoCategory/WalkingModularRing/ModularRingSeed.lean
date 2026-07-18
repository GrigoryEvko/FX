import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingModularRing.ModularRingSeed

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingModularRing.ModularRingSeed — zero-axiom gate (the FULLY DECIDED walking free commutative ring over ℤ/6)

Per-declaration zero-axiom gate for the walking free commutative ring over `ℤ/n` — the polynomial ring
`(ℤ/6)[X]`.  The modular successor of the ℕ[X] commutative-semiring rung: the same monomial machinery
(sorted-`List Nat` multiset via the imported `insertMany`, monomial order, convolution) with coefficients
reduced mod `mrModulus = 6` via the imported structural counting divider `natRemainder` and the vanishing terms
dropped, plus the single characteristic law `nTimesOne` (`6` copies of `1` are `≈ 0`).  `6` is composite with
zero divisors `2·3 ≡ 0`, so `(ℤ/6)[X]` is not an integral domain.  Covers the modular coefficient arithmetic
(`mrRemIdem` / `mrRemAddPushRight` / `mrRemMulPushRight` / `mrRemAddZeroModRight` / `mrRemMulZeroMod`), the
reduction pass `mrReduce` with its sortedness-preservation (`mrReduceSorted` / `mrReduceBelowHead`) and the
crux reduction-insertion homomorphism `mrReduceInsertReduce` from which flow the merge / term-scaling /
convolution homomorphisms (`mrReduceMergeHom` / `mrReduceTermMulRightHom` / `mrReduceConvolveHom`), the tree
carrier `MrTree`, the base-then-reduce `mrNormalize`, the `ModularRingTreeConv` convertibility (the eleven
commutative-semiring laws PLUS the characteristic `nTimesOne`), soundness (`mrNormalize_respects`, the
congruence cases via the homomorphisms and `nTimesOne` via `natRemainderSelf`), the reification tower with the
modular collapse `mrScaleTreeCharN` (`6·X ≈ 0`) and `mrScaleReduce`, completeness (`mrConv_of_normalizeEq`),
and THE DECISION (`mrDecideConv` / `modularRingTreeConv_iff_normalForm` / the `Decidable` instance
`mrDecidableConv`) plus its marker.  Every landed declaration must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, and all other non-Init axioms — verified below by an independent
per-declaration `#assert_no_axioms`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.mrModulus
#assert_no_axioms FX1Poly.Polygraph.mrModulusPos
#assert_no_axioms FX1Poly.Polygraph.mrRemIdem
#assert_no_axioms FX1Poly.Polygraph.mrRemZero
#assert_no_axioms FX1Poly.Polygraph.mrRemAddPushRight
#assert_no_axioms FX1Poly.Polygraph.mrRemMulPushRight
#assert_no_axioms FX1Poly.Polygraph.mrRemAddZeroModRight
#assert_no_axioms FX1Poly.Polygraph.mrRemMulZeroMod
#assert_no_axioms FX1Poly.Polygraph.mrReduce
#assert_no_axioms FX1Poly.Polygraph.mrReduceNil
#assert_no_axioms FX1Poly.Polygraph.mrReduceConsZero
#assert_no_axioms FX1Poly.Polygraph.mrReduceConsNonzero
#assert_no_axioms FX1Poly.Polygraph.mrBeqZeroEq
#assert_no_axioms FX1Poly.Polygraph.mrBeqZeroOf
#assert_no_axioms FX1Poly.Polygraph.mrReduceIdem
#assert_no_axioms FX1Poly.Polygraph.mrBelowHeadStep
#assert_no_axioms FX1Poly.Polygraph.mrReduceBelowHead
#assert_no_axioms FX1Poly.Polygraph.mrReduceSorted
#assert_no_axioms FX1Poly.Polygraph.mrReduceInsertZero
#assert_no_axioms FX1Poly.Polygraph.mrReduceInsertReduce
#assert_no_axioms FX1Poly.Polygraph.mrReduceMergeHom
#assert_no_axioms FX1Poly.Polygraph.mrReduceTermMulZero
#assert_no_axioms FX1Poly.Polygraph.mrReduceTermMulScalar
#assert_no_axioms FX1Poly.Polygraph.mrReduceTermMulRightHom
#assert_no_axioms FX1Poly.Polygraph.mrReduceConvolveHom
#assert_no_axioms FX1Poly.Polygraph.MrTree
#assert_no_axioms FX1Poly.Polygraph.mrBaseNormalize
#assert_no_axioms FX1Poly.Polygraph.mrBaseNormalizeSorted
#assert_no_axioms FX1Poly.Polygraph.mrBaseNormalizeMonoSorted
#assert_no_axioms FX1Poly.Polygraph.mrNormalize
#assert_no_axioms FX1Poly.Polygraph.mrNormalize_zero_smoke
#assert_no_axioms FX1Poly.Polygraph.mrNormalize_one_smoke
#assert_no_axioms FX1Poly.Polygraph.mrSumOfOnes
#assert_no_axioms FX1Poly.Polygraph.mrConstNF
#assert_no_axioms FX1Poly.Polygraph.mrInsertOneConstNF
#assert_no_axioms FX1Poly.Polygraph.mrBaseNormalizeSumOfOnes
#assert_no_axioms FX1Poly.Polygraph.mrReduceSingletonModulus
#assert_no_axioms FX1Poly.Polygraph.ModularRingTreeConv
#assert_no_axioms FX1Poly.Polygraph.mrNormalizeAddCongr
#assert_no_axioms FX1Poly.Polygraph.mrNormalizeMulCongr
#assert_no_axioms FX1Poly.Polygraph.mrNormalize_respects
#assert_no_axioms FX1Poly.Polygraph.mrConvAddZeroLeft
#assert_no_axioms FX1Poly.Polygraph.mrConvMulOneLeft
#assert_no_axioms FX1Poly.Polygraph.mrConvAnnihilLeft
#assert_no_axioms FX1Poly.Polygraph.mrConvDistribRight
#assert_no_axioms FX1Poly.Polygraph.mrConvAddSwap13
#assert_no_axioms FX1Poly.Polygraph.mrConvMulSwap13
#assert_no_axioms FX1Poly.Polygraph.mrScaleTree
#assert_no_axioms FX1Poly.Polygraph.mrScaleTreeCongr
#assert_no_axioms FX1Poly.Polygraph.mrScaleAdd
#assert_no_axioms FX1Poly.Polygraph.mrScaleTreeMulLeft
#assert_no_axioms FX1Poly.Polygraph.mrScaleTreeMulRight
#assert_no_axioms FX1Poly.Polygraph.mrScaleTreeMulCoeff
#assert_no_axioms FX1Poly.Polygraph.mrMonoToTree
#assert_no_axioms FX1Poly.Polygraph.mrMonoToTreeInsertSorted
#assert_no_axioms FX1Poly.Polygraph.mrMonoToTreeInsertMany
#assert_no_axioms FX1Poly.Polygraph.mrMonoToTreeMonoMul
#assert_no_axioms FX1Poly.Polygraph.mrTermToTree
#assert_no_axioms FX1Poly.Polygraph.mrTermToTreeMul
#assert_no_axioms FX1Poly.Polygraph.mrCombOfNF
#assert_no_axioms FX1Poly.Polygraph.mrCombOfNFCons
#assert_no_axioms FX1Poly.Polygraph.mrCombInsertTerm
#assert_no_axioms FX1Poly.Polygraph.mrCombMergeAdd
#assert_no_axioms FX1Poly.Polygraph.mrCombTermMul
#assert_no_axioms FX1Poly.Polygraph.mrCombMulConvolve
#assert_no_axioms FX1Poly.Polygraph.mrBaseReifies
#assert_no_axioms FX1Poly.Polygraph.mrScaleTreeEqMulSum
#assert_no_axioms FX1Poly.Polygraph.mrScaleTreeCharN
#assert_no_axioms FX1Poly.Polygraph.mrScaleMultipleZero
#assert_no_axioms FX1Poly.Polygraph.mrScaleReduce
#assert_no_axioms FX1Poly.Polygraph.mrReduceReifies
#assert_no_axioms FX1Poly.Polygraph.mrTreeReifies
#assert_no_axioms FX1Poly.Polygraph.mrConv_of_normalizeEq
#assert_no_axioms FX1Poly.Polygraph.mrNFEq
#assert_no_axioms FX1Poly.Polygraph.mrNFEqRefl
#assert_no_axioms FX1Poly.Polygraph.mrNFEq_eq
#assert_no_axioms FX1Poly.Polygraph.mrDecideConv
#assert_no_axioms FX1Poly.Polygraph.modularRingTreeConv_iff_normalForm
#assert_no_axioms FX1Poly.Polygraph.mrDecidableConv
#assert_no_axioms FX1Poly.Polygraph.fxWalkingModularRing_hasNormalFormDecision

end FX1PolyAudit
