import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescInsertion

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescInsertion — zero-axiom gate (WP-BRAUER-4 r5–r7)

Per-declaration zero-axiom gate for the crossing-only word-problem layer.  Round 5: the canonical reduced word
(`canonicalCrossingWord` = reverse of the `inversionCount`-fuelled bubble word), the homomorphism helpers, the identity
base, the peel-last outer fold CONDITIONAL on the general insertion step (`crossingOnly_straightens_ofInsertionStep` /
`crossingWords_equalPerm_conv_ofInsertionStep`), and the non-vacuity witnesses.  Round 6: the CANCEL mode general
(`crossingInsertionStep_atLeftmostDescent`) + its structural kit.  Round 7: the HONEST reformulation — the in-range
insertion residual `InRangeInsertionStep` over genuine permutations + the revised well-formed fold, the EXTEND mode
general (`crossingInsertionStep_extend`) + its swap-involution / leftmost-descent-tracking kit, and the COMMUTE mode
local Coxeter step (`crossingInsertionStep_commute_localReduction`).  The private propext-free arithmetic / list
helpers are covered transitively.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- homomorphism helpers + the realized-permutation snoc law
#assert_no_axioms FX1Poly.Polygraph.crossingWord_append
#assert_no_axioms FX1Poly.Polygraph.foldlSwapSnoc
#assert_no_axioms FX1Poly.Polygraph.permuteOfCrossingWord_snoc

-- the canonical reduced word (Lehmer / decreasing-staircase form) + its supporting predicates
#assert_no_axioms FX1Poly.Polygraph.isIdentityPerm
#assert_no_axioms FX1Poly.Polygraph.leftmostDescent
#assert_no_axioms FX1Poly.Polygraph.countEntriesBelow
#assert_no_axioms FX1Poly.Polygraph.inversionCount
#assert_no_axioms FX1Poly.Polygraph.bubbleWordFueled
#assert_no_axioms FX1Poly.Polygraph.bubbleWord
#assert_no_axioms FX1Poly.Polygraph.canonicalCrossingWord

-- the identity base
#assert_no_axioms FX1Poly.Polygraph.isAscendingFrom
#assert_no_axioms FX1Poly.Polygraph.isAscendingFrom_isIdentity
#assert_no_axioms FX1Poly.Polygraph.rangeLoopAscending
#assert_no_axioms FX1Poly.Polygraph.isAscendingFrom_range
#assert_no_axioms FX1Poly.Polygraph.bubbleWordFueled_identity
#assert_no_axioms FX1Poly.Polygraph.canonicalCrossingWord_range

-- the outer fold conditional on the insertion step + the word-problem reduction
#assert_no_axioms FX1Poly.Polygraph.crossingOnly_straightensFueled
#assert_no_axioms FX1Poly.Polygraph.crossingOnly_straightens_ofInsertionStep
#assert_no_axioms FX1Poly.Polygraph.crossingWords_equalPerm_conv_ofInsertionStep

-- non-vacuity: canonical is a genuine reduced word; the three insertion-step modes; the two direct word pairs
#assert_no_axioms FX1Poly.Polygraph.canonical_reducedWord_smoke_transposition
#assert_no_axioms FX1Poly.Polygraph.canonical_reducedWord_smoke_threeCycle
#assert_no_axioms FX1Poly.Polygraph.canonical_reducedWord_smoke_reversal
#assert_no_axioms FX1Poly.Polygraph.crossingInsertionStep_cancel_smoke
#assert_no_axioms FX1Poly.Polygraph.crossingInsertionStep_extend_smoke
#assert_no_axioms FX1Poly.Polygraph.crossingInsertionStep_braid_smoke
#assert_no_axioms FX1Poly.Polygraph.crossingWords_equalPerm_conv_braidPair
#assert_no_axioms FX1Poly.Polygraph.crossingWords_equalPerm_conv_r2Pair

-- WP-BRAUER r6: the CANCEL mode of the insertion step, closed generally, plus its structural kit
-- (staircase snoc, Lehmer measure drop, countEntriesBelow multiset-invariance).  The private propext-free
-- bool / arithmetic / reverse helpers are covered transitively.
#assert_no_axioms FX1Poly.Polygraph.countEntriesBelow_applyAdjacentSwap
#assert_no_axioms FX1Poly.Polygraph.inversionCount_ofLeftmostDescentSwap_succ
#assert_no_axioms FX1Poly.Polygraph.canonicalCrossingWord_snoc_leftmostDescent
#assert_no_axioms FX1Poly.Polygraph.crossingInsertionStep_atLeftmostDescent
#assert_no_axioms FX1Poly.Polygraph.crossingInsertionStep_atLeftmostDescent_smoke

-- WP-BRAUER r7: the HONEST reformulation (in-range insertion step over genuine permutations) + the revised fold.
-- Private propext-free bool / order / list helpers are covered transitively.
#assert_no_axioms FX1Poly.Polygraph.memBool
#assert_no_axioms FX1Poly.Polygraph.isDistinctList
#assert_no_axioms FX1Poly.Polygraph.wellFormedCrossingWord
#assert_no_axioms FX1Poly.Polygraph.InRangeInsertionStep
#assert_no_axioms FX1Poly.Polygraph.memBool_applyAdjacentSwap
#assert_no_axioms FX1Poly.Polygraph.isDistinctList_applyAdjacentSwap
#assert_no_axioms FX1Poly.Polygraph.isDistinctList_range
#assert_no_axioms FX1Poly.Polygraph.isDistinctList_permuteOfCrossingWord
#assert_no_axioms FX1Poly.Polygraph.lastPosition_inRange_ofWellFormed
#assert_no_axioms FX1Poly.Polygraph.crossingOnly_straightensFueled_wellFormed
#assert_no_axioms FX1Poly.Polygraph.crossingOnly_straightens_wellFormed
#assert_no_axioms FX1Poly.Polygraph.crossingWords_equalPerm_conv_wellFormed

-- WP-BRAUER r7: the EXTEND mode (general) + its structural kit (swap involution, leftmost-descent tracking).
#assert_no_axioms FX1Poly.Polygraph.applyAdjacentSwap_involutive
#assert_no_axioms FX1Poly.Polygraph.leftmostDescent_applyAdjacentSwap_belowDescent
#assert_no_axioms FX1Poly.Polygraph.crossingInsertionStep_extend
#assert_no_axioms FX1Poly.Polygraph.crossingInsertionStep_extend_general_smoke

-- WP-BRAUER r7: the COMMUTE mode local Coxeter step (general, IH-free).
#assert_no_axioms FX1Poly.Polygraph.crossingInsertionStep_commute_localReduction
#assert_no_axioms FX1Poly.Polygraph.crossingInsertionStep_commute_localReduction_smoke

-- WP-BRAUER r8: the BRAID mode local Coxeter step (Regime B, general, IH-free).
#assert_no_axioms FX1Poly.Polygraph.crossingInsertionStep_braid_localReduction
#assert_no_axioms FX1Poly.Polygraph.crossingInsertionStep_braid_localReduction_smoke

-- WP-BRAUER r8: the distant-swap kit (disjoint-swap commutation + leftmost-descent invariance) and the COMMUTE mode
-- FULL reduction (conditional on the smaller-perm insertion step).  Private helpers covered transitively.
#assert_no_axioms FX1Poly.Polygraph.applyAdjacentSwap_swap_disjoint
#assert_no_axioms FX1Poly.Polygraph.leftmostDescent_applyAdjacentSwap_distant
#assert_no_axioms FX1Poly.Polygraph.crossingInsertionStep_commute_full
#assert_no_axioms FX1Poly.Polygraph.crossingInsertionStep_commute_full_smoke

-- honesty markers
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCanonicalCrossingWordLayer
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCrossingWordProblemConditionalReduction
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasInsertionCancelMode
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasInRangeInsertionReformulation
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasInsertionExtendMode
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasInsertionCommuteLocalMove
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasInsertionBraidLocalMove
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasDistantSwapKit
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasInsertionCommuteFullMode
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCrossingInsertionStepGeneralResidual

end FX1PolyAudit
