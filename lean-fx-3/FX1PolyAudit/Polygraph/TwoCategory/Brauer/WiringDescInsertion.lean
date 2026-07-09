import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescInsertion

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescInsertion — zero-axiom gate (WP-BRAUER-4 r5)

Per-declaration zero-axiom gate for the crossing-only word-problem layer landed in round 5: the canonical reduced
word (`canonicalCrossingWord` = reverse of the `inversionCount`-fuelled bubble word), the homomorphism helpers, the
identity base, the peel-last outer fold CONDITIONAL on the general insertion step
(`crossingOnly_straightens_ofInsertionStep` / `crossingWords_equalPerm_conv_ofInsertionStep`), and the non-vacuity
witnesses (canonical-is-a-reduced-word smokes + the three insertion-step modes + the two direct word-problem pairs).
The private propext-free arithmetic / list helpers are covered transitively.

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

-- honesty markers
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCanonicalCrossingWordLayer
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCrossingWordProblemConditionalReduction
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasInsertionCancelMode
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCrossingInsertionStepGeneralResidual

end FX1PolyAudit
