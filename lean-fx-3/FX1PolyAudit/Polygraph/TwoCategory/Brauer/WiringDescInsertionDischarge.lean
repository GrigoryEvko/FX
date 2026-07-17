import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescInsertionDischarge

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescInsertionDischarge — zero-axiom gate (WP-BRAUER r13)

Per-declaration zero-axiom gate for the `InRangeInsertionStep` discharge: the range certificate, the Lehmer
realization + swap equivariance, the permutation-equality brick, the discharge itself, the
`BraidAscentInsertionStep` corollary, the unconditional r7 folds, and the smokes.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Private helpers
(the local Bool/Nat/list kit, `isBelowAllEntries`, `onePlusEach`, the range decompositions) covered
transitively. -/

namespace FX1PolyAudit

-- Brick (b): the range certificate — descent bound, bubble-word bound, the canonical-word certificate.
#assert_no_axioms FX1Poly.Polygraph.leftmostDescent_blt_predLength
#assert_no_axioms FX1Poly.Polygraph.bubbleWordFueled_mentionsOnlyBelow
#assert_no_axioms FX1Poly.Polygraph.canonicalCrossingWord_mentionsOnlyBelow

-- The Lehmer standardization + swap equivariance.
#assert_no_axioms FX1Poly.Polygraph.lehmerRankAgainst
#assert_no_axioms FX1Poly.Polygraph.lehmerStandardize
#assert_no_axioms FX1Poly.Polygraph.lehmerStandardize_applyAdjacentSwap

-- The identity base — strictly-ascending lists standardize to `List.range`.
#assert_no_axioms FX1Poly.Polygraph.lehmerStandardize_ofIdentityDistinct

-- Brick (a): the realization — fueled + un-fueled.
#assert_no_axioms FX1Poly.Polygraph.canonicalCrossingWord_realizesFueled
#assert_no_axioms FX1Poly.Polygraph.canonicalCrossingWord_realizes_lehmerStandardize

-- The permutation-equality brick + THE DISCHARGE.
#assert_no_axioms FX1Poly.Polygraph.canonicalInsertion_permEq
#assert_no_axioms FX1Poly.Polygraph.inRangeInsertionStep_holds

-- Corollaries: the braid-ascent leaf Prop inhabited + the unconditional r7 folds.
#assert_no_axioms FX1Poly.Polygraph.braidAscentInsertionStep_holds
#assert_no_axioms FX1Poly.Polygraph.crossingOnly_straightens_unconditional
#assert_no_axioms FX1Poly.Polygraph.crossingWords_equalPerm_conv_wellFormed_unconditional

-- Non-vacuity smokes.
#assert_no_axioms FX1Poly.Polygraph.canonicalRealization_smoke_residualLeaf
#assert_no_axioms FX1Poly.Polygraph.canonicalRealization_smoke_nonRangeAscending
#assert_no_axioms FX1Poly.Polygraph.inRangeInsertionStep_smoke_residualLeaf
#assert_no_axioms FX1Poly.Polygraph.inRangeInsertionStep_smoke_stuckPair
#assert_no_axioms FX1Poly.Polygraph.inRangeInsertionStep_smoke_braidPair
#assert_no_axioms FX1Poly.Polygraph.canonicalCrossingWord_mentionsOnlyBelow_smoke

-- Honesty marker.
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasInRangeInsertionStepDischarged

end FX1PolyAudit
