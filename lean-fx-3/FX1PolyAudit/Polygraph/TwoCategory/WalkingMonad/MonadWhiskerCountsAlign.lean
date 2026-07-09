import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadWhiskerCountsAlign

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingMonad.MonadWhiskerCountsAlign — zero-axiom gate (whisker counts-alignment)

Per-declaration zero-axiom gate for the counts-alignment feeding the two whisker `normalizeCell` cases: the
`countsOf` shift-invariance / ascending-prefix peel / cons-append split, the two ordinal-sum-embedding counts lifts,
and the two `canonCounts_whisker*` corollaries.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.runLengthAt_shiftPrepend
#assert_no_axioms FX1Poly.Polygraph.dropRunAt_shiftPrepend
#assert_no_axioms FX1Poly.Polygraph.countsOf_shiftPrepend
#assert_no_axioms FX1Poly.Polygraph.dropRunAt_of_runLengthAt_zero
#assert_no_axioms FX1Poly.Polygraph.runLengthAt_ascendingPrepend_zero
#assert_no_axioms FX1Poly.Polygraph.countsOf_ascendingPrepend
#assert_no_axioms FX1Poly.Polygraph.countsOf_embedLocalMap_left
#assert_no_axioms FX1Poly.Polygraph.runLengthAt_zero_of_lowerBound
#assert_no_axioms FX1Poly.Polygraph.runLengthAt_consAppend
#assert_no_axioms FX1Poly.Polygraph.dropRunAt_consAppend
#assert_no_axioms FX1Poly.Polygraph.countsOf_consAppend_split
#assert_no_axioms FX1Poly.Polygraph.shiftPrepend_zero
#assert_no_axioms FX1Poly.Polygraph.countsOf_embedLocalMap_right
#assert_no_axioms FX1Poly.Polygraph.canonCounts_whiskerLeft
#assert_no_axioms FX1Poly.Polygraph.canonCounts_whiskerRight
#assert_no_axioms FX1Poly.Polygraph.fxMonad_hasWhiskerCountsAlignment

end FX1PolyAudit
