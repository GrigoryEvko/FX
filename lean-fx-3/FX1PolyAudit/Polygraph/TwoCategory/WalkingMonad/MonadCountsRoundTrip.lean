import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadCountsRoundTrip

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingMonad.MonadCountsRoundTrip — zero-axiom gate (map→counts inversion)

Per-declaration zero-axiom gate for the map→counts inversion: the fold monotonicity invariant (the covariant fold
lands in a WEAKLY-INCREASING value-list), the run-peel `runLengthAt` / `dropRunAt` + `countsOf`, their unfold /
tail / suffix-invariant lemmas, the UNCONDITIONAL reconstruction step `consReplicate (runLengthAt) (dropRunAt) =
values`, the ★★ counts round-trip `reconstructFrom 0 (countsOf …) = values` + its whole-cell instance, the
non-vacuity smokes, and the honesty marker.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.monadRunMonoCell_isWeaklyIncreasing_gen
#assert_no_axioms FX1Poly.Polygraph.monadRunMonoCell_isWeaklyIncreasing
#assert_no_axioms FX1Poly.Polygraph.monadMonotoneMapOf_isWeaklyIncreasing
#assert_no_axioms FX1Poly.Polygraph.runLengthAt
#assert_no_axioms FX1Poly.Polygraph.dropRunAt
#assert_no_axioms FX1Poly.Polygraph.runLengthAt_cons_pos
#assert_no_axioms FX1Poly.Polygraph.runLengthAt_cons_neg
#assert_no_axioms FX1Poly.Polygraph.dropRunAt_cons_pos
#assert_no_axioms FX1Poly.Polygraph.dropRunAt_cons_neg
#assert_no_axioms FX1Poly.Polygraph.countsOf
#assert_no_axioms FX1Poly.Polygraph.isWeaklyIncreasing_tail
#assert_no_axioms FX1Poly.Polygraph.mapsInto_tail
#assert_no_axioms FX1Poly.Polygraph.lowerBound_tail
#assert_no_axioms FX1Poly.Polygraph.dropRunAt_isWeaklyIncreasing
#assert_no_axioms FX1Poly.Polygraph.dropRunAt_lowerBound
#assert_no_axioms FX1Poly.Polygraph.dropRunAt_mapsInto
#assert_no_axioms FX1Poly.Polygraph.consReplicate_runLengthAt_dropRunAt
#assert_no_axioms FX1Poly.Polygraph.reconstructFrom_countsOf
#assert_no_axioms FX1Poly.Polygraph.monadMonotoneMapOf_reconstructRoundTrip
#assert_no_axioms FX1Poly.Polygraph.countsOf_id_two
#assert_no_axioms FX1Poly.Polygraph.countsOf_merge
#assert_no_axioms FX1Poly.Polygraph.countsOf_merge_first
#assert_no_axioms FX1Poly.Polygraph.countsOf_insert_first
#assert_no_axioms FX1Poly.Polygraph.reconstructFrom_countsOf_smoke
#assert_no_axioms FX1Poly.Polygraph.fxMonad_hasCountsRoundTripInversion

end FX1PolyAudit
