import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadNormalizeVcomp

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingMonad.MonadNormalizeVcomp — zero-axiom gate

Per-declaration zero-axiom gate for the DATA bridge `canonCounts_vcomp` (the Δ fibre-count functoriality
`countsOf ∘ composeMap = composeCounts ∘ countsOf`) and the assembled `vcomp` normalize case
`monadNormalize_vcomp`.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- the mid-domain reindex kit
#assert_no_axioms FX1Poly.Polygraph.mapSub
#assert_no_axioms FX1Poly.Polygraph.mapSub_length
#assert_no_axioms FX1Poly.Polygraph.monotoneMapGet_mapSub
#assert_no_axioms FX1Poly.Polygraph.mapSub_isWeaklyIncreasing
#assert_no_axioms FX1Poly.Polygraph.natAddSubOfGe
#assert_no_axioms FX1Poly.Polygraph.shiftPrepend_mapSub

-- the value-threshold split kit
#assert_no_axioms FX1Poly.Polygraph.splitLow
#assert_no_axioms FX1Poly.Polygraph.splitHigh
#assert_no_axioms FX1Poly.Polygraph.splitLow_cons_lt
#assert_no_axioms FX1Poly.Polygraph.splitLow_cons_ge
#assert_no_axioms FX1Poly.Polygraph.splitHigh_cons_lt
#assert_no_axioms FX1Poly.Polygraph.splitHigh_cons_ge
#assert_no_axioms FX1Poly.Polygraph.consAppend_splitLow_splitHigh
#assert_no_axioms FX1Poly.Polygraph.splitLow_lt
#assert_no_axioms FX1Poly.Polygraph.splitHigh_ge
#assert_no_axioms FX1Poly.Polygraph.splitHigh_mapsInto
#assert_no_axioms FX1Poly.Polygraph.monotoneMapGet_consAppend_left
#assert_no_axioms FX1Poly.Polygraph.isWeaklyIncreasing_consAppend_left
#assert_no_axioms FX1Poly.Polygraph.splitLow_isWeaklyIncreasing
#assert_no_axioms FX1Poly.Polygraph.splitHigh_isWeaklyIncreasing

-- composite-map run/drop pointwise facts
#assert_no_axioms FX1Poly.Polygraph.composeMap_consAppend
#assert_no_axioms FX1Poly.Polygraph.runLengthAt_le_length
#assert_no_axioms FX1Poly.Polygraph.dropRunAt_of_all_eq
#assert_no_axioms FX1Poly.Polygraph.monotoneMapGet_lt_runLengthAt
#assert_no_axioms FX1Poly.Polygraph.monotoneMapGet_dropRunAt_shift
#assert_no_axioms FX1Poly.Polygraph.monotoneMapGet_ge_runLengthAt_gt
#assert_no_axioms FX1Poly.Polygraph.composeMap_reindex_high
#assert_no_axioms FX1Poly.Polygraph.dropRunAt_composeMap_eq
#assert_no_axioms FX1Poly.Polygraph.runLengthAt_composeMap_eq_splitLow_length

-- counts-sum + shift + block-split helpers
#assert_no_axioms FX1Poly.Polygraph.listSum_countsOf
#assert_no_axioms FX1Poly.Polygraph.countsOf_mapSub_shift
#assert_no_axioms FX1Poly.Polygraph.consTake_countsOf_consAppend
#assert_no_axioms FX1Poly.Polygraph.consDrop_countsOf_consAppend

-- ★★ the functoriality bridge + canonCounts bridge
#assert_no_axioms FX1Poly.Polygraph.countsOf_composeMap
#assert_no_axioms FX1Poly.Polygraph.canonCounts_vcomp

-- the vcomp normalize case + the honesty flag
#assert_no_axioms FX1Poly.Polygraph.monadNormalize_vcomp
#assert_no_axioms FX1Poly.Polygraph.fxMonad_hasCanonCountsVcompBridge

end FX1PolyAudit
