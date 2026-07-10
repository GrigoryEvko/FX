import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadSaturatedCanonReps

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingMonad.MonadSaturatedCanonReps — zero-axiom gate (canonical-word leaf)

Per-declaration zero-axiom gate for the bespoke-free CANONICAL-WORD representatives leaf: the eta/mu word builder,
fibre counts, and round-trip relocated VERBATIM from the pure-bespoke Δ chain so the survivor lane can reconstruct
canonical words conv-decoupled.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.monadTPower
#assert_no_axioms FX1Poly.Polygraph.monadTPower_zero_length
#assert_no_axioms FX1Poly.Polygraph.monadTPower_length
#assert_no_axioms FX1Poly.Polygraph.monadTPower_one
#assert_no_axioms FX1Poly.Polygraph.monadTPower_two
#assert_no_axioms FX1Poly.Polygraph.monadGadget
#assert_no_axioms FX1Poly.Polygraph.embedLocalMap_oneOneZero
#assert_no_axioms FX1Poly.Polygraph.shiftPrepend_one_replicateZero
#assert_no_axioms FX1Poly.Polygraph.composeMap_replicateOne_merge
#assert_no_axioms FX1Poly.Polygraph.composeMap_embed_merge
#assert_no_axioms FX1Poly.Polygraph.monadGadget_map
#assert_no_axioms FX1Poly.Polygraph.monadGadget_zero_map
#assert_no_axioms FX1Poly.Polygraph.monadGadget_one_map
#assert_no_axioms FX1Poly.Polygraph.monadGadget_two_map
#assert_no_axioms FX1Poly.Polygraph.monadGadget_three_map
#assert_no_axioms FX1Poly.Polygraph.countsDomainPath
#assert_no_axioms FX1Poly.Polygraph.wordFromCounts
#assert_no_axioms FX1Poly.Polygraph.consReplicate
#assert_no_axioms FX1Poly.Polygraph.consReplicate_length
#assert_no_axioms FX1Poly.Polygraph.monotoneMapGet_consReplicate_lt
#assert_no_axioms FX1Poly.Polygraph.monotoneMapGet_consReplicate_ge
#assert_no_axioms FX1Poly.Polygraph.replicate_length
#assert_no_axioms FX1Poly.Polygraph.reconstructFrom
#assert_no_axioms FX1Poly.Polygraph.reconstructFrom_length
#assert_no_axioms FX1Poly.Polygraph.monotoneMapGet_replicate
#assert_no_axioms FX1Poly.Polygraph.reconstructFrom_get_succ
#assert_no_axioms FX1Poly.Polygraph.monadMonotoneMapOf_wordFromCounts
#assert_no_axioms FX1Poly.Polygraph.wordFromCounts_id_two
#assert_no_axioms FX1Poly.Polygraph.wordFromCounts_merge_first
#assert_no_axioms FX1Poly.Polygraph.wordFromCounts_insert_first
#assert_no_axioms FX1Poly.Polygraph.wordFromCounts_merge_all
#assert_no_axioms FX1Poly.Polygraph.wordFromCounts_separates
#assert_no_axioms FX1Poly.Polygraph.fxMonad_hasEilenbergZilberWordBuilder
#assert_no_axioms FX1Poly.Polygraph.fxMonad_hasConvOfMapEqNormalization

end FX1PolyAudit
