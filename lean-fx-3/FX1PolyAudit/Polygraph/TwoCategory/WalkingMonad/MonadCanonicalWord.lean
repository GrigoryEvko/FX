import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadCanonicalWord

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingMonad.MonadCanonicalWord — zero-axiom gate (the EZ word-builder)

Per-declaration zero-axiom gate for the Eilenberg–Zilber word-builder: the canonical `t`-power boundary path, the
per-count merge gadget and its fold, the `consReplicate` cons-only difference-list primitives (replacing
`List.replicate _ _ ++ tail` so length/indexing stay `propext`-free), the reconstructed monotone map and its
indexing laws, the per-target canonical word, the ★★ section theorem `monadMonotoneMapOf (wordFromCounts counts)
= reconstructFrom 0 counts`, the non-vacuity + separation smokes, and the two honesty markers.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

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
