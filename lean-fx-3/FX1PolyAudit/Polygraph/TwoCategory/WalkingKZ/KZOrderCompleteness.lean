import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingKZ.KZOrderCompleteness

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingKZ.KZOrderCompleteness — zero-axiom gate (the KZ covering move)

Per-declaration zero-axiom gate for the walking-KZ LOCAL covering move: the KZ boundary-cast / horizontal-composite
congruences, the fold-invisibility of casts, the merge-collapse `List Nat` identities, the flat covering carrier,
the base / right-context / atomic covering moves, the local 2-block covering `kzLocalCovering`, the strict / merged
non-vacuity smokes, and the honesty markers.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.KZTwoCellLE.castBoundaryCongr
#assert_no_axioms FX1Poly.Polygraph.monadMonotoneMapOf_castBoundary
#assert_no_axioms FX1Poly.Polygraph.KZTwoCellLE.hcompCongrRight
#assert_no_axioms FX1Poly.Polygraph.KZTwoCellLE.hcompCongrLeft
#assert_no_axioms FX1Poly.Polygraph.composeMap_consReplicate
#assert_no_axioms FX1Poly.Polygraph.consReplicate_add
#assert_no_axioms FX1Poly.Polygraph.mergeCollapse_srcCounts
#assert_no_axioms FX1Poly.Polygraph.mergeCollapse_tgtCounts
#assert_no_axioms FX1Poly.Polygraph.kzBaseCovering
#assert_no_axioms FX1Poly.Polygraph.kzCoveringRightContext
#assert_no_axioms FX1Poly.Polygraph.kzAtomicCovering
#assert_no_axioms FX1Poly.Polygraph.kzAtomicCoveringLiteral
#assert_no_axioms FX1Poly.Polygraph.kzFlatWord
#assert_no_axioms FX1Poly.Polygraph.kzFlatWord_map
#assert_no_axioms FX1Poly.Polygraph.kzLE_ofFlatMapEq
#assert_no_axioms FX1Poly.Polygraph.kzLocalCovering
#assert_no_axioms FX1Poly.Polygraph.kzAtomicCoveringSuffix
#assert_no_axioms FX1Poly.Polygraph.reconstructFrom_ones_get
#assert_no_axioms FX1Poly.Polygraph.composeMap_reconstructFrom_relabel
#assert_no_axioms FX1Poly.Polygraph.listSum_consReplicate_ones
#assert_no_axioms FX1Poly.Polygraph.kzMergeSuffix_listSum
#assert_no_axioms FX1Poly.Polygraph.kzMergeSuffix_length
#assert_no_axioms FX1Poly.Polygraph.mergemapSuffix_get_ge
#assert_no_axioms FX1Poly.Polygraph.mergeCollapseSuffix_src
#assert_no_axioms FX1Poly.Polygraph.mergeCollapseSuffix_tgt
#assert_no_axioms FX1Poly.Polygraph.kzFrontCovering
#assert_no_axioms FX1Poly.Polygraph.kzFlatWord_cons
#assert_no_axioms FX1Poly.Polygraph.kzPrefixAdd
#assert_no_axioms FX1Poly.Polygraph.kzBaseCovering_isStrict
#assert_no_axioms FX1Poly.Polygraph.kzLocalCovering_merged_smoke
#assert_no_axioms FX1Poly.Polygraph.kzFrontCovering_suffix_smoke
#assert_no_axioms FX1Poly.Polygraph.kzPrefixAdd_smoke
#assert_no_axioms FX1Poly.Polygraph.fxKZ_hasWalkingKZLocalCovering
#assert_no_axioms FX1Poly.Polygraph.fxKZ_hasWalkingKZContextualCoveringAndStrip
-- The completeness CHAIN (GAP-2) — the prefix-sum majorization bridge, the head-peel recursion, the bridge.
#assert_no_axioms FX1Poly.Polygraph.natLeOfAddLeAddLeft
#assert_no_axioms FX1Poly.Polygraph.natAddSubCancelOfLe
#assert_no_axioms FX1Poly.Polygraph.reconstructFrom_get_ge_base
#assert_no_axioms FX1Poly.Polygraph.reconstructFrom_get_ge
#assert_no_axioms FX1Poly.Polygraph.reconstructFrom_ge_get
#assert_no_axioms FX1Poly.Polygraph.reconstructFrom_length_listSum
#assert_no_axioms FX1Poly.Polygraph.prefixSum_le_listSum
#assert_no_axioms FX1Poly.Polygraph.mapLE_imp_prefixDom
#assert_no_axioms FX1Poly.Polygraph.prefixSumDominates_strip
#assert_no_axioms FX1Poly.Polygraph.prefixSumDominates_covering
#assert_no_axioms FX1Poly.Polygraph.twoConsLength
#assert_no_axioms FX1Poly.Polygraph.listSum_twoCons
#assert_no_axioms FX1Poly.Polygraph.listSum_move
#assert_no_axioms FX1Poly.Polygraph.kzFrontCoveringMulti
#assert_no_axioms FX1Poly.Polygraph.kzFlatWord_totalCast
#assert_no_axioms FX1Poly.Polygraph.kzFlatWord_codCast
#assert_no_axioms FX1Poly.Polygraph.kzPrefixAddTotal
#assert_no_axioms FX1Poly.Polygraph.list_eq_nil_of_length_zero
#assert_no_axioms FX1Poly.Polygraph.kzChainByLength
#assert_no_axioms FX1Poly.Polygraph.kzChainMapLE
#assert_no_axioms FX1Poly.Polygraph.canonCounts_listSum
#assert_no_axioms FX1Poly.Polygraph.canonAsFlatCast
#assert_no_axioms FX1Poly.Polygraph.kzLE_complete
#assert_no_axioms FX1Poly.Polygraph.kzOrderCompletenessWitness
#assert_no_axioms FX1Poly.Polygraph.decideKZLETotal
#assert_no_axioms FX1Poly.Polygraph.kzOrderWordProblem
#assert_no_axioms FX1Poly.Polygraph.kzOrderComplete_yes
#assert_no_axioms FX1Poly.Polygraph.kzOrderComplete_no
#assert_no_axioms FX1Poly.Polygraph.fxKZ_hasWalkingKZOrderCompletenessChain

end FX1PolyAudit
