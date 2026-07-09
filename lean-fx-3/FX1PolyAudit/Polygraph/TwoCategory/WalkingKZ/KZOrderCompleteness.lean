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
#assert_no_axioms FX1Poly.Polygraph.kzBaseCovering_isStrict
#assert_no_axioms FX1Poly.Polygraph.kzLocalCovering_merged_smoke
#assert_no_axioms FX1Poly.Polygraph.fxKZ_hasWalkingKZLocalCovering
#assert_no_axioms FX1Poly.Polygraph.fxKZ_hasWalkingKZOrderCompletenessChain

end FX1PolyAudit
