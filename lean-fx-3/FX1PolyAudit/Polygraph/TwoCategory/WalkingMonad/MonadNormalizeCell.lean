import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadNormalizeCell

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingMonad.MonadNormalizeCell — zero-axiom gate (boundary transport + canon + convOfMapEq reduction)

Per-declaration zero-axiom gate for the cell-level normalization scaffolding toward `convOfMapEq`: the
`countsOf` length law, the boundary transport `monadPath_normalForm` (every walking-monad 1-cell is a `t`-power —
the SECONDARY residual the honesty markers named), the canonical-word count list + its length, the two boundary
transport equalities, the boundary-transported canonical word `canon`, the soundness cross-check that `canon`
folds back to the cell's monotone map, the `canon` congruence (`canon` depends on a cell only through its map,
via proof-irrelevant boundary casts), and the machine-checked reduction of `convOfMapEq` to the cell-level
normalization `normalize : MonadNormalizesToCanon`, plus the honesty markers.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.countsOf_length
#assert_no_axioms FX1Poly.Polygraph.monadPath_normalForm_ofLength
#assert_no_axioms FX1Poly.Polygraph.monadPath_normalForm
#assert_no_axioms FX1Poly.Polygraph.canonCounts
#assert_no_axioms FX1Poly.Polygraph.canonCounts_length
#assert_no_axioms FX1Poly.Polygraph.canonCodomain_eq
#assert_no_axioms FX1Poly.Polygraph.canonDomain_eq
#assert_no_axioms FX1Poly.Polygraph.canon
#assert_no_axioms FX1Poly.Polygraph.monadMonotoneMapOf_canon
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.castBoundary_wordCongr
#assert_no_axioms FX1Poly.Polygraph.canonCounts_eqOfMapEq
#assert_no_axioms FX1Poly.Polygraph.canon_eqOfMapEq
#assert_no_axioms FX1Poly.Polygraph.monadConvOfMapEq_ofNormalize
#assert_no_axioms FX1Poly.Polygraph.fxMonad_hasBoundaryTransportAndCanon
#assert_no_axioms FX1Poly.Polygraph.fxMonad_hasConvOfMapEqReducedToNormalize
#assert_no_axioms FX1Poly.Polygraph.fxMonad_hasWordMulVcomp

end FX1PolyAudit
