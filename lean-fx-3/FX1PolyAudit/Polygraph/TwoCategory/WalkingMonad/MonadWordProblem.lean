import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadWordProblem

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingMonad.MonadWordProblem — zero-axiom gate

Per-declaration zero-axiom gate for the full cell-level normalization `monadNormalize`, the inhabited
canonicalization `monadSaturatedCanonicalization`, the unconditional decision `monadSaturatedTwoCellDecision`, and
the non-vacuity witnesses.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.one_le_cellSize
#assert_no_axioms FX1Poly.Polygraph.monadNormalizeCellFueled
#assert_no_axioms FX1Poly.Polygraph.monadNormalize
#assert_no_axioms FX1Poly.Polygraph.monadSaturatedCanonicalization
#assert_no_axioms FX1Poly.Polygraph.monadSaturatedTwoCellDecision
#assert_no_axioms FX1Poly.Polygraph.monadDecision_yes_assoc
#assert_no_axioms FX1Poly.Polygraph.monadDecision_no_faces
#assert_no_axioms FX1Poly.Polygraph.fxMonad_hasSaturatedWordProblemClosed

end FX1PolyAudit
