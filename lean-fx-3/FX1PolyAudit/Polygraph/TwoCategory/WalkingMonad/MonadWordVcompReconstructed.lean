import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadWordVcompReconstructed

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingMonad.MonadWordVcompReconstructed — zero-axiom gate
(WP-AMALG-2 r14, Brick B1: the vertical word multiplicativity RESEATED onto the reconstructed pushout signature)

Per-declaration zero-axiom gate for Finding-C's cross-lane reseat — `reconWordFromCounts` (the inverse-reseat image
of the canonical word) and `wordMul_vcompReconstructed` (the reconstructed-signature vertical word
multiplicativity), plus the two r8-shaped truth probes and the establishment marker. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconWordFromCounts
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconWordFromCounts_eq
#assert_no_axioms FX1Poly.Polygraph.Amalgam.wordMul_vcompReconstructed
#assert_no_axioms FX1Poly.Polygraph.Amalgam.wordMul_vcompReconstructed_smoke_merge
#assert_no_axioms FX1Poly.Polygraph.Amalgam.wordMul_vcompReconstructed_smoke_mixed
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasReconstructedWordVcompReseat

end FX1PolyAudit
