import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingIdempotent.IdempotentMonadGeneralNormalizer

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingIdempotent.IdempotentMonadGeneralNormalizer — zero-axiom gate

Per-declaration zero-axiom gate for the walking-idempotent-monad general normalizer bricks: the boundary-cast
helpers, the general-width left-whisker canonicalisation (`whiskerLeftCanon`), the right-whisker bricks, the
boundary-determined representative, and the assembled normalization.  Must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega`, and any well-founded recursion (all inductions STRUCTURAL). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.IdempotentMonadSaturatedTwoCellConv.castBoundaryCongr
#assert_no_axioms FX1Poly.Polygraph.IdempotentMonadSaturatedTwoCellConv.ofCastLeft
#assert_no_axioms FX1Poly.Polygraph.IdempotentMonadSaturatedTwoCellConv.vcompCastLeftExtrude
#assert_no_axioms FX1Poly.Polygraph.monadTPower_add_left
#assert_no_axioms FX1Poly.Polygraph.monadTPower_succ_add_left
#assert_no_axioms FX1Poly.Polygraph.whiskerLeftCanon
#assert_no_axioms FX1Poly.Polygraph.composePath_monadTPower_monadT
#assert_no_axioms FX1Poly.Polygraph.gadgetSplitRight_zero
#assert_no_axioms FX1Poly.Polygraph.gadgetSplitRight_one
#assert_no_axioms FX1Poly.Polygraph.whiskerRightLeftBraid
#assert_no_axioms FX1Poly.Polygraph.gadgetSplitRight
#assert_no_axioms FX1Poly.Polygraph.whiskerLeftCanon_width_two_smoke
#assert_no_axioms FX1Poly.Polygraph.gadgetSplitRight_width_three_smoke
#assert_no_axioms FX1Poly.Polygraph.fxIdempotentMonad_hasGeneralWidthWhiskerLeftCanon
#assert_no_axioms FX1Poly.Polygraph.fxIdempotentMonad_hasGadgetSplitRight
#assert_no_axioms FX1Poly.Polygraph.fxIdempotentMonad_hasWhiskerRightCanon

end FX1PolyAudit
