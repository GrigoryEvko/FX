import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingIdempotent.IdempotentMonadGeneralNormalizer

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingIdempotent.IdempotentMonadGeneralNormalizer — zero-axiom gate

Per-declaration zero-axiom gate for the walking-idempotent-monad general normalizer bricks: the boundary-cast
helpers, the general-width left-whisker canonicalisation (`whiskerLeftCanon`), the right-whisker bricks, the
boundary-determined representative, and the assembled normalization.  Must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega`, and any well-founded recursion (all inductions STRUCTURAL). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.IdempotentMonadSaturatedTwoCellConv.castBoundaryCongr
#assert_no_axioms FX1Poly.Polygraph.monadTPower_add_left
#assert_no_axioms FX1Poly.Polygraph.monadTPower_succ_add_left
#assert_no_axioms FX1Poly.Polygraph.whiskerLeftCanon

end FX1PolyAudit
