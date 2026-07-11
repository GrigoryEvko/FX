import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadArcCensus

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingMonad.MonadArcCensus — zero-axiom gate

Per-declaration zero-axiom gate for the WP-MONAD arc census (the `rfl`-conjunction over the lane's completeness
markers plus the one honestly-`false` mode-side node).  Must be free of `propext`, `Quot.sound`, `Classical`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.wpMonadArcCensus_allClosed
#assert_no_axioms FX1Poly.Polygraph.fxMonad_wpMonadArcCensus

end FX1PolyAudit
