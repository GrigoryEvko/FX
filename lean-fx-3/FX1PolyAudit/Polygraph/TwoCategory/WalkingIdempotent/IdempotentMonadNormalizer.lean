import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingIdempotent.IdempotentMonadNormalizer

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingIdempotent.IdempotentMonadNormalizer — zero-axiom gate (fold/grow ladder)

Per-declaration zero-axiom gate for the walking-idempotent-monad general-`n` fold/grow ladder: the grow tower and
the through-`t` canonical cell, the fold-then-grow round-trip (`foldThenGrow`, the `n`-fold iterate of the shipped
mu-iso base), its dual grow-then-fold (`growThenFold`, via the left-unit law), the tower smokes, and the honesty
marker.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`, and any
well-founded recursion (the tower induction is STRUCTURAL on the `Nat` power). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.growTower
#assert_no_axioms FX1Poly.Polygraph.canonThroughT
#assert_no_axioms FX1Poly.Polygraph.growTower_zero
#assert_no_axioms FX1Poly.Polygraph.growTower_one_unfold
#assert_no_axioms FX1Poly.Polygraph.foldThenGrow
#assert_no_axioms FX1Poly.Polygraph.growThenFold
#assert_no_axioms FX1Poly.Polygraph.fxIdempotentMonad_hasFoldGrowLadder

end FX1PolyAudit
