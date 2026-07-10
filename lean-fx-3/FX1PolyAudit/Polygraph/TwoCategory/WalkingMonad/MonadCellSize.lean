import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadCellSize

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingMonad.MonadCellSize — zero-axiom gate (the conv-FREE size floor)

Per-declaration zero-axiom gate for the structural-size floor lemma `one_le_cellSize`, relocated into the conv-FREE
`MonadCellSize` leaf so the native decider file can consume it off the pure-bespoke Δ chain.  Must be free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.one_le_cellSize

end FX1PolyAudit
