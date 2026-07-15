import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Type.Level.LevelExpr

/-! # FX1PolyAudit.Axis.Type.Level.LevelExpr

Zero-axiom audit shard mirroring kernel module `FX1Poly.Axis.Type.Level.LevelExpr`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Universe.LevelExpr

#assert_no_axioms FX1Poly.Universe.LevelExpr.lzero_canonical

#assert_no_axioms FX1Poly.Universe.LevelExpr.lsucc_lzero_canonical

#assert_no_axioms FX1Poly.Universe.LevelExpr.lmax_lzero_lzero_canonical

#assert_no_axioms FX1Poly.Universe.LevelExpr.limax_lzero_lzero_canonical

#assert_no_axioms FX1Poly.Universe.LevelExpr.lvar_zero_canonical

#assert_no_axioms FX1Poly.Universe.LevelExpr.decEq_refl_lzero

-- structural distinctness `e ≠ lsucc e` (no-Type-in-Type probe support):
-- size-free structural induction, the predicativity guard at the level algebra
#assert_no_axioms FX1Poly.Universe.LevelExpr.ne_lsucc_self

-- the double-successor guard `e ≠ lsucc (lsucc e)` (no-level-deflation support): same induction
#assert_no_axioms FX1Poly.Universe.LevelExpr.ne_lsuccLsucc_self

end FX1PolyAudit
