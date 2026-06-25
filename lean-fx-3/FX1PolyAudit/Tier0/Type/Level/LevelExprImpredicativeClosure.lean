import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Type.Level.LevelExprImpredicativeClosure

/-! # FX1PolyAudit.Tier0.Type.Level.LevelExprImpredicativeClosure

Zero-axiom audit shard mirroring kernel module `FX1Poly.Tier0.Type.Level.LevelExprImpredicativeClosure`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Universe.bothBoolTrue

#assert_no_axioms FX1Poly.Universe.LevelExpr.isClosed

#assert_no_axioms FX1Poly.Universe.LevelExpr.denote_closed_env_independent

#assert_no_axioms FX1Poly.Universe.LevelExpr.denoteEquiv_closed_iff

#assert_no_axioms FX1Poly.Universe.LevelExpr.decidableDenoteEquivClosed

#assert_no_axioms FX1Poly.Universe.LevelExpr.limax_denoteEquiv_lmax_of_codomainPos

#assert_no_axioms FX1Poly.Universe.LevelExpr.limax_denoteEquiv_lzero_of_codomainZero

end FX1PolyAudit
