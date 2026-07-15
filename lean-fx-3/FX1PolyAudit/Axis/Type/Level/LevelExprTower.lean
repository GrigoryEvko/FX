import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Type.Level.LevelExprTower

/-! # FX1PolyAudit.Axis.Type.Level.LevelExprTower — zero-axiom gate (ℕ ↪ LevelExpr tower)

Per-declaration zero-axiom gate for the relocated standalone level-tower family: the n-fold-`lsucc`
`universeLevelOfNat` and its ℕ-injectivity. Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Universe.universeLevelOfNat
#assert_no_axioms FX1Poly.Universe.universeLevelOfNat_injective

end FX1PolyAudit
