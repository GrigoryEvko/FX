import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Type.Level.LevelExprComplexity

/-! # FX1PolyAudit.Tier0.Type.Level.LevelExprComplexity

Zero-axiom audit shard mirroring kernel module `FX1Poly.Tier0.Type.Level.LevelExprComplexity`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Universe.pow_one_eq_self

#assert_no_axioms FX1Poly.Universe.addSelf_le_mulSelf_add_two

#assert_no_axioms FX1Poly.Universe.mulSelf_add_self_add_self_le_doubleSquare

#assert_no_axioms FX1Poly.Universe.addSelf_add_addSelf_eq_four_mul

#assert_no_axioms FX1Poly.Universe.add_two_add_add_two_eq_add_four

#assert_no_axioms FX1Poly.Universe.LevelExpr.decideDenoteEquivSteps_isPolynomial

#assert_no_axioms FX1Poly.Universe.levelDenoteEquivDecisionComplexity

#assert_no_axioms FX1Poly.Universe.levelDenoteEquivDecisionComplexity_stepCount_smoke

#assert_no_axioms FX1Poly.Universe.levelDenoteEquivDecisionComplexity_stepCount_smoke_larger

end FX1PolyAudit
