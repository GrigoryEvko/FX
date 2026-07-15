import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Type.Level.LevelDecision

/-! # FX1PolyAudit/Axis/Type/Level/LevelDecision — WP-LEVEL audit shard

Per-declaration zero-axiom gate for the WP-LEVEL capstone: the impredicative-boundary
arithmetic + congruences, the unified fragment dispatcher and its Boolean verdict, the
non-vacuity smokes, the fragment ledger, the two rung markers, and the capstone certificate.
Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## Impredicative-boundary arithmetic + congruences -/

#assert_no_axioms FX1Poly.Universe.LevelExpr.levelMax_succ_right_ne_zero
#assert_no_axioms FX1Poly.Universe.LevelExpr.levelMax_imax_lmax_distrib_arith
#assert_no_axioms FX1Poly.Universe.LevelExpr.levelMax_imax_assoc_arith
#assert_no_axioms FX1Poly.Universe.LevelExpr.limax_lmax_distrib_denoteEquiv
#assert_no_axioms FX1Poly.Universe.LevelExpr.limax_assoc_denoteEquiv

/-! ## The unified dispatcher + Boolean verdict -/

#assert_no_axioms FX1Poly.Universe.LevelExpr.inDecidableFragment
#assert_no_axioms FX1Poly.Universe.LevelExpr.closedConjunct_of_fragment
#assert_no_axioms FX1Poly.Universe.LevelExpr.decideDenoteEquivDispatch
#assert_no_axioms FX1Poly.Universe.LevelExpr.dispatchVerdict

/-! ## Non-vacuity smokes -/

#assert_no_axioms FX1Poly.Universe.LevelExpr.smoke_dispatch_predicativeEqual_true
#assert_no_axioms FX1Poly.Universe.LevelExpr.smoke_dispatch_predicativeDistinct_false
#assert_no_axioms FX1Poly.Universe.LevelExpr.smoke_dispatch_closedImaxCollapse_true
#assert_no_axioms FX1Poly.Universe.LevelExpr.smoke_dispatch_closedImaxDistinct_false
#assert_no_axioms FX1Poly.Universe.LevelExpr.smoke_dispatch_distributionInstance_true

/-! ## The fragment ledger + markers + capstone certificate -/

#assert_no_axioms FX1Poly.Universe.levelFragmentDecision
#assert_no_axioms FX1Poly.Universe.fxLevel_hasDecidableLevelAlgebraOnDecidedFragments
#assert_no_axioms FX1Poly.Universe.fxLevel_hasFullDecidableLevelAlgebra
#assert_no_axioms FX1Poly.Universe.levelDecision_certificate

end FX1PolyAudit
