import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.Modularity

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.Modularity — zero-axiom gate for the modularity theorem
(WP-AMALG-2 r1, B2)

Per-declaration zero-axiom gate: the general modularity biconditional (pushout saturated convertibility over an
empty-crossing-law relation ↔ free `TwoCellConvFull`), the concrete instance at `involution +_M monad`, the
non-vacuous blockwise soundness lift, and the cross-block Godement commutation leg.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

-- the modularity biconditional (general + concrete)
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutConvIffFree_ofEmptyComponents
#assert_no_axioms FX1Poly.Polygraph.Amalgam.involutionMonadPushoutConvIffFree

-- the soundness leg (a real component conv lifts) + the cross-block commutation leg
#assert_no_axioms FX1Poly.Polygraph.Amalgam.modularityRightBlockLift
#assert_no_axioms FX1Poly.Polygraph.Amalgam.modularityCrossBlockCommute

-- honesty marker
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasModularityDisjointScope

end FX1PolyAudit
