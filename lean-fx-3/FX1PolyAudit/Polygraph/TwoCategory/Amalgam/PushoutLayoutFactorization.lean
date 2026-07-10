import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutLayoutFactorization

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutLayoutFactorization — zero-axiom gate for the factorization
motive, the `id` case, and the wall-splitting positive counterpoint (WP-AMALG-2 r8, B1)

Per-declaration zero-axiom gate for the `PushoutLayoutFactorization` motive, the `id` case, the `eta`-gap block and
the wall-splitting factorization, and the honesty marker.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.PushoutLayoutFactorization
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutFactorizeId
#assert_no_axioms FX1Poly.Polygraph.Amalgam.unitSplitsWallPair
#assert_no_axioms FX1Poly.Polygraph.Amalgam.unitSplitsWallFactorization
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasLayoutFactorizationMotive

end FX1PolyAudit
