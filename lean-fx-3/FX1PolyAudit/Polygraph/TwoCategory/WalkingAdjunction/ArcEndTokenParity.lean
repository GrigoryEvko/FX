import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcEndTokenParity

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcEndTokenParity — zero-axiom gate

Per-declaration zero-axiom gate for the opposite-class strand-endpoint invariant's
statement layer: the token class function, the pairwise opposite-class invariant, and its
truth at the fresh seed state.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcEndTokenClass
#assert_no_axioms FX1Poly.Polygraph.ArcEndTokenParity
#assert_no_axioms FX1Poly.Polygraph.arcEndTokenParity_initial
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcEndTokenParitySeed

end FX1PolyAudit
