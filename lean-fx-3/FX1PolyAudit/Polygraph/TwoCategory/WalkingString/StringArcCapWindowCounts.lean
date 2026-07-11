import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcCapWindowCounts

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringArcCapWindowCounts — zero-axiom gate
(FC-3 r20, THE CLONE CAMPAIGN — floor)

Per-declaration zero-axiom gate for the consumed strand's event counts ported to the adjoint-triple seed.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringArcCapHeadFolded_windowStrandCapCount
#assert_no_axioms FX1Poly.Polygraph.stringArcCapHeadFolded_windowStrandCupCount
#assert_no_axioms FX1Poly.Polygraph.stringArcCapHeadFolded_windowRightRootEq
#assert_no_axioms FX1Poly.Polygraph.fxString_hasArcCapWindowCounts

end FX1PolyAudit
