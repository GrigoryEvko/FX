import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcCapWindowPartners

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringArcCapWindowPartners — zero-axiom gate
(FC-3 r20, THE CLONE CAMPAIGN — Branch A)

Per-declaration zero-axiom gate for the consumed window pair partnering each other, ported to the adjoint-triple seed.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringArcCapHeadFolded_windowLeftPartner
#assert_no_axioms FX1Poly.Polygraph.stringArcCapHeadFolded_windowRightPartner
#assert_no_axioms FX1Poly.Polygraph.fxString_hasArcCapWindowPartners

end FX1PolyAudit
