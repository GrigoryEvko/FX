import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcCapHeadTransport

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringArcCapHeadTransport — zero-axiom gate
(FC-3 r20, THE CLONE CAMPAIGN — Branch B)

Per-declaration zero-axiom gate for the cap-head pin transport ported to the adjoint-triple seed.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringArcPairCapWindow_ofCapHeadExtractEq
#assert_no_axioms FX1Poly.Polygraph.fxString_hasArcCapHeadPinTransport

end FX1PolyAudit
