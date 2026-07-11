import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcEventCountTransport

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringArcEventCountTransport — zero-axiom gate
(FC-3 r20, THE CLONE CAMPAIGN — floor)

Per-declaration zero-axiom gate for the per-strand event-count transport ported to the adjoint-triple seed.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringArcCupHeadFolded_cupEventCountAtImage
#assert_no_axioms FX1Poly.Polygraph.stringArcCupHeadFolded_capEventCountAtImage
#assert_no_axioms FX1Poly.Polygraph.stringArcCapHeadFolded_cupEventCountAtImage
#assert_no_axioms FX1Poly.Polygraph.stringArcCapHeadFolded_capEventCountAtImage
#assert_no_axioms FX1Poly.Polygraph.fxString_hasArcEventCountTransport

end FX1PolyAudit
