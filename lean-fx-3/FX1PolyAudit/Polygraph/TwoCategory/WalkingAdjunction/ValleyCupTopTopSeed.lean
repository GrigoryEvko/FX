import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyCupTopTopSeed

/-! # FX1PolyAudit/…/ValleyCupTopTopSeed — zero-axiom gate

Per-declaration zero-axiom gate for the CLOSING of the top-top cup-arc partner (Piece II tail, cup case 3):
the pure-cap top-port-below-floor seed fact and the assembled `cupTopTopPartner`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.pureCapTopPartnerBelow
#assert_no_axioms FX1Poly.Polygraph.cupTopTopPartner
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasCupTopTopPartnerClosed

end FX1PolyAudit
