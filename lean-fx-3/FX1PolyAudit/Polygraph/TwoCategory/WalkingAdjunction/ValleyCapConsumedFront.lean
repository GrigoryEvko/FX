import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyCapConsumedFront

/-! # FX1PolyAudit/…/ValleyCapConsumedFront — zero-axiom gate

Per-declaration zero-axiom gate for the cap-consumed partner leg of the full `capRestrict` `DiagramType.ext`
(Piece II tail): the front-confinement duals and the cap-consumed partner agreement.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.partnerIndexOf_eq_frontScan_ofFrontNe
#assert_no_axioms FX1Poly.Polygraph.frontScan_ne_ofPartnerBelow
#assert_no_axioms FX1Poly.Polygraph.capConsumed_partner_agree
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasValleyCapConsumedFront

end FX1PolyAudit
