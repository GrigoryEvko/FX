import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingPartnerInvolution

/-! # FX1PolyAudit/…/MatchingPartnerInvolution — zero-axiom gate

Per-declaration zero-axiom gate for the `matchingOf` partner-INVOLUTION (Piece II tail): the boundary
matching is a fixed-point-free involution on the arc structure's `.diagram` and, transported across the
diagram = matching bridge, on the plain `matchingOf` carrier.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcDiagram_partner_isInvolution
#assert_no_axioms FX1Poly.Polygraph.matchingOf_partner_isInvolution
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingPartnerInvolution

end FX1PolyAudit
