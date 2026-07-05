import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupTransportReadoff

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupTransportReadoff — zero-axiom gate

Per-declaration zero-axiom gate for the pointwise transport read-off: the partner
transport and the two internal-count transports read off the composite equality at every
in-range composite index.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCupHeadFolded_partnerTransport_pointwise
#assert_no_axioms FX1Poly.Polygraph.arcCupHeadFolded_cupCountTransport_pointwise
#assert_no_axioms FX1Poly.Polygraph.arcCupHeadFolded_capCountTransport_pointwise
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupTransportReadoff

end FX1PolyAudit
