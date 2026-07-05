import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupPartnerDispatch

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupPartnerDispatch — zero-axiom gate

Per-declaration zero-axiom gate for the per-index cup partner dispatch (peel campaign H,
cup rung 4 close): the transported partner value function and the dispatch master equating
the composite partner to it at every in-range index.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCupPartnerTransport
#assert_no_axioms FX1Poly.Polygraph.arcCupHeadFolded_partnerDispatch

end FX1PolyAudit
