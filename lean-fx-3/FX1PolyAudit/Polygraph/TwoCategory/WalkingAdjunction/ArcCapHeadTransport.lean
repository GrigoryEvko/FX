import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapHeadTransport

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCapHeadTransport — zero-axiom gate

Per-declaration zero-axiom gate for the cap-head pin transport: full-arc-structure equality
against the cap-headed reference locates the consuming cap in the second spine.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcPairCapWindow_ofCapHeadExtractEq
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCapHeadPinTransport

end FX1PolyAudit
