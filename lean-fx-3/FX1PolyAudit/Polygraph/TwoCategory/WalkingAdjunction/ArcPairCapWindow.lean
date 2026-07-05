import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPairCapWindow

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcPairCapWindow — zero-axiom gate

Per-declaration zero-axiom gate for the located consuming cap: the window certificate and
the read-off from the final partner/count pins over the canonical seed.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.ArcPairCapWindow
#assert_no_axioms FX1Poly.Polygraph.arcPairCapWindow_ofFinalPins
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcPairCapWindow

end FX1PolyAudit
