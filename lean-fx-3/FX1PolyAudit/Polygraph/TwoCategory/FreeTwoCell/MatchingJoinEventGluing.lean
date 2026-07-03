import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingJoinEventGluing

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingJoinEventGluing — zero-axiom gate

Per-declaration zero-axiom gate for the cross-connected gluing engine (the private boolean
helper is covered transitively).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.componentView_applyJoinEvents_ofCrossConnected
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasComponentViewCrossConnectedGluing

end FX1PolyAudit
