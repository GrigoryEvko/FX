import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcHalfTouchKill

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcHalfTouchKill — zero-axiom gate

Per-declaration zero-axiom gate for the half-touch kill: the contradiction (survival dies on
the singleton-component collapse, a second touch dies on two fresh-distinct events in one
pinned root) and the window read-off (the located toucher's reads are exactly the pair).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcHalfTouchContradiction
#assert_no_axioms FX1Poly.Polygraph.arcTouchWindowReadsArePair
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcTouchWindowPinning

end FX1PolyAudit
