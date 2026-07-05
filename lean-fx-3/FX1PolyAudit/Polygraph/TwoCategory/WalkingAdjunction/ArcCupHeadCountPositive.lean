import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupHeadCountPositive

/-! # FX1PolyAudit/…/ArcCupHeadCountPositive — zero-axiom gate

Per-declaration zero-axiom gate for the cup-headed positivity: the cup-event list never shrinks
through the fold, so a cup-headed walking-adjunction spine has a positive cup total.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.cupEventNodes_length_monotone
#assert_no_axioms FX1Poly.Polygraph.arcCupHead_cupCount_pos
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupHeadCountPositive

end FX1PolyAudit
