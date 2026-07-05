import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupExists

/-! # FX1PolyAudit/…/ArcCupExists — zero-axiom gate

Per-declaration zero-axiom gate for the cup-existence half of the cup locator: a positive cup
total locates a cup atom in a walking-adjunction spine (the structural cap-peeling recursion).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcSpine_cupSplit_of_cupEventGrowth
#assert_no_axioms FX1Poly.Polygraph.arcSpine_hasCup_of_cupCount_pos
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupExists

end FX1PolyAudit
