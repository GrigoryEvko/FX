import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupStepDropCore

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupStepDropCore — zero-axiom gate

Per-declaration zero-axiom gate for the top-of-stack cup-drop core: the fresh cup component's single root, the
fresh-leg-versus-old-port disjointness, and the two trivial cup/cap count legs.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stepCupArc_freshComponentRoot
#assert_no_axioms FX1Poly.Polygraph.stepCupArc_freshLeg_ne_oldRoot
#assert_no_axioms FX1Poly.Polygraph.cupCount_stepCupArc_succ
#assert_no_axioms FX1Poly.Polygraph.capCount_stepCupArc_eq
#assert_no_axioms FX1Poly.Polygraph.partnerIndexOf_stepCupArc_old

end FX1PolyAudit
