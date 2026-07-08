import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingStepCupOldPartner

/-! # FX1PolyAudit/…/MatchingStepCupOldPartner — zero-axiom gate

Per-declaration zero-axiom gate for the plain-carrier top-of-stack cup old-port census (Track B
route 1, brick 3 core): a top-of-stack cup on the plain `stepCup` carrier roots its fresh 2-node
component to `nextFresh + 1`, leaves every old node's root unchanged, and shifts every old port's
`partnerIndexOf` by `freshShiftAbove (seedBoundary + windowPosition) 2` — positivity-free (no
`0 < bottomCount`).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stepCup_freshComponentRoot
#assert_no_axioms FX1Poly.Polygraph.unionFindRootOf_stepCup_old
#assert_no_axioms FX1Poly.Polygraph.partnerIndexOf_stepCup_old

end FX1PolyAudit
