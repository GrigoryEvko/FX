import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupTailsCancelCounts

/-! # FX1PolyAudit/…/ArcCupTailsCancelCounts — zero-axiom gate

Per-declaration zero-axiom gate for the cup tails-cancel's total count legs: for a cup head, the
whole-spine arc equality plus the located bubble's trace equivalence force the tail and remainder to
agree on the total cup and cap counts.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCupTailsCancel_countLegs_ofCupHead
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupTailsCancelCounts

end FX1PolyAudit
