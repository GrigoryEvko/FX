import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupCountCancellation

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupCountCancellation — zero-axiom gate

Per-declaration zero-axiom gate for the unconditional count legs of the cup partial
cancel: equal composite extracts over the same peeled cup force equal fresh cup totals,
cap totals, and boundary widths.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCupHeadFolded_cupTotal_cancel
#assert_no_axioms FX1Poly.Polygraph.arcCupHeadFolded_capTotal_cancel
#assert_no_axioms FX1Poly.Polygraph.arcCupHeadFolded_topCount_cancel
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupCountCancellation

end FX1PolyAudit
