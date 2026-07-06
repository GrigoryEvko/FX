import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupSingleInternalWindowReadoff

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupSingleInternalWindowReadoff — zero-axiom gate

Per-declaration zero-axiom gate for the R1 head-cup window read-off base case: a lone cup's `internalCupCounts`
reads `1` at its two leg ports and `0` below the window, so `internalCupCounts` PINS the single cup's window —
the universal R1 read-off restricted to the empty tail.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.singleCupInternalCupCount_atLeftLeg
#assert_no_axioms FX1Poly.Polygraph.singleCupInternalCupCount_belowWindow
#assert_no_axioms FX1Poly.Polygraph.singleCupWindowPinnedByInternalCupCounts
#assert_no_axioms FX1Poly.Polygraph.singleCupHeadWindowPinned

end FX1PolyAudit
