import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapWindowScanFailure

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCapWindowScanFailure — zero-axiom gate

Per-declaration zero-axiom gate for the failing window scan tests (peel campaign H,
rung E-3, part 3a): the left and right window candidates' folded scan tests are false
against any reindexed-fresh-probe root, plus the packaged middle-fails hypothesis.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCapHeadFolded_windowLeftScanTestFails
#assert_no_axioms FX1Poly.Polygraph.arcCapHeadFolded_windowRightScanTestFails
#assert_no_axioms FX1Poly.Polygraph.arcCapHeadFolded_windowPairScanTestsFail

end FX1PolyAudit
