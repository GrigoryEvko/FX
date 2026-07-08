import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyStraightenSeedB

/-! # FX1PolyAudit/…/SpineValleyStraightenSeedB — zero-axiom gate

Per-declaration zero-axiom gate for the STRAIGHTEN seed specialization (handedness B): the pinned atoms
(`pinnedCupAtomB` / `pinnedCapAtomB`), the band↔merged-frame identities (`pinnedCupBandB_eq_merged` /
`pinnedCapBandB_eq_merged`), the pinned-pair collapse (`pinnedZigZagBandCollapseB`), and the generic handedness-B
band collapse (`zigZagBandCollapseB`).  Every declaration must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.pinnedCupAtomB
#assert_no_axioms FX1Poly.Polygraph.pinnedCupBandB_eq_merged
#assert_no_axioms FX1Poly.Polygraph.pinnedCapAtomB
#assert_no_axioms FX1Poly.Polygraph.pinnedCapBandB_eq_merged
#assert_no_axioms FX1Poly.Polygraph.pinnedZigZagBandCollapseB
#assert_no_axioms FX1Poly.Polygraph.zigZagBandCollapseB
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSpineValleyStraightenSeedB

end FX1PolyAudit
