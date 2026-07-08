import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyStraightenSeed

/-! # FX1PolyAudit/…/SpineValleyStraightenSeed — zero-axiom gate

Per-declaration zero-axiom gate for Piece I STRAIGHTEN producer (i, handedness A) — the seed specialization: the
two pinned atoms (`pinnedCupAtom` / `pinnedCapAtom`), the band ↔ merged-frame identities (`pinnedCupBand_eq_merged`
/ `pinnedCapBand_eq_merged`), the pinned-pair collapse `pinnedZigZagBandCollapse`, and the generic handedness-A
closer `zigZagBandCollapseA`.  Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.pinnedCupAtom
#assert_no_axioms FX1Poly.Polygraph.pinnedCupBand_eq_merged
#assert_no_axioms FX1Poly.Polygraph.pinnedCapAtom
#assert_no_axioms FX1Poly.Polygraph.pinnedCapBand_eq_merged
#assert_no_axioms FX1Poly.Polygraph.pinnedZigZagBandCollapse
#assert_no_axioms FX1Poly.Polygraph.zigZagBandCollapseA
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSpineValleyStraightenSeed

end FX1PolyAudit
