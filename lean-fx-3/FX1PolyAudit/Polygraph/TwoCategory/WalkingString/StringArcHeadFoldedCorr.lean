import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcHeadFoldedCorr

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringArcHeadFoldedCorr — zero-axiom gate
(FC-3 r20, THE CLONE CAMPAIGN — floor)

Per-declaration zero-axiom gate for the folded component correspondences ported to the adjoint-triple seed.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringArcComponentShiftCorr_cupHeadFolded
#assert_no_axioms FX1Poly.Polygraph.stringArcComponentShiftCorr_capHeadFolded
#assert_no_axioms FX1Poly.Polygraph.fxString_hasArcHeadFoldedCorr

end FX1PolyAudit
