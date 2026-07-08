import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyStraightenCastBridge

/-! # FX1PolyAudit/…/SpineValleyStraightenCastBridge — zero-axiom gate

Per-declaration zero-axiom gate for THE CAST BRIDGE — the merged-`atomFrame` shared-leg frame collapse (handedness
A): the two merged frames (`mergedCupFrame` / `mergedCapFrame`), the two merged↔iterated-leg conversions
(`mergedCupFrame_convFull_castCupLeg` / `mergedCapFrame_convFull_castCapLeg`), the two `composePath`-associativity
alignment casts (`mergedFramesAlign` / `mergedFramesEndpoint`), and the collapse itself
(`mergedSharedLegFramesCollapse`).  Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.mergedCupFrame
#assert_no_axioms FX1Poly.Polygraph.mergedCapFrame
#assert_no_axioms FX1Poly.Polygraph.mergedCupFrame_convFull_castCupLeg
#assert_no_axioms FX1Poly.Polygraph.mergedCapFrame_convFull_castCapLeg
#assert_no_axioms FX1Poly.Polygraph.mergedFramesAlign
#assert_no_axioms FX1Poly.Polygraph.mergedFramesEndpoint
#assert_no_axioms FX1Poly.Polygraph.mergedSharedLegFramesCollapse
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSpineValleyStraightenCastBridge

end FX1PolyAudit
