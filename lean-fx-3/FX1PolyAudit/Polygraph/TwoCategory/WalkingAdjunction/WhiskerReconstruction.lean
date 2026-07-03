import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.WhiskerReconstruction

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.WhiskerReconstruction — zero-axiom gate (mode-3 floor)

Per-declaration zero-axiom gate for the YES-direction readback bridge over the completed convertibility:
the dissolved unsoundness witness (`adjunctionUnitFrame_convFull_unit` — the identity-whiskered frame is now
convertible to the bare generator), the interchange-free normal-form lift, the chain-concat conversion, and the
proved reduction `nfReconstructFull ⟹ spine reconstruction` (so closing the normal-form residual closes the
whole YES-direction).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.adjunctionUnitFrame_convFull_unit
#assert_no_axioms FX1Poly.Polygraph.convToInterchangeFreeNormalFormFull
#assert_no_axioms FX1Poly.Polygraph.chainToCellConcatConvFull
#assert_no_axioms FX1Poly.Polygraph.adjunctionReconstructionFromNfFull
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasWhiskerFunctorialityReconstruction

end FX1PolyAudit
