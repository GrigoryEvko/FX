import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedFragmentNormalize

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/SaturatedFragmentNormalize — zero-axiom gate

Per-declaration zero-axiom gate for the saturated fragment normalizer and its
saturated-class soundness.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.saturatedFragmentNormalizer
#assert_no_axioms FX1Poly.Polygraph.saturatedFragmentNormalize_conv

end FX1PolyAudit
