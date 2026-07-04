import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedFragmentNewman

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/SaturatedFragmentNewman — zero-axiom gate

Per-declaration zero-axiom gate for the fragment's star-congruence toolkit, the conditional
Newman reduction, the conditional Knuth-Bendix word-problem decision, and the conditional
canonicity of the fragment normalizer.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.saturatedInterchangeFreeReducesStar_whiskerLeftCongr
#assert_no_axioms FX1Poly.Polygraph.saturatedInterchangeFreeReducesStar_whiskerRightCongr
#assert_no_axioms FX1Poly.Polygraph.saturatedInterchangeFreeReducesStar_vcompCongrLeft
#assert_no_axioms FX1Poly.Polygraph.saturatedInterchangeFreeReducesStar_vcompCongrRight
#assert_no_axioms FX1Poly.Polygraph.saturatedStepInterchangeFree_isConfluent
#assert_no_axioms FX1Poly.Polygraph.decidableSaturatedFragmentEquational
#assert_no_axioms FX1Poly.Polygraph.saturatedFragmentNormalize_isCanonical

end FX1PolyAudit
