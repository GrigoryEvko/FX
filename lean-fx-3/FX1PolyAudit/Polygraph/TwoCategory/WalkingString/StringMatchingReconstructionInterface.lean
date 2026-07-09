import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMatchingReconstructionInterface

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringMatchingReconstructionInterface — zero-axiom gate

Per-declaration zero-axiom gate for the FC-6 completeness-residual reductions: the two interfaces
(`StringMatchingReconstruction`, `StringFcNormalizer`), each reduction of `StringMatchingReductsShareSpineTrace`
(the matching-section route and the matching-injective-normalizer route), the base completeness / keystone /
decision assembled from each, and the two honesty markers.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringMatchingReductsShareSpineTrace_ofReconstruction
#assert_no_axioms FX1Poly.Polygraph.stringConvOfMapEq_ofReconstruction
#assert_no_axioms FX1Poly.Polygraph.stringSaturatedMatchingCanonicalization_ofReconstruction
#assert_no_axioms FX1Poly.Polygraph.decidableStringSaturatedConv_ofReconstruction
#assert_no_axioms FX1Poly.Polygraph.stringMatchingReductsShareSpineTrace_ofNormalizer
#assert_no_axioms FX1Poly.Polygraph.stringConvOfMapEq_ofNormalizer
#assert_no_axioms FX1Poly.Polygraph.stringSaturatedMatchingCanonicalization_ofNormalizer
#assert_no_axioms FX1Poly.Polygraph.decidableStringSaturatedConv_ofNormalizer
#assert_no_axioms FX1Poly.Polygraph.fxString_hasReconstructionInterfaceReduction
#assert_no_axioms FX1Poly.Polygraph.fxString_hasReconstructionInhabited

end FX1PolyAudit
