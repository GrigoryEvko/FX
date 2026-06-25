import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationCodeFormers

/-! # FX1PolyAudit.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationCodeFormers

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationCodeFormers`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Structural SN closure completing the universe-code former family: the one-child listCode/optionCode
-- congruence inversions + SN, the three-child idCode inversion + SN, and the reusable three-child congruence
-- SN combinator (the three-child analogue of the one/two-child versions).  The SN half of "the code is a
-- reducible member of El"; SN is fuel-independent.
#assert_no_axioms FX1Poly.Core.Step.from_listCode

#assert_no_axioms FX1Poly.Core.Step.from_optionCode

#assert_no_axioms FX1Poly.Core.Step.from_idCode

#assert_no_axioms FX1Poly.Core.StepStar.isStronglyNormalizing_of_threeChildCong

#assert_no_axioms FX1Poly.Core.StepStar.listCode_isStronglyNormalizing_of_element

#assert_no_axioms FX1Poly.Core.StepStar.optionCode_isStronglyNormalizing_of_element

#assert_no_axioms FX1Poly.Core.StepStar.idCode_isStronglyNormalizing_of_type_endpoints

end FX1PolyAudit
