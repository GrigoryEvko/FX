import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationLinearFormers

/-! # FX1PolyAudit.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationLinearFormers

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationLinearFormers`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Linear-logic type-former SN (congruence-only, no beta+iota root rule): linearArrow and tensorProduct,
-- two-child formers structurally identical to arrowCode/productCode.  Cong inversions + twoChildCong SN.
-- Extends the former-SN coverage to the linear generator family.
#assert_no_axioms FX1Poly.Core.Step.from_linearArrow

#assert_no_axioms FX1Poly.Core.Step.from_tensorProduct

#assert_no_axioms FX1Poly.Core.StepStar.linearArrow_isStronglyNormalizing_of_source_target

#assert_no_axioms FX1Poly.Core.StepStar.tensorProduct_isStronglyNormalizing_of_factors

end FX1PolyAudit
