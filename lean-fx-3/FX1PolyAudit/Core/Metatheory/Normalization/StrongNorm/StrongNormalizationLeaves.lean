import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationLeaves

/-! # FX1PolyAudit.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationLeaves

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationLeaves`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.StepStar.noStep_unitTypeCode

#assert_no_axioms FX1Poly.Core.StepStar.unitTypeCode_isStronglyNormalizing

end FX1PolyAudit
