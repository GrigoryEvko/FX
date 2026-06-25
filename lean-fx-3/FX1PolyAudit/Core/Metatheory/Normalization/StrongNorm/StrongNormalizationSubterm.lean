import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationSubterm

/-! # FX1PolyAudit.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationSubterm

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationSubterm`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Strong-normalization inverse lemmas for dependent type-code children.  These are the subterm
-- accessibility projections needed by structural arguments over reducible Pi/Sigma type values.
#assert_no_axioms FX1Poly.Core.StepStar.domain_isStronglyNormalizing_of_piTyCode

#assert_no_axioms FX1Poly.Core.StepStar.codomain_isStronglyNormalizing_of_piTyCode

#assert_no_axioms FX1Poly.Core.StepStar.domain_isStronglyNormalizing_of_sigmaTyCode

#assert_no_axioms FX1Poly.Core.StepStar.codomain_isStronglyNormalizing_of_sigmaTyCode

end FX1PolyAudit
