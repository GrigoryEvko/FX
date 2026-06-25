import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.ApplicationStrongNormalizationForward

/-! # FX1PolyAudit.Core.Metatheory.Normalization.StrongNorm.ApplicationStrongNormalizationForward

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Metatheory.Normalization.StrongNorm.ApplicationStrongNormalizationForward`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- SN of an application under the beta-contraction side-condition (the member weak-head-expansion brick):
-- app f a is SN given f SN, a SN, and every beta-contraction body[a] (for f reducing to lam body) SN.  The
-- side-condition is essential, since SN of the two positions alone does not give SN of the application (the
-- Omega term loops).  This is "application preserves SN" and the load-bearing Pi arm of the recursor-value
-- `headExpand` premise.  `descendStepStar` is the StepStar-iterated forward SN closure (every reduct of an SN
-- term is SN).
#assert_no_axioms FX1Poly.Core.IsStronglyNormalizing.descendStepStar

#assert_no_axioms FX1Poly.Core.isStronglyNormalizing_applicationCell_aux

#assert_no_axioms FX1Poly.Core.isStronglyNormalizing_applicationCell_ofBetaContractionsStronglyNormalizing

end FX1PolyAudit
