import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationApplication

/-! # FX1PolyAudit.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationApplication

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationApplication`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- CR1 structural ingredient: an application's strong normalization descends to its function (Acc pullback).
#assert_no_axioms FX1Poly.Core.appFunctionCongStep

#assert_no_axioms FX1Poly.Core.isStronglyNormalizing_of_appFunction_aux

#assert_no_axioms FX1Poly.Core.isStronglyNormalizing_of_appFunction

end FX1PolyAudit
