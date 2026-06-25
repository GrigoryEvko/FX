import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationSmokeCorpus

/-! # FX1PolyAudit.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationSmokeCorpus

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationSmokeCorpus`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Concrete strong-normalization smoke corpus (variable leaf, unit leaf, identity beta-redex).
#assert_no_axioms FX1Poly.Core.smoke_variable_isStronglyNormalizing

#assert_no_axioms FX1Poly.Core.smoke_unit_isStronglyNormalizing

#assert_no_axioms FX1Poly.Core.smoke_identityRedex_isStronglyNormalizing

end FX1PolyAudit
