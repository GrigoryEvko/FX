import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.IdentityEliminatorStrongNormalization

/-! # FX1PolyAudit.Core.Metatheory.Normalization.StrongNorm.IdentityEliminatorStrongNormalization

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Metatheory.Normalization.StrongNorm.IdentityEliminatorStrongNormalization`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Identity eliminators: idJ / idStrictRec base witness is SN when base and witness are SN, via the
-- boolElim-style double nested accessibility induction over base and witness.
#assert_no_axioms FX1Poly.Core.StepStar.idJ_isStronglyNormalizing_of_strongly_normalizing_base

#assert_no_axioms FX1Poly.Core.StepStar.idStrictRec_isStronglyNormalizing_of_strongly_normalizing_base

end FX1PolyAudit
