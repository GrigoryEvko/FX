import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.BoolElimStrongNormalization

/-! # FX1PolyAudit.Core.Metatheory.Normalization.StrongNorm.BoolElimStrongNormalization

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Metatheory.Normalization.StrongNorm.BoolElimStrongNormalization`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- boolElim s t e is strongly normalizing when its scrutinee and both branches are SN (the branch-SN form,
-- via a triple nested accessibility induction absorbing the iota-redex).  The iota-head-expansion SN
-- foundation for boolElim reducibility and the fundamental theorem's eliminator arm.
#assert_no_axioms FX1Poly.Core.StepStar.boolElim_isStronglyNormalizing_of_strongly_normalizing_branches

end FX1PolyAudit
