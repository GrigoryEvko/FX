import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationRenameForward

/-! # FX1PolyAudit.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationRenameForward

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationRenameForward`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Forward strong-normalization preservation along a left-invertible renaming: the neutral-leaf
-- ingredient of the stratified reducibility rename-closure.  Explicit per-decl gate.
#assert_no_axioms FX1Poly.Core.StepStar.isStronglyNormalizing_rename_of_leftInverse

end FX1PolyAudit
