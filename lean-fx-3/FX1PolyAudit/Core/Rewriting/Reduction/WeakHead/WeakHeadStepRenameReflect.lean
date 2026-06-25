import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.Reduction.WeakHead.WeakHeadStepRenameReflect

/-! # FX1PolyAudit.Core.Rewriting.Reduction.WeakHead.WeakHeadStepRenameReflect

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Rewriting.Reduction.WeakHead.WeakHeadStepRenameReflect`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- A left-invertible renaming REFLECTS weak-head reduction (hence preserves weak-head normality): the
-- neutral-arm ingredient of the stratified ReducibleTypeStep rename-closure, derived from WeakHeadStep.rename
-- preservation run on the left inverse plus the round-trip (no per-shape inversion grind).
#assert_no_axioms FX1Poly.Core.RawTerm.rename_leftInverse_roundTrip

#assert_no_axioms FX1Poly.Core.WeakHeadStep.rename_reflects_of_leftInverse

#assert_no_axioms FX1Poly.Core.WeakHeadStep.rename_preserves_weakHeadNormal_of_leftInverse

end FX1PolyAudit
