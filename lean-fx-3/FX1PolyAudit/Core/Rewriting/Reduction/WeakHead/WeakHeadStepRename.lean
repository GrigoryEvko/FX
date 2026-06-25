import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.Reduction.WeakHead.WeakHeadStepRename

/-! # FX1PolyAudit.Core.Rewriting.Reduction.WeakHead.WeakHeadStepRename

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Rewriting.Reduction.WeakHead.WeakHeadStepRename`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The complete weak-head reduction commutes with renaming (the renaming twin of WeakHeadStep.subst):
-- the whnfExpand-arm ingredient of the stratified ReducibleTypeStep rename-closure.
#assert_no_axioms FX1Poly.Core.IotaHeadStep.rename

#assert_no_axioms FX1Poly.Core.WeakHeadStep.rename

end FX1PolyAudit
