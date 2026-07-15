import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.Normalize.WeakHeadNormalPreservation

/-! # FX1PolyAudit.Core.Rewriting.Normalize.WeakHeadNormalPreservation

Zero-axiom audit shard mirroring kernel module
`FX1Poly.Core.Rewriting.Normalize.WeakHeadNormalPreservation` — the packaging inversion of a step
INTO a concrete cell (`Step.weakHeadOrSpineStepIntoCell`), the backward weak-head-step reflection
(`WeakHeadStep.reflectAlongStep`), and the weak-head-normality preservation corollary.  Each
declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.Step.weakHeadOrSpineStepIntoCell
#assert_no_axioms FX1Poly.Core.WeakHeadStep.reflectAlongStep
#assert_no_axioms FX1Poly.Core.WeakHeadStep.weakHeadNormalPreservedByStep

end FX1PolyAudit
