import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Reducibility.Stratified.StratifiedReducibleMemberStepClosure

/-! # FX1PolyAudit.Core.Metatheory.Reducibility.Stratified.StratifiedReducibleMemberStepClosure

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Metatheory.Reducibility.Stratified.StratifiedReducibleMemberStepClosure`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- CR2 / CR3 closure lifted to the semantic-membership layer (the forward-Step, forward-StepStar, and
-- neutral-backward companions of the CR1 membership corollary; the Tait closure bricks the fundamental
-- theorem's neutral and reduction-stable cases consume).
#assert_no_axioms FX1Poly.Core.IsReducibleMemberAt.closedUnderStep

#assert_no_axioms FX1Poly.Core.IsReducibleMemberAt.closedUnderStepStar

#assert_no_axioms FX1Poly.Core.IsReducibleMemberAt.neutralExpansion

end FX1PolyAudit
