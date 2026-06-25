import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationModalEliminators

/-! # FX1PolyAudit.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationModalEliminators

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationModalEliminators`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Modal-core beta+iota SN coverage: gen_modElim / gen_subsume are congruence-only (no iota root rule; the
-- modal collapse is raw eta), so their cong inversions + one-child-cong SN closures complete the modal-core SN
-- coverage alongside modIntro (StrongNormalizationConstructors) and the modIntro reducibility candidate.
#assert_no_axioms FX1Poly.Core.Step.from_modElim

#assert_no_axioms FX1Poly.Core.Step.from_subsume

#assert_no_axioms FX1Poly.Core.StepStar.modElim_isStronglyNormalizing_of_child

#assert_no_axioms FX1Poly.Core.StepStar.subsume_isStronglyNormalizing_of_child

end FX1PolyAudit
