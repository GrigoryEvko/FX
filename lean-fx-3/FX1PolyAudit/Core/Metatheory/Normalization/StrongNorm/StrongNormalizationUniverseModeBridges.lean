import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationUniverseModeBridges

/-! # FX1PolyAudit.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationUniverseModeBridges

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationUniverseModeBridges`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Universe-mode bridge beta+iota SN coverage: gen_liftInnerToOuter (1-child inner-to-outer lift) and
-- gen_lowerOuterToInner (2-child outer-to-inner lower) are congruence-only (no iota root rule; the mode-bridge
-- collapse `lower (lift x)` is not in the current beta+iota substrate, like the modal modElim collapse), so
-- their cong inversions + one-/two-child-cong SN closures complete the 2LTT mode-bridge SN coverage.
#assert_no_axioms FX1Poly.Core.Step.from_liftInnerToOuter

#assert_no_axioms FX1Poly.Core.Step.from_lowerOuterToInner

#assert_no_axioms FX1Poly.Core.StepStar.liftInnerToOuter_isStronglyNormalizing_of_child

#assert_no_axioms FX1Poly.Core.StepStar.lowerOuterToInner_isStronglyNormalizing_of_children

end FX1PolyAudit
