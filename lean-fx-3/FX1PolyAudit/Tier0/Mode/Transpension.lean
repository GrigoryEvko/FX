import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.Transpension

/-! # FX1PolyAudit/AuditTier0ModeTranspension — zero-axiom gate for mode-11

Per-declaration zero-axiom gate for `mode-11` (`FX1Poly/Tier0/Mode/Transpension.lean`): the transpension
adjunction `Π ⊣ Ξ` + the identity witness + the derived faithfulness theorems, the recovered-zoo enumeration,
and the honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The transpension adjunction + witness + derived faithfulness
#assert_no_axioms FX1Poly.Tier0.TranspensionAdjunction
#assert_no_axioms FX1Poly.Tier0.identityTranspension
#assert_no_axioms FX1Poly.Tier0.TranspensionAdjunction.transpose_injective
#assert_no_axioms FX1Poly.Tier0.TranspensionAdjunction.untranspose_injective
#assert_no_axioms FX1Poly.Tier0.TranspensionAdjunction.transpose_surjective
#assert_no_axioms FX1Poly.Tier0.TranspensionAdjunction.untranspose_surjective

-- The weakening ⊣ Π rung (the chain neighbour) + the non-degenerate witness
#assert_no_axioms FX1Poly.Tier0.WeakeningPiAdjunction
#assert_no_axioms FX1Poly.Tier0.productWeakeningPiAdjunction
#assert_no_axioms FX1Poly.Tier0.WeakeningPiAdjunction.curry_injective
#assert_no_axioms FX1Poly.Tier0.WeakeningPiAdjunction.uncurry_injective
#assert_no_axioms FX1Poly.Tier0.WeakeningPiAdjunction.curry_surjective
#assert_no_axioms FX1Poly.Tier0.WeakeningPiAdjunction.uncurry_surjective
#assert_no_axioms FX1Poly.Tier0.productWeakeningPiAdjunction_dimension

-- The recovered zoo
#assert_no_axioms FX1Poly.Tier0.TranspensionRecoverable
#assert_no_axioms FX1Poly.Tier0.TranspensionRecoverable.all
#assert_no_axioms FX1Poly.Tier0.TranspensionRecoverable.all_length

-- Honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasTranspensionZooRecovery
#assert_no_axioms FX1Poly.Tier0.fxMode_hasFullMultiplierAdjointString
#assert_no_axioms FX1Poly.Tier0.fxMode_hasDependentTranspension
#assert_no_axioms FX1Poly.Tier0.fxMode_hasKernelTranspensionConnection

end FX1PolyAudit
