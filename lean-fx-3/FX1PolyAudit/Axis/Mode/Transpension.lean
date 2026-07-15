import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Mode.Transpension

/-! # FX1PolyAudit/AuditAxisModeTranspension — zero-axiom gate for mode-11

Per-declaration zero-axiom gate for `mode-11` (`FX1Poly/Axis/Mode/Transpension.lean`): the transpension
adjunction `Π ⊣ Ξ` + the identity witness + the derived faithfulness theorems, the recovered-zoo enumeration,
and the honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The transpension adjunction + witness + derived faithfulness
#assert_no_axioms FX1Poly.Axis.TranspensionAdjunction
#assert_no_axioms FX1Poly.Axis.identityTranspension
#assert_no_axioms FX1Poly.Axis.TranspensionAdjunction.transpose_injective
#assert_no_axioms FX1Poly.Axis.TranspensionAdjunction.untranspose_injective
#assert_no_axioms FX1Poly.Axis.TranspensionAdjunction.transpose_surjective
#assert_no_axioms FX1Poly.Axis.TranspensionAdjunction.untranspose_surjective

-- The weakening ⊣ Π rung (the chain neighbour) + the non-degenerate witness
#assert_no_axioms FX1Poly.Axis.WeakeningPiAdjunction
#assert_no_axioms FX1Poly.Axis.productWeakeningPiAdjunction
#assert_no_axioms FX1Poly.Axis.WeakeningPiAdjunction.curry_injective
#assert_no_axioms FX1Poly.Axis.WeakeningPiAdjunction.uncurry_injective
#assert_no_axioms FX1Poly.Axis.WeakeningPiAdjunction.curry_surjective
#assert_no_axioms FX1Poly.Axis.WeakeningPiAdjunction.uncurry_surjective
#assert_no_axioms FX1Poly.Axis.productWeakeningPiAdjunction_dimension

-- The recovered zoo
#assert_no_axioms FX1Poly.Axis.TranspensionRecoverable
#assert_no_axioms FX1Poly.Axis.TranspensionRecoverable.all
#assert_no_axioms FX1Poly.Axis.TranspensionRecoverable.all_length

-- Honesty markers
#assert_no_axioms FX1Poly.Axis.fxMode_hasTranspensionZooRecovery
#assert_no_axioms FX1Poly.Axis.fxMode_hasFullMultiplierAdjointString
#assert_no_axioms FX1Poly.Axis.fxMode_hasDependentTranspension
#assert_no_axioms FX1Poly.Axis.fxMode_hasKernelTranspensionConnection

end FX1PolyAudit
