import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Substrate.Univalence.TranspensionAffineContractionEquivariance

/-! # AuditTranspensionAffineContractionEquivariance — zero-axiom gate for TRANSP-DSL (#1414)

The transpension/affine contraction's partial-substitution equivariance
rides the shipped ETA-T2 `strengthenBy?` machinery; each pin must be free
of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.transpensionAffineContraction_subst
#assert_no_axioms FX1Poly.Core.transpensionAffineContraction_rename
#assert_no_axioms FX1Poly.Core.transpensionAffineContraction_firingGuardSound

end FX1PolyAudit
