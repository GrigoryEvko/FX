import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Dimensions.Parametricity.GelIsTranspensionAtAffine

/-! # FX1PolyAudit/AuditGelIsTranspensionAtAffine — zero-axiom gate for TRANSP-PARAM-RETIRE rung 1

Per-declaration zero-axiom gate for
`FX1Poly/Typed/Dimensions/Parametricity/GelIsTranspensionAtAffine.lean`: the Gel former's multiplier
structure-class (`gelStructureClass`), the Cavallo-Harper soundness gate (`gelMultiplier_forbidsDiagonal`
and the affine-property facts), the `mode-19` arity-multiplier identity (`gelMultiplier_isParametricArity`
/ `gelMultiplier_parametricIsIrreflexive`), the computing gel-beta leg (`gelComputesAtEveryScope`), the
recovery witness (`gelRecoveredAtAffine`), and the honest per-operator recovery ledger
(`transpensionOperatorIsKernelBacked` / `kernelBackedOperatorCount_isOne`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.gelStructureClass
#assert_no_axioms FX1Poly.Typed.gelMultiplier_forbidsDiagonal
#assert_no_axioms FX1Poly.Typed.gelMultiplier_forbidsConnections
#assert_no_axioms FX1Poly.Typed.gelMultiplier_forbidsReversal
#assert_no_axioms FX1Poly.Typed.gelMultiplier_isAffine
#assert_no_axioms FX1Poly.Typed.gelMultiplier_isQuantifiable
#assert_no_axioms FX1Poly.Typed.gelMultiplier_isSemicartesian
#assert_no_axioms FX1Poly.Typed.gelMultiplier_isParametricArity
#assert_no_axioms FX1Poly.Typed.gelMultiplier_parametricIsIrreflexive
#assert_no_axioms FX1Poly.Typed.gelComputesAtEveryScope
#assert_no_axioms FX1Poly.Typed.gelRecoveredAtAffine
#assert_no_axioms FX1Poly.Typed.transpensionOperatorIsKernelBacked
#assert_no_axioms FX1Poly.Typed.gel_isKernelBacked
#assert_no_axioms FX1Poly.Typed.kernelBackedOperatorCount_isOne

end FX1PolyAudit
