import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Fib.ModeLockPath

/-! # FX1PolyAudit.Typed.Fib.ModeLockPath — zero-axiom gate (fib-3b)

Per-declaration zero-axiom gate for the mode-axis polygraph presentation of the affine dimension modality and
the faithful embedding of the bespoke `ObligationModality` into the mode axis's `ModalityPath`: the affine
dimension mode graph, its single mode + generator, the enum-to-path translation, the two path-length identities,
and the injectivity of the translation. Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.Fib.affineDimensionModeGraph
#assert_no_axioms FX1Poly.Core.Fib.affineDimensionMode
#assert_no_axioms FX1Poly.Core.Fib.affineLockGenerator
#assert_no_axioms FX1Poly.Core.Fib.obligationModalityToPath
#assert_no_axioms FX1Poly.Core.Fib.obligationModalityToPath_fibrant_length
#assert_no_axioms FX1Poly.Core.Fib.obligationModalityToPath_dimensional_length
#assert_no_axioms FX1Poly.Core.Fib.obligationModalityToPath_injective
#assert_no_axioms FX1Poly.Core.Fib.affineModalityPath_length_injective_overEndpoints
#assert_no_axioms FX1Poly.Core.Fib.affineModalityPath_length_injective
#assert_no_axioms FX1Poly.Core.Fib.affineModalityPathDecidableEq
#assert_no_axioms FX1Poly.Core.Fib.bindingModalityPath
#assert_no_axioms FX1Poly.Core.Fib.isFibrantlyAccessibleAt_eq_identityPathEq
#assert_no_axioms FX1Poly.Core.Fib.isDimensionallyAccessibleAt_eq_generatorPathEq
#assert_no_axioms FX1Poly.Core.Fib.isAccessibleAtModality_eq_pathEq
#assert_no_axioms FX1Poly.Core.Fib.pathToObligationModality
#assert_no_axioms FX1Poly.Core.Fib.pathToObligationModality_obligationModalityToPath
#assert_no_axioms FX1Poly.Core.Fib.obligationModalityToPath_length_le_one
#assert_no_axioms FX1Poly.Core.Fib.isAccessibleViaModeAxis
#assert_no_axioms FX1Poly.Core.Fib.isAccessibleAtModality_eq_isAccessibleViaModeAxis

end FX1PolyAudit
