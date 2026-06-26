import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Fib.ModeLockPath

/-! # FX1PolyAudit.Core.Fib.ModeLockPath — zero-axiom gate (fib-3b)

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

end FX1PolyAudit
