import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Fib.KernelBridgeModeTheory

/-! # FX1PolyAudit.Typed.Fib.KernelBridgeModeTheory — zero-axiom gate (CORE-WP r1 K2)

Per-declaration zero-axiom gate for the kernel's affine dimension mode theory presented as a 2-polygraph: the
`ModeSignature` (relation-free, empty 2-cell family), its decidable-equality data (`Unit`/`Unit`/`Empty`), the
two parallel free cells, the kernel's own dimension-2 free word-problem decision (through `decideTwoCellConvFull`)
with its `rfl` verdict, the `admitByRowAware` cross-arc non-match, and the presentation marker.  Must be free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.Fib.affineDimensionModeSignature
#assert_no_axioms FX1Poly.Core.Fib.affineKernelModeDecEq
#assert_no_axioms FX1Poly.Core.Fib.affineKernelModalityDecEq
#assert_no_axioms FX1Poly.Core.Fib.affineKernelTwoCellDecEq
#assert_no_axioms FX1Poly.Core.Fib.kernelAffineIdentityCell
#assert_no_axioms FX1Poly.Core.Fib.kernelAffineVcompIdentityCell
#assert_no_axioms FX1Poly.Core.Fib.kernelAffineFreeDimTwoDecision
#assert_no_axioms FX1Poly.Core.Fib.kernelAffineFreeDimTwoDecision_holds
#assert_no_axioms FX1Poly.Core.Fib.affineKernelRowAware
#assert_no_axioms FX1Poly.Core.Fib.affineKernel_admitByRowAware_isNone
#assert_no_axioms FX1Poly.Core.Fib.fxKernelBridge_hasAffineModeTheoryPresentation

end FX1PolyAudit
