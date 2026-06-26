import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Fib.FibrationArchitecture

/-! # FX1PolyAudit.Core.Fib.FibrationArchitecture — zero-axiom gate (fib-0 design-lock)

Per-declaration zero-axiom gate for the four-axis fibred-kernel design-lock: the `FibAxis`/`CellSort` map,
the `FibredKernel` shape + its FX witness, the fib-1..5 connection-point ledger, and the `rfl` sanity facts.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.Fib.FibAxis.cellSort
#assert_no_axioms FX1Poly.Core.Fib.fxFibredKernel
#assert_no_axioms FX1Poly.Core.Fib.fxFib_hasTypeContextDisplay
#assert_no_axioms FX1Poly.Core.Fib.fxFib_hasTypeTermUniverseReflection
#assert_no_axioms FX1Poly.Core.Fib.fxFib_hasModeFibration
#assert_no_axioms FX1Poly.Core.Fib.fxFib_hasCrossAxisRightAdjointCoherence
#assert_no_axioms FX1Poly.Core.Fib.fxFib_hasWeakBiInitiality
#assert_no_axioms FX1Poly.Core.Fib.fxFibredKernel_presentation_eq
#assert_no_axioms FX1Poly.Core.Fib.modeAxis_cellSort
#assert_no_axioms FX1Poly.Core.Fib.termAxis_cellSort

end FX1PolyAudit
