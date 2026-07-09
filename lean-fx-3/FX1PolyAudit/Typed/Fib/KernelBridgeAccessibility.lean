import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Fib.KernelBridgeAccessibility

/-! # FX1PolyAudit.Typed.Fib.KernelBridgeAccessibility — zero-axiom gate (CORE-WP r1 K3/K4/K5)

Per-declaration zero-axiom gate for the mode-accessibility decider bridge: the affine graph's decidable-equality
data, the accessibility relation and its total decider (through the generic `modalityPathDecEq`), the `Bool`
surface, the three real paths, and both-verdict theorems (K3); the discharged premise bridge + concrete corpus
instances (K4); and the separation certificate + markers (K5).  Must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## K3 — the decider + both verdicts -/

#assert_no_axioms FX1Poly.Core.Fib.affineGraphModeDecEq
#assert_no_axioms FX1Poly.Core.Fib.affineGraphModalityDecEq
#assert_no_axioms FX1Poly.Core.Fib.IsModeAccessible
#assert_no_axioms FX1Poly.Core.Fib.modeAccessibilityDecider
#assert_no_axioms FX1Poly.Core.Fib.modeAccessibleBool
#assert_no_axioms FX1Poly.Core.Fib.fibrantUsePath
#assert_no_axioms FX1Poly.Core.Fib.dimensionalUsePath
#assert_no_axioms FX1Poly.Core.Fib.doubleLockPath
#assert_no_axioms FX1Poly.Core.Fib.modeAccessible_fibrant_self
#assert_no_axioms FX1Poly.Core.Fib.modeAccessible_dimensional_self
#assert_no_axioms FX1Poly.Core.Fib.modeAccessible_doubleLock_self
#assert_no_axioms FX1Poly.Core.Fib.modeAccessible_fibrant_dimensional_false
#assert_no_axioms FX1Poly.Core.Fib.modeAccessible_dimensional_doubleLock_false

end FX1PolyAudit
