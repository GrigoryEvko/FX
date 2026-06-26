import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Fib.BiInitiality

/-! # FX1PolyAudit.Core.Fib.BiInitiality — zero-axiom gate (fib-5 b/d)

Per-declaration zero-axiom gate for the fibred kernel's object-level bi-initiality substrate: the context
algebra, the interpretation morphism existence + uniqueness (reused from context-5, no Quot.sound), the
faithful-witness non-vacuity, and the syntactic-algebra smoke. Must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.Fib.fxFibredKernel_contextAlgebra
#assert_no_axioms FX1Poly.Core.Fib.fxFibredKernel_interpretation
#assert_no_axioms FX1Poly.Core.Fib.fxFibredKernel_interpretation_unique
#assert_no_axioms FX1Poly.Core.Fib.fxFibredKernel_interpretation_faithful
#assert_no_axioms FX1Poly.Core.Fib.fxFibredKernel_contextAlgebra_isSyntactic

end FX1PolyAudit
