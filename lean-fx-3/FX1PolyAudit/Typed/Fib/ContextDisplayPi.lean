import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Fib.ContextDisplayPi

/-! # FX1PolyAudit.Typed.Fib.ContextDisplayPi — zero-axiom gate (fib-1d (i))

Per-declaration zero-axiom gate for the fibred-Π right adjoint's forward transpose: the kernel's `lam` realizes
the currying map `Tm(Γ.A, B) → Tm(Γ, Π_A B)` over the comprehension, and the comprehension-tie. Must be free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.Fib.lamRealizesFibredPiTranspose
#assert_no_axioms FX1Poly.Core.Fib.fibredPiTranspose_overComprehension
#assert_no_axioms FX1Poly.Core.Fib.appRealizesFibredPiCotranspose
#assert_no_axioms FX1Poly.Core.Fib.fibredPiBetaTriangle
#assert_no_axioms FX1Poly.Core.Fib.fibredPiEtaTriangle

end FX1PolyAudit
