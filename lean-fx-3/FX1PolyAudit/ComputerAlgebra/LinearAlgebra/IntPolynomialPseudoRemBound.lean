import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialPseudoRemBound

/-! # FX1PolyAudit/.../IntPolynomialPseudoRemBound — zero-axiom gate

Per-declaration zero-axiom gate for the pseudo-remainder degree bound: with adequate fuel the pseudo-remainder
has degree strictly below the divisor, threading the single-step degree decrease through the fuel recursion.
Structural recursion on fuel; guard `Nat.decLt`; core Nat order lemmas.  Free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.polyPseudoRemDegreeLtDivisor
#assert_no_axioms FX1Poly.ComputerAlgebra.polyPseudoRemDegreeLtDivisorGrounding

end FX1PolyAudit
