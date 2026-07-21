import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialPseudoRemStable

/-! # FX1PolyAudit/.../IntPolynomialPseudoRemStable — zero-axiom gate

Per-declaration zero-axiom gate for the pseudo-remainder terminal-shape stability: a below-divisor-degree
dividend is its own pseudo-remainder for every fuel (`polyPseudoRemBelowDivisor`).  Structural fuel
recursion; guard `Nat.decLt` cased, false branch by `absurd`.  Free of `propext`, `Quot.sound`, `Classical`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.polyPseudoRemZeroFuel
#assert_no_axioms FX1Poly.ComputerAlgebra.polyPseudoRemBelowDivisor
#assert_no_axioms FX1Poly.ComputerAlgebra.polyPseudoRemBelowDivisorGrounding

end FX1PolyAudit
