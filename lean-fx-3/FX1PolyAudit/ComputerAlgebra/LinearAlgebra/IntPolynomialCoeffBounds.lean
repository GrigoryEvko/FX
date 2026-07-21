import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialCoeffBounds

/-! # FX1PolyAudit/.../IntPolynomialCoeffBounds — zero-axiom gate

Per-declaration zero-axiom gate for the ℤ[x] coefficient-vanishing bounds: reading past a list's length,
trimming-agreement at every position, and the corollary that coefficients at or above the trimmed length
(strictly above the degree) vanish.  Structural induction on the list and position; the only non-list case
analysis is `Int.decEq coeff 0`.  Free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.polyCoeffPastLength
#assert_no_axioms FX1Poly.ComputerAlgebra.polyCoeffTrimAgree
#assert_no_axioms FX1Poly.ComputerAlgebra.polyCoeffZeroFromTrimLength
#assert_no_axioms FX1Poly.ComputerAlgebra.polyCoeffPastLengthGrounding
#assert_no_axioms FX1Poly.ComputerAlgebra.polyCoeffTrimAgreeGrounding

end FX1PolyAudit
