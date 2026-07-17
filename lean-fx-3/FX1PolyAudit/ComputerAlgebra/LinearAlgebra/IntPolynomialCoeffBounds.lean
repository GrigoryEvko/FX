import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialCoeffBounds

/-! # FX1PolyAudit/.../IntPolynomialCoeffBounds — zero-axiom gate

Per-declaration zero-axiom gate for the ℤ[x] coefficient-vanishing bounds (the eighth brick of
`invariantFactorSeparator`'s ℚ[x] arc, WP-ENDO #2255): reading past a list's length, trimming-agreement at
every position, and the corollary that coefficients at/above the trimmed length (strictly above the
degree) vanish.

Structural induction on the list and position; the only non-list case analysis is `Int.decEq coeff 0`; the
Nat plumbing is core `Nat.le_of_succ_le_succ` / `Nat.not_succ_le_zero`.  Must be free of `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.polyCoeffPastLength
#assert_no_axioms FX1Poly.ComputerAlgebra.polyCoeffTrimAgree
#assert_no_axioms FX1Poly.ComputerAlgebra.polyCoeffZeroFromTrimLength
#assert_no_axioms FX1Poly.ComputerAlgebra.polyCoeffPastLengthGrounding
#assert_no_axioms FX1Poly.ComputerAlgebra.polyCoeffTrimAgreeGrounding
#assert_no_axioms FX1Poly.ComputerAlgebra.fxIntPoly_hasCoefficientVanishingBounds

end FX1PolyAudit
