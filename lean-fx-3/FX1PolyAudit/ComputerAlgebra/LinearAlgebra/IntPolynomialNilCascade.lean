import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialNilCascade

/-! # FX1PolyAudit/.../IntPolynomialNilCascade — zero-axiom gate

Per-declaration zero-axiom gate for the ℤ[x] zero-polynomial nil cascade (the seventeenth brick of
`invariantFactorSeparator`'s ℚ[x] arc, WP-ENDO #2255): the coefficient ↔ trims-to-nil bridge, zero-monomial
annihilation, and pseudo-dividing the zero polynomial leaving a zero remainder
(`polyPseudoRemZeroDividendTrimsNil`) — the fuel-adequacy wiring's zero-polynomial edge.

Structural recursions on list / degree / fuel; coefficient homomorphisms; `Int.decEq`-clean trimming.  Must
be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.polyTrimConsZeroNil
#assert_no_axioms FX1Poly.ComputerAlgebra.polyTrimNilOfAllCoeffZero
#assert_no_axioms FX1Poly.ComputerAlgebra.polyCoeffZeroOfTrimNil
#assert_no_axioms FX1Poly.ComputerAlgebra.polyCoeffZeroSingleton
#assert_no_axioms FX1Poly.ComputerAlgebra.polyCoeffZeroConsSucc
#assert_no_axioms FX1Poly.ComputerAlgebra.polyMulZeroMonomialCoeff
#assert_no_axioms FX1Poly.ComputerAlgebra.polyPseudoRemZeroDividendTrimsNil
#assert_no_axioms FX1Poly.ComputerAlgebra.polyPseudoRemZeroDividendGrounding
#assert_no_axioms FX1Poly.ComputerAlgebra.fxIntPoly_hasZeroPolynomialNilCascade

end FX1PolyAudit
