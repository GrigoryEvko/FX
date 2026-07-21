import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialDegreeBound

/-! # FX1PolyAudit/.../IntPolynomialDegreeBound — zero-axiom gate

Per-declaration zero-axiom gate for the degree-from-coefficient-vanishing lever: the trim invariant
(nonzero last coefficient), the nonzero leading coefficient, and the strict degree bound when coefficients
vanish at or above a positive bound.  Structural induction with `Int.decEq` casing and constructive Nat
decidability (`Nat.lt_of_not_le`).  Free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.polyTrimNilOrLastNonzero
#assert_no_axioms FX1Poly.ComputerAlgebra.polyLeadingCoeffNonzeroWhenNonempty
#assert_no_axioms FX1Poly.ComputerAlgebra.polyCoeffAtDegreeNonzeroWhenNonempty
#assert_no_axioms FX1Poly.ComputerAlgebra.polyDegreeLtOfCoeffVanishingAbove
#assert_no_axioms FX1Poly.ComputerAlgebra.polyLeadingCoeffNonzeroGrounding
#assert_no_axioms FX1Poly.ComputerAlgebra.polyCoeffAtDegreeNonzeroGrounding

end FX1PolyAudit
