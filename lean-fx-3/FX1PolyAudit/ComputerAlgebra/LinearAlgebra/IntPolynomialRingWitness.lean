import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialRingWitness

/-! # FX1PolyAudit/.../IntPolynomialRingWitness — zero-axiom gate

Per-declaration zero-axiom gate for ℤ[x] as a setoid commutative ring (the first brick of the char-matrix →
invariant-factors layer, WP-ENDO #2255): `intPolynomialRingWitness` instantiates the generic
`SetoidMatrix`/`cofactorDet` tower at polynomials, so the characteristic matrix `x·I − M` (`charMatrix`) and
its determinant `det(x·I − M)` (`charPolyDeterminant`) are honest ℤ[x] objects.

Each ring law is an evaluation-homomorphism `rw` + a ℤ law.  Must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.polyDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.intPolynomialRingWitness
#assert_no_axioms FX1Poly.ComputerAlgebra.charMatrix
#assert_no_axioms FX1Poly.ComputerAlgebra.charPolyDeterminant
#assert_no_axioms FX1Poly.ComputerAlgebra.intPolynomialRingWitnessMulGrounding
#assert_no_axioms FX1Poly.ComputerAlgebra.charPolyDeterminantDiagGrounding
#assert_no_axioms FX1Poly.ComputerAlgebra.fxIntPoly_hasPolynomialRingWitness

end FX1PolyAudit
