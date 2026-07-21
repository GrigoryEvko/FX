import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Algebra.SetoidRingTower

/-! # FX1PolyAudit/ComputerAlgebra/Algebra/SetoidRingTower — zero-axiom gate

Per-declaration zero-axiom gate for the ℕ→ℤ→ℚ→ℝ→ℂ diagram of setoid-rings: the ℤ
and ℚ ring objects, the commutative-semiring layer hosting ℕ, the four widening
homomorphisms, and their composite widenings.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.intCommutativeRingWitness
#assert_no_axioms FX1Poly.ComputerAlgebra.rationalCommutativeRingWitness
#assert_no_axioms FX1Poly.ComputerAlgebra.CommutativeSemiringWitness
#assert_no_axioms FX1Poly.ComputerAlgebra.commutativeSemiringWitnessOfRing
#assert_no_axioms FX1Poly.ComputerAlgebra.natCommutativeSemiringWitness
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidSemiringHom
#assert_no_axioms FX1Poly.ComputerAlgebra.embedNatToInt
#assert_no_axioms FX1Poly.ComputerAlgebra.embedIntToRat
#assert_no_axioms FX1Poly.ComputerAlgebra.embedRatToReal
#assert_no_axioms FX1Poly.ComputerAlgebra.complexOfReal
#assert_no_axioms FX1Poly.ComputerAlgebra.embedRealToComplex
#assert_no_axioms FX1Poly.ComputerAlgebra.embedIntToReal
#assert_no_axioms FX1Poly.ComputerAlgebra.embedRatToComplex
#assert_no_axioms FX1Poly.ComputerAlgebra.embedIntToComplex

end FX1PolyAudit
