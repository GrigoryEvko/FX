import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialDeterminantalDivisorThree

/-! # FX1PolyAudit/.../IntPolynomialDeterminantalDivisorThree — zero-axiom gate

Per-declaration zero-axiom gate for the dimension-3 determinantal divisors: `d₁` (GCD of the nine `1×1`
minors) and `d₂` (GCD of the nine `2×2` minors) of `x·I − M`, whose degree signature `(deg d₁, deg d₂)`
separates all three similarity classes of char poly `(x−2)³` — `J₃(2)` `(0,0)`, `J₂⊕J₁` `(0,1)`, `2·I₃`
`(1,2)`.  GCD folds + `charMatrixMinor` + `polyDegree` + `decide` groundings + pair inequalities.  Free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.threeByThreeMatrix
#assert_no_axioms FX1Poly.ComputerAlgebra.charMatrixDivisorOneAtThree
#assert_no_axioms FX1Poly.ComputerAlgebra.charMatrixDivisorTwoAtThree
#assert_no_axioms FX1Poly.ComputerAlgebra.divisorDegreeSignatureThree
#assert_no_axioms FX1Poly.ComputerAlgebra.allThreeShareCharPolyCubed
#assert_no_axioms FX1Poly.ComputerAlgebra.divisorSignatureJordanBlockThree
#assert_no_axioms FX1Poly.ComputerAlgebra.divisorSignatureJordanTwoPlusOne
#assert_no_axioms FX1Poly.ComputerAlgebra.divisorSignatureScalarThree
#assert_no_axioms FX1Poly.ComputerAlgebra.DissimilarByDivisorSignatureThree
#assert_no_axioms FX1Poly.ComputerAlgebra.allThreeCubicClassesPairwiseDissimilar

end FX1PolyAudit
