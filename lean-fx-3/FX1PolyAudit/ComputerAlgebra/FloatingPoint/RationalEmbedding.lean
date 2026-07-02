import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.FloatingPoint.RationalEmbedding

/-! # FX1PolyAudit/ComputerAlgebra/FloatingPoint/RationalEmbedding — zero-axiom
    gate (NUM-Q-5)

Per-declaration zero-axiom gate for the ℤ[1/β] ↪ ℚ embedding: the clamped
rational reading, the denominator read-back, and the setoid-embedding iff with
both of its directions.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.rationalOfRadixScaled
#assert_no_axioms FX1Poly.ComputerAlgebra.rationalOfRadixScaledDenominatorInt
#assert_no_axioms FX1Poly.ComputerAlgebra.rationalOfRadixScaledRespectsDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.denotesSameOfRationalOfRadixScaled
#assert_no_axioms FX1Poly.ComputerAlgebra.rationalOfRadixScaledDenotesSameAsIff
#assert_no_axioms FX1Poly.ComputerAlgebra.rationalOfRadixScaledRespectsLessEqual
#assert_no_axioms FX1Poly.ComputerAlgebra.lessEqualOfRationalOfRadixScaled
#assert_no_axioms FX1Poly.ComputerAlgebra.rationalOfRadixScaledLessEqualAsIff

end FX1PolyAudit
