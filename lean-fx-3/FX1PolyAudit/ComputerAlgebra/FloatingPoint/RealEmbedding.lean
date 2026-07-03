import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.FloatingPoint.RealEmbedding

/-! # FX1PolyAudit/ComputerAlgebra/FloatingPoint/RealEmbedding — zero-axiom
    gate (NUM-R-7c)

Per-declaration zero-axiom gate for the float bridge: the ℤ[1/β] ↪ ℝ
embedding, its setoid faithfulness (both directions), the constant
re-read principle (ℚ-level distance = real-level distance), and
monotonicity at both the constant and radix-scaled levels.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.realOfRadixScaled
#assert_no_axioms FX1Poly.ComputerAlgebra.realOfRadixScaledRespectsDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.denotesSameOfRealOfRadixScaled
#assert_no_axioms FX1Poly.ComputerAlgebra.isWithinRealBoundConstantOfIsWithinBound
#assert_no_axioms FX1Poly.ComputerAlgebra.lessEqualRealConstantOfLessEqualAs
#assert_no_axioms FX1Poly.ComputerAlgebra.realOfRadixScaledRespectsLessEqual

end FX1PolyAudit
