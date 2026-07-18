import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Analysis.RealFiniteSum

/-! # FX1PolyAudit/ComputerAlgebra/Analysis/RealFiniteSum — zero-axiom gate
    (ANALYSIS-FINSUM-1)

Per-declaration zero-axiom gate for the real finite-sum layer: the prefix
fold, its setoid congruence, additivity, scalar pull, the count-scaled bound
respect, the cut split, and the product regroup.

Every declaration must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.sumReal
#assert_no_axioms FX1Poly.ComputerAlgebra.sumRealZero
#assert_no_axioms FX1Poly.ComputerAlgebra.sumRealSucc
#assert_no_axioms FX1Poly.ComputerAlgebra.sumRealRespectsDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.sumRealAddReal
#assert_no_axioms FX1Poly.ComputerAlgebra.sumRealScalarMulReal
#assert_no_axioms FX1Poly.ComputerAlgebra.sumRealNegReal
#assert_no_axioms FX1Poly.ComputerAlgebra.natScaleRational
#assert_no_axioms FX1Poly.ComputerAlgebra.sumRealRespectsIsWithinRealBound
#assert_no_axioms FX1Poly.ComputerAlgebra.sumRealSplit
#assert_no_axioms FX1Poly.ComputerAlgebra.sumRealRegroupProduct
#assert_no_axioms FX1Poly.ComputerAlgebra.sumRealMonotone
#assert_no_axioms FX1Poly.ComputerAlgebra.sumRealTriangle

end FX1PolyAudit
