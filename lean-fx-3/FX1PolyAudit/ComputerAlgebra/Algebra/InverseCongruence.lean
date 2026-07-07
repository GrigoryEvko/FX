import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Algebra.InverseCongruence

/-! # FX1PolyAudit/ComputerAlgebra/Algebra/InverseCongruence — zero-axiom gate
    (NUM-ALG-3)

Per-declaration zero-axiom gate for the analytic inverse congruences: the ℝ
positivity inverse, the ℝ apartness inverse, and the ℂ Gauss inverse — each
base-congruent and witness-independent by inverse uniqueness.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.inverseRealCongr
#assert_no_axioms FX1Poly.ComputerAlgebra.inverseRealWitnessIndependent
#assert_no_axioms FX1Poly.ComputerAlgebra.inverseRealOfApartnessCongr
#assert_no_axioms FX1Poly.ComputerAlgebra.inverseRealOfApartnessWitnessIndependent
#assert_no_axioms FX1Poly.ComputerAlgebra.inverseComplexCongr
#assert_no_axioms FX1Poly.ComputerAlgebra.inverseComplexWitnessIndependent

end FX1PolyAudit
