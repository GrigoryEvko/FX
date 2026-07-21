import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Algebra.InverseCongruence

/-! # FX1PolyAudit/ComputerAlgebra/Algebra/InverseCongruence — zero-axiom gate

Per-declaration zero-axiom gate for the ℝ and ℂ inverse congruences: each of the
ℝ positivity inverse, ℝ apartness inverse, and ℂ Gauss inverse is base-congruent
and witness-independent.

Free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.inverseRealCongr
#assert_no_axioms FX1Poly.ComputerAlgebra.inverseRealWitnessIndependent
#assert_no_axioms FX1Poly.ComputerAlgebra.inverseRealOfApartnessCongr
#assert_no_axioms FX1Poly.ComputerAlgebra.inverseRealOfApartnessWitnessIndependent
#assert_no_axioms FX1Poly.ComputerAlgebra.inverseComplexCongr
#assert_no_axioms FX1Poly.ComputerAlgebra.inverseComplexWitnessIndependent

end FX1PolyAudit
