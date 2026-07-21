import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Analysis.RealLimit

/-! # FX1PolyAudit/ComputerAlgebra/Analysis/RealLimit — zero-axiom gate

Per-declaration zero-axiom gate for modulus-based real-sequence
convergence: the Nat monotonicity shims, the real-level bound relaxation
and congruence, `ConvergesTo`, the constant/diagonal convergences,
modulus-form limit uniqueness, and the sum/negation limit laws with their
real-level bound-respecting lemmas.

Every declaration must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.natSelfLeAddRight
#assert_no_axioms FX1Poly.ComputerAlgebra.natSelfLeAddLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.isWithinRealBoundOfBoundLessEqual
#assert_no_axioms FX1Poly.ComputerAlgebra.isWithinRealBoundCongrBound
#assert_no_axioms FX1Poly.ComputerAlgebra.ConvergesTo
#assert_no_axioms FX1Poly.ComputerAlgebra.convergesToConstant
#assert_no_axioms FX1Poly.ComputerAlgebra.convergesToLimitReal
#assert_no_axioms FX1Poly.ComputerAlgebra.denotesSameRealOfConvergesToBoth
#assert_no_axioms FX1Poly.ComputerAlgebra.addRealRespectsIsWithinRealBound
#assert_no_axioms FX1Poly.ComputerAlgebra.convergesToAddReal
#assert_no_axioms FX1Poly.ComputerAlgebra.negRealRespectsIsWithinRealBound
#assert_no_axioms FX1Poly.ComputerAlgebra.convergesToNegReal
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.nonNegLimitTailCollapses
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.nonNegLimitTailCollapsesShaped
#assert_no_axioms FX1Poly.ComputerAlgebra.realNonNegativeOfConvergesTo
#assert_no_axioms FX1Poly.ComputerAlgebra.lessEqualRealOfConvergesTo

end FX1PolyAudit
