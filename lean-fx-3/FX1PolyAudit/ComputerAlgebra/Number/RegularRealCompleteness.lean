import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.RegularRealCompleteness

/-! # FX1PolyAudit/ComputerAlgebra/Number/RegularRealCompleteness — zero-axiom gate

Per-declaration zero-axiom gate for the diagonal limit: the
quarter-scaled sampling depth, the regular-Cauchy-sequence structure,
`limitReal` itself, the exactly-tight convergence theorem, and the
limit-uniqueness pair that closes completeness.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.diagonalSamplingIndex
#assert_no_axioms FX1Poly.ComputerAlgebra.RegularRealSequence
#assert_no_axioms FX1Poly.ComputerAlgebra.RegularRealSequence.mk
#assert_no_axioms FX1Poly.ComputerAlgebra.limitReal
#assert_no_axioms FX1Poly.ComputerAlgebra.sequenceConvergesToLimitReal
#assert_no_axioms FX1Poly.ComputerAlgebra.denotesSameRealOfSharedConvergence
#assert_no_axioms FX1Poly.ComputerAlgebra.limitRealIsTheUniqueLimit

end FX1PolyAudit
