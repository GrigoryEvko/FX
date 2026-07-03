import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.RegularRealCompleteness

/-! # FX1PolyAudit/ComputerAlgebra/Number/RegularRealCompleteness — zero-axiom
    gate (NUM-R-6b/6c)

Per-declaration zero-axiom gate for the diagonal limit: the
quarter-scaled sampling depth, the regular-Cauchy-sequence structure,
`limitReal` itself, and the exactly-tight convergence theorem.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.diagonalSamplingIndex
#assert_no_axioms FX1Poly.ComputerAlgebra.RegularRealSequence
#assert_no_axioms FX1Poly.ComputerAlgebra.RegularRealSequence.mk
#assert_no_axioms FX1Poly.ComputerAlgebra.limitReal
#assert_no_axioms FX1Poly.ComputerAlgebra.sequenceConvergesToLimitReal

end FX1PolyAudit
