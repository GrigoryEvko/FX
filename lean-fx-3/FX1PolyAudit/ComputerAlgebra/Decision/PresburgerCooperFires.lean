import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Decision.PresburgerCooperFires

/-! # FX1PolyAudit/ComputerAlgebra/Decision/PresburgerCooperFires — zero-axiom
    gate (Cooper decision fires: the 2x = 1 integrality-gap separator both
    directly and through the lane translation path, the rational-relaxation
    companion pin, the divisibility fire, the two-quantifier fire, the
    negative control, and the negation-path fire — all kernel-decided `rfl`
    pins)

Every declaration must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.pcqFireTwoPivotTerm
#assert_no_axioms FX1Poly.ComputerAlgebra.pcqFirePivotTerm
#assert_no_axioms FX1Poly.ComputerAlgebra.pcqFireOuterPivotTerm
#assert_no_axioms FX1Poly.ComputerAlgebra.pcqFireOuterPivotPlusTwoTerm
#assert_no_axioms FX1Poly.ComputerAlgebra.pcqFireGapFormula
#assert_no_axioms FX1Poly.ComputerAlgebra.pcqFireGapDecidesFalse
#assert_no_axioms FX1Poly.ComputerAlgebra.pcqFireGapSystem
#assert_no_axioms FX1Poly.ComputerAlgebra.pcqFireGapSystemDecidesFalse
#assert_no_axioms FX1Poly.ComputerAlgebra.pcqFireGapRationallyFeasible
#assert_no_axioms FX1Poly.ComputerAlgebra.pcqFireDvdFormula
#assert_no_axioms FX1Poly.ComputerAlgebra.pcqFireDvdDecidesTrue
#assert_no_axioms FX1Poly.ComputerAlgebra.pcqFireTwoQuantFormula
#assert_no_axioms FX1Poly.ComputerAlgebra.pcqFireTwoQuantDecidesTrue
#assert_no_axioms FX1Poly.ComputerAlgebra.pcqFireEmptyWindowFormula
#assert_no_axioms FX1Poly.ComputerAlgebra.pcqFireEmptyWindowDecidesFalse
#assert_no_axioms FX1Poly.ComputerAlgebra.pcqFireNegatedGapDecidesTrue

end FX1PolyAudit
