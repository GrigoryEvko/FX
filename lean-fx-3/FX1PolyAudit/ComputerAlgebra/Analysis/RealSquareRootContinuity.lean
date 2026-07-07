import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Analysis.RealSquareRootContinuity

/-! # FX1PolyAudit/ComputerAlgebra/Analysis/RealSquareRootContinuity — zero-axiom
    gate (ANALYSIS-SQRTCONT-1)

Per-declaration zero-axiom gate for real square-root continuity: the three-term
sum-of-squares drop, the slack-carrying Hölder-1/2 difference bound (the
shrinking->fixed rework), the partial-map uniform-continuity predicate, and the
quadratic-modulus uniform continuity of `sqrtReal`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.sumThreeSquaresLeSquareSumNonNeg
#assert_no_axioms FX1Poly.ComputerAlgebra.sqrtApproxPairDifferenceBoundedWithSlack
#assert_no_axioms FX1Poly.ComputerAlgebra.IsUniformlyContinuousOnNonNeg
#assert_no_axioms FX1Poly.ComputerAlgebra.sqrtRealIsUniformlyContinuous

end FX1PolyAudit
