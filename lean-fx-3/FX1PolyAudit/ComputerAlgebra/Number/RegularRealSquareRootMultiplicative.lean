import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.RegularRealSquareRootMultiplicative

/-! # FX1PolyAudit/ComputerAlgebra/Number/RegularRealSquareRootMultiplicative —
    zero-axiom gate

Per-declaration zero-axiom gate for `sqrt` multiplicativity on nonnegative Bishop
reals: the rational quadratic estimate (`squareZeroImpliesZero`), the
difference-of-squares reduction and its ring lemmas, the equal-nonnegative-squares
cancellation crux, and the headline `sqrtRealMulDenotesSame`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.ratioTwoLeReciprocalSquare
#assert_no_axioms FX1Poly.ComputerAlgebra.subExactZeroRightDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.subExactZeroLeftDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.subExactNegRightDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.mulExactNegNegDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.natSlackLeRadicand
#assert_no_axioms FX1Poly.ComputerAlgebra.mulRealPreservesIsNonNegativeReal
#assert_no_axioms FX1Poly.ComputerAlgebra.sqrtRealIsNonNegativeReal
#assert_no_axioms FX1Poly.ComputerAlgebra.squareZeroImpliesZero
#assert_no_axioms FX1Poly.ComputerAlgebra.nonNegNonPosSetoidImpliesZero
#assert_no_axioms FX1Poly.ComputerAlgebra.subRealSelfDenotesZero
#assert_no_axioms FX1Poly.ComputerAlgebra.negRealAddSelfDenotesZero
#assert_no_axioms FX1Poly.ComputerAlgebra.negRealConstantZeroDenotesZero
#assert_no_axioms FX1Poly.ComputerAlgebra.denotesSameRealOfSubRealZero
#assert_no_axioms FX1Poly.ComputerAlgebra.denotesSameRealNegOfAddRealZero
#assert_no_axioms FX1Poly.ComputerAlgebra.mulRealMedial
#assert_no_axioms FX1Poly.ComputerAlgebra.mulRealDiffSquaresDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.nonNegSquareCancel
#assert_no_axioms FX1Poly.ComputerAlgebra.sqrtRealMulDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.fxRegularReal_hasSquareRootMultiplicativity

end FX1PolyAudit
