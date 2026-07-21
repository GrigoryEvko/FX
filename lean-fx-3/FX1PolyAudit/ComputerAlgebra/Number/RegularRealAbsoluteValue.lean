import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.RegularRealAbsoluteValue

/-! # FX1PolyAudit/ComputerAlgebra/Number/RegularRealAbsoluteValue — zero-axiom
    gate for the real absolute value

Per-declaration zero-axiom gate for the real absolute value `absReal x = √(x²)`
and its core order/setoid theory: nonnegativity, the `x ≤ |x|` / `-x ≤ |x|`
bounds, setoid congruence, and the real triangle inequality `absRealSubAdditive`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.absReal
#assert_no_axioms FX1Poly.ComputerAlgebra.absRealNonNegative
#assert_no_axioms FX1Poly.ComputerAlgebra.selfLeAbsReal
#assert_no_axioms FX1Poly.ComputerAlgebra.negSelfLeAbsReal
#assert_no_axioms FX1Poly.ComputerAlgebra.absRealRespectsDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.absRealSubAdditive
#assert_no_axioms FX1Poly.ComputerAlgebra.absRealNegReal
#assert_no_axioms FX1Poly.ComputerAlgebra.absRealReverseTriangle
#assert_no_axioms FX1Poly.ComputerAlgebra.zeroRationalIsNonNegative
#assert_no_axioms FX1Poly.ComputerAlgebra.constantRealIsNonNegativeRealOfNonNegative
#assert_no_axioms FX1Poly.ComputerAlgebra.absRealOfNonNegDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.absRealMulConstantNonNeg
#assert_no_axioms FX1Poly.ComputerAlgebra.fxRegularReal_hasRealAbsoluteValue

end FX1PolyAudit
