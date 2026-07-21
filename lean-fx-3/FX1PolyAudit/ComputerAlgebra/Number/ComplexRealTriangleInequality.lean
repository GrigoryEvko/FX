import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.ComplexRealTriangleInequality

/-! # FX1PolyAudit/ComputerAlgebra/Number/ComplexRealTriangleInequality — zero-axiom gate

Per-declaration zero-axiom gate for the ℂ modulus triangle inequality: the ℚ-level
reflection lemmas and the reflection step, the square-root order reflection
(`realLeOfSquareLeNonNeg`) and its corollaries (`nonNegSquareOrderReflect`,
`sqrtRealMonotone`, `leSqrtOfSquareLe`, `selfLeSqrtRealSquare`), the Cauchy–Schwarz
inequality with its real ring lemmas, the transitivity and additivity lemmas, and
`modulusTriangleInequality` itself.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.negExactZeroDenotesZero
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.lessEqualAsNegRightOfAddNonNeg
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.addNonNegOfLessEqualAsNegRight
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.reflectBridgeIdentity
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.orderReflectStep
#assert_no_axioms FX1Poly.ComputerAlgebra.realLeOfSquareLeNonNeg
#assert_no_axioms FX1Poly.ComputerAlgebra.nonNegSquareOrderReflect
#assert_no_axioms FX1Poly.ComputerAlgebra.sqrtRealMonotone
#assert_no_axioms FX1Poly.ComputerAlgebra.leSqrtOfSquareLe
#assert_no_axioms FX1Poly.ComputerAlgebra.selfLeSqrtRealSquare
#assert_no_axioms FX1Poly.ComputerAlgebra.mulRealNegNegDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.subRealAddLeftCancelDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.realVanishingLowerBoundOfNonNeg
#assert_no_axioms FX1Poly.ComputerAlgebra.cauchySchwarzReal
#assert_no_axioms FX1Poly.ComputerAlgebra.squareSumExpand
#assert_no_axioms FX1Poly.ComputerAlgebra.realVanishingLowerBoundAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.subRealChainDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.lessEqualRealTrans
#assert_no_axioms FX1Poly.ComputerAlgebra.lessEqualRealAddCompatLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.modulusTriangleInequality
#assert_no_axioms FX1Poly.ComputerAlgebra.fxComplexReal_hasModulusTriangleInequality

end FX1PolyAudit
