import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntUnivariatePolynomial

/-! # FX1PolyAudit/.../IntUnivariatePolynomial — zero-axiom gate

Per-declaration zero-axiom gate for the ℤ[x] substrate: the ascending-coefficient-list operations
(`polyAdd`/`polyScale`/`polyMul`/`polyEval`), the evaluation ring homomorphism
(`polyEvalAdd`/`polyEvalScale`/`polyEvalMul`, the last being discrete-convolution correctness of `polyMul`),
negation/subtraction, the linear factor and factor theorem, composition, powers, the semantic ring laws,
and monomials.  Every operation is structural on the coefficient list; corpus `Int` lemmas.  Free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.polyAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.polyScale
#assert_no_axioms FX1Poly.ComputerAlgebra.polyMul
#assert_no_axioms FX1Poly.ComputerAlgebra.polyEval
#assert_no_axioms FX1Poly.ComputerAlgebra.intAddInterchange
#assert_no_axioms FX1Poly.ComputerAlgebra.polyEvalAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.polyEvalScale
#assert_no_axioms FX1Poly.ComputerAlgebra.polyEvalMul
#assert_no_axioms FX1Poly.ComputerAlgebra.polyNeg
#assert_no_axioms FX1Poly.ComputerAlgebra.polySub
#assert_no_axioms FX1Poly.ComputerAlgebra.polyEvalNeg
#assert_no_axioms FX1Poly.ComputerAlgebra.polyEvalSub
#assert_no_axioms FX1Poly.ComputerAlgebra.polyLinearFactor
#assert_no_axioms FX1Poly.ComputerAlgebra.polyEvalOne
#assert_no_axioms FX1Poly.ComputerAlgebra.polyEvalLinearFactor
#assert_no_axioms FX1Poly.ComputerAlgebra.polyLinearFactorVanishesAtRoot
#assert_no_axioms FX1Poly.ComputerAlgebra.polyLinearFactorRootAnnihilatesMultiple
#assert_no_axioms FX1Poly.ComputerAlgebra.polyEvalConstant
#assert_no_axioms FX1Poly.ComputerAlgebra.polyCompose
#assert_no_axioms FX1Poly.ComputerAlgebra.polyEvalCompose
#assert_no_axioms FX1Poly.ComputerAlgebra.polyPow
#assert_no_axioms FX1Poly.ComputerAlgebra.polyEvalPow
#assert_no_axioms FX1Poly.ComputerAlgebra.polyEvalMulComm
#assert_no_axioms FX1Poly.ComputerAlgebra.polyEvalMulAssoc
#assert_no_axioms FX1Poly.ComputerAlgebra.polyMonomial
#assert_no_axioms FX1Poly.ComputerAlgebra.polyEvalMonomial
#assert_no_axioms FX1Poly.ComputerAlgebra.polyMulDifferenceOfSquaresExample
#assert_no_axioms FX1Poly.ComputerAlgebra.polyEvalDifferenceOfSquaresAtThree
#assert_no_axioms FX1Poly.ComputerAlgebra.polyEvalMulGroundingAtFive
#assert_no_axioms FX1Poly.ComputerAlgebra.polySubCancelsLinearTermExample
#assert_no_axioms FX1Poly.ComputerAlgebra.polyEvalSubGroundingAtFive
#assert_no_axioms FX1Poly.ComputerAlgebra.polyLinearFactorProductExample
#assert_no_axioms FX1Poly.ComputerAlgebra.polyLinearFactorProductVanishesAtTwo
#assert_no_axioms FX1Poly.ComputerAlgebra.polyLinearFactorProductVanishesAtFive
#assert_no_axioms FX1Poly.ComputerAlgebra.polyComposeConstantExample
#assert_no_axioms FX1Poly.ComputerAlgebra.polyEvalComposeGroundingAtTwo
#assert_no_axioms FX1Poly.ComputerAlgebra.polyEvalPowGroundingCube
#assert_no_axioms FX1Poly.ComputerAlgebra.polyEvalPowGroundingBinomial
#assert_no_axioms FX1Poly.ComputerAlgebra.polyMonomialExample
#assert_no_axioms FX1Poly.ComputerAlgebra.polyEvalMonomialGrounding

end FX1PolyAudit
