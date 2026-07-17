import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.EndomorphismMinimalPolynomial

/-! # FX1PolyAudit/.../EndomorphismMinimalPolynomial — zero-axiom gate

Per-declaration zero-axiom gate for the minimal-polynomial annihilator separator (the top invariant factor,
partial delivery of `invariantFactorSeparator`, WP-ENDO #2255): the polynomial-at-matrix evaluation engine,
the decidable annihilation predicate, the Cayley–Hamilton groundings, the annihilator dissimilarity
separator, the char-poly-and-rank-blind separation, and the grounded census feed.

`matrixPolyEval` is structural over the shipped `endomorphismMatrixPower`; every check is `decide` over a
bounded `agreeOnWindow` ball with `Int.decEq`.  Must be free of `propext`, `Quot.sound`, `Classical`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.matrixPolyEvalFrom
#assert_no_axioms FX1Poly.ComputerAlgebra.matrixPolyEval
#assert_no_axioms FX1Poly.ComputerAlgebra.EndomorphismAnnihilates
#assert_no_axioms FX1Poly.ComputerAlgebra.intMulPowerLeftCancelOfMagnitude
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismWitnessUniformConjugation
#assert_no_axioms FX1Poly.ComputerAlgebra.addMatrixCongrOnWindow
#assert_no_axioms FX1Poly.ComputerAlgebra.intMatrixScaleOverAddOnWindow
#assert_no_axioms FX1Poly.ComputerAlgebra.intMatrixMulLeftDistribOnWindow
#assert_no_axioms FX1Poly.ComputerAlgebra.intMatrixMulRightDistribOnWindow
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismMatrixPowerColCount
#assert_no_axioms FX1Poly.ComputerAlgebra.matrixPolyEvalFromColCount
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismSandwichPowerEqScaledTarget
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismSandwichPolyEqScaledTarget
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismWitnessTransportsAnnihilation
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismRationalConjugacyTransportsMinimalPolynomial
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismCharPolyAnnihilatesTwoByTwo
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismCharPolyAnnihilatesThreeByThree
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismLinearAnnihilatesScalar
#assert_no_axioms FX1Poly.ComputerAlgebra.EndomorphismDissimilarByAnnihilator
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismScalarVersusJordanDissimilar
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismScalarVersusJordanShareCharPoly
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismScalarVersusJordanShareRank
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismJordanNilpotentDissimilarByMinPoly
#assert_no_axioms FX1Poly.ComputerAlgebra.walkingEndomorphismMinimalPolynomialGrounded
#assert_no_axioms FX1Poly.ComputerAlgebra.fxEndo_hasMinimalPolynomialAnnihilatorSeparator

end FX1PolyAudit
