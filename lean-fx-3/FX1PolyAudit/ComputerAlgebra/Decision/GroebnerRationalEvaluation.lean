import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Decision.GroebnerRationalEvaluation

/-! # FX1PolyAudit/ComputerAlgebra/Decision/GroebnerRationalEvaluation — zero-axiom gate
    (ℚ evaluation layer: the common-zero grounding of ideal membership)

Per-declaration zero-axiom gate for the ℚ Gröbner evaluation homomorphism layer that
grounds the certificate route semantically: the canonical power `qnfPow` with the
power homomorphism `qnfPowAdd` (the bill the `grq` brick deferred), `qnfPowOne`,
`qnfOnePow`, and the product power `qnfMulPow` telescoped through the two reusable
rearrangers `qnfMulSwapLeft`/`qnfMulExchange`; monomial evaluation over a
`List QnfRat` environment (`greEnvLookup`/`greEvalVarPower`/`greEvalExp`) with the
exponent-multiplication homomorphism `greEvalExpMul` (via `greEvalExpInsert`);
polynomial evaluation `greEvalPoly` with the ring homomorphisms
`greEvalAdd`/`greEvalScaleTerm`/`greEvalMul`/`greEvalSumOfProducts` (through the
insert-fold workhorse `greEvalPolyTermInsert` and the dot product `greEvalDotProduct`);
THE GROUNDING `greCommonZeroOfIdealMember` (ideal members vanish at every common zero
of the generators); the closed kernel-`rfl` fires (`2^3 = 8`, `(1/2)^2 = 1/4`,
`x^2 - 1` at `3` is `8`, the two-variable eval, and the T4-consuming certificate fire
`greFireXSquaredMinusOneVanishesAtOne`); and the DECIDED markers
`greHasEvaluationHomomorphism` / `greHasCommonZeroGrounding`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.qnfPow
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfPowZero
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfPowSucc
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfMulSwapLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfPowAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfPowOne
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfOnePow
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfMulExchange
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfMulPow
#assert_no_axioms FX1Poly.ComputerAlgebra.greEnvLookup
#assert_no_axioms FX1Poly.ComputerAlgebra.greEvalVarPower
#assert_no_axioms FX1Poly.ComputerAlgebra.greEvalExp
#assert_no_axioms FX1Poly.ComputerAlgebra.greEvalExpInsert
#assert_no_axioms FX1Poly.ComputerAlgebra.greEvalExpMul
#assert_no_axioms FX1Poly.ComputerAlgebra.greEvalPoly
#assert_no_axioms FX1Poly.ComputerAlgebra.greEvalPolyTermInsert
#assert_no_axioms FX1Poly.ComputerAlgebra.greEvalAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.greEvalScaleTerm
#assert_no_axioms FX1Poly.ComputerAlgebra.greEvalMul
#assert_no_axioms FX1Poly.ComputerAlgebra.greEvalDotProduct
#assert_no_axioms FX1Poly.ComputerAlgebra.greEvalSumOfProducts
#assert_no_axioms FX1Poly.ComputerAlgebra.greCommonZeroOfIdealMember
#assert_no_axioms FX1Poly.ComputerAlgebra.greFirePowTwoCubed
#assert_no_axioms FX1Poly.ComputerAlgebra.greFirePowOneHalfSquared
#assert_no_axioms FX1Poly.ComputerAlgebra.greFireXSquaredMinusOneAtThree
#assert_no_axioms FX1Poly.ComputerAlgebra.greFireXMinusOneVanishesAtOne
#assert_no_axioms FX1Poly.ComputerAlgebra.greFireSingletonGeneratorVanishes
#assert_no_axioms FX1Poly.ComputerAlgebra.greFireXSquaredMinusOneVanishesAtOne
#assert_no_axioms FX1Poly.ComputerAlgebra.greFireTwoVariableEval
#assert_no_axioms FX1Poly.ComputerAlgebra.greHasEvaluationHomomorphism
#assert_no_axioms FX1Poly.ComputerAlgebra.greHasCommonZeroGrounding

end FX1PolyAudit
