import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithReachableMagnitudeWitnesses

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithReachableMagnitudeWitnesses — zero-axiom gate
    (H2-SMITH r38 — the residual body on the coverage-probe seeds + the K2 non-vacuity witness)

Per-declaration zero-axiom gate for the r38 witnesses battery: five `decide` pins of the residual body
`|landed| = gcd(minor)` on the coverage-probe decision seeds (the divisor-chain refuter `diag(100,75,30,14)`
headlined), plus the K2 non-vacuity witnesses (`pivotOneExitCarriesSurvivingInteriorFillIn`,
`pivotOneLandedDividesSurvivingInteriorFillIn`).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`.  Both the fuel-based `#assert_no_axioms` AND the independent (non-fuel) `#print axioms` are run on
every declaration (the project macro is fuel-based — not trusted alone). -/

namespace FX1PolyAudit

/- The residual body on the coverage-probe seeds. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.landedAbsEqMinorGcdOnDivisorChainRefuterSeed
#assert_no_axioms FX1Poly.ComputerAlgebra.landedAbsEqMinorGcdOnProbeSixTenEight
#assert_no_axioms FX1Poly.ComputerAlgebra.landedAbsEqMinorGcdOnProbeFifteenTenSixFour
#assert_no_axioms FX1Poly.ComputerAlgebra.landedAbsEqMinorGcdOnThirtyTwentyTwelve
#assert_no_axioms FX1Poly.ComputerAlgebra.landedAbsEqMinorGcdOnTwelveEighteenThirtyFortyTwo

/- The K2 non-vacuity witnesses (the double-sweep exit + the landed-pivot divisibility). -/
#assert_no_axioms FX1Poly.ComputerAlgebra.pivotOneExitCarriesSurvivingInteriorFillIn
#assert_no_axioms FX1Poly.ComputerAlgebra.pivotOneLandedDividesSurvivingInteriorFillIn

-- Independent (non-fuel) axiom prints on every declaration.
#print axioms FX1Poly.ComputerAlgebra.landedAbsEqMinorGcdOnDivisorChainRefuterSeed
#print axioms FX1Poly.ComputerAlgebra.landedAbsEqMinorGcdOnProbeSixTenEight
#print axioms FX1Poly.ComputerAlgebra.landedAbsEqMinorGcdOnProbeFifteenTenSixFour
#print axioms FX1Poly.ComputerAlgebra.landedAbsEqMinorGcdOnThirtyTwentyTwelve
#print axioms FX1Poly.ComputerAlgebra.landedAbsEqMinorGcdOnTwelveEighteenThirtyFortyTwo
#print axioms FX1Poly.ComputerAlgebra.pivotOneExitCarriesSurvivingInteriorFillIn
#print axioms FX1Poly.ComputerAlgebra.pivotOneLandedDividesSurvivingInteriorFillIn

end FX1PolyAudit
