import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.NatGreatestCommonDivisor

/-! # FX1PolyAudit/ComputerAlgebra/Number/NatGreatestCommonDivisor — zero-axiom
    gate (NUM-Q-4a)

Per-declaration zero-axiom gate for the counting-Euclid gcd: the
explicit-witness divisibility kit, the fuel-structural algorithm, the joint
divides certificate, and the canonical-fuel wrappers.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.NatDivides
#assert_no_axioms FX1Poly.ComputerAlgebra.natDividesZero
#assert_no_axioms FX1Poly.ComputerAlgebra.natDividesRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.natDividesOfEq
#assert_no_axioms FX1Poly.ComputerAlgebra.natDividesMulRight
#assert_no_axioms FX1Poly.ComputerAlgebra.natDividesAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.natDivisorOfSuccIsPositive
#assert_no_axioms FX1Poly.ComputerAlgebra.natGcdWithFuel
#assert_no_axioms FX1Poly.ComputerAlgebra.natGcdWithFuelDividesBoth
#assert_no_axioms FX1Poly.ComputerAlgebra.natGcd
#assert_no_axioms FX1Poly.ComputerAlgebra.natGcdZeroLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.natGcdDividesLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.natGcdDividesRight
#assert_no_axioms FX1Poly.ComputerAlgebra.natGcdOfSuccLeftIsPositive

end FX1PolyAudit
