import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.NatGreatestCommonDivisor

/-! # Zero-axiom gate for `NatGreatestCommonDivisor`

Per-declaration zero-axiom gate for the counting-Euclid gcd: the explicit-witness
divisibility kit, the fuel-structural algorithm, the joint divides certificate, the
canonical-fuel wrappers, the Bezout identity, and greatest-ness. Every declaration must
be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, and
`omega`. -/

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
#assert_no_axioms FX1Poly.ComputerAlgebra.natDividesMulLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.natDividesAddCancelLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.NatBezoutIdentityFor
#assert_no_axioms FX1Poly.ComputerAlgebra.natGcdWithFuelBezout
#assert_no_axioms FX1Poly.ComputerAlgebra.natGcdBezout
#assert_no_axioms FX1Poly.ComputerAlgebra.natDividesGcdOfDividesBoth
#assert_no_axioms FX1Poly.ComputerAlgebra.natDividesRemainderIsZero
#assert_no_axioms FX1Poly.ComputerAlgebra.natExactQuotientReconstructs
#assert_no_axioms FX1Poly.ComputerAlgebra.natRightFactorOfSuccIsPositive
#assert_no_axioms FX1Poly.ComputerAlgebra.natExactQuotientIsPositive
#assert_no_axioms FX1Poly.ComputerAlgebra.NatCoprime
#assert_no_axioms FX1Poly.ComputerAlgebra.natDividesOfCoprimeOfDividesMul
#assert_no_axioms FX1Poly.ComputerAlgebra.natScaledDividesOfDividesQuotient
#assert_no_axioms FX1Poly.ComputerAlgebra.natLeftFactorOfProductEqOne
#assert_no_axioms FX1Poly.ComputerAlgebra.natGcdOfExactQuotientsIsOne
#assert_no_axioms FX1Poly.ComputerAlgebra.natDividesAntisymm
#assert_no_axioms FX1Poly.ComputerAlgebra.natGcdComm

end FX1PolyAudit
