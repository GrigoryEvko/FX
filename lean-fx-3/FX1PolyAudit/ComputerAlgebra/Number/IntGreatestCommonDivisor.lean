import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.IntGreatestCommonDivisor

/-! # Zero-axiom gate for `IntGreatestCommonDivisor`

Per-declaration zero-axiom gate for the signed integer gcd: the `IntDivides` predicate, the
`natAbs` sign bridges, and the `intGcd` divides/greatest/commutativity certificates. Every
declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, and `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.IntDivides
#assert_no_axioms FX1Poly.ComputerAlgebra.intDividesRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.intDividesZero
#assert_no_axioms FX1Poly.ComputerAlgebra.natAbsNegOfNat
#assert_no_axioms FX1Poly.ComputerAlgebra.intNatAbsMul
#assert_no_axioms FX1Poly.ComputerAlgebra.intDividesOfNatDividesNatAbs
#assert_no_axioms FX1Poly.ComputerAlgebra.natDividesNatAbsOfIntDivides
#assert_no_axioms FX1Poly.ComputerAlgebra.intDividesOfNatAbsDivides
#assert_no_axioms FX1Poly.ComputerAlgebra.intGcd
#assert_no_axioms FX1Poly.ComputerAlgebra.intGcdIsNonnegative
#assert_no_axioms FX1Poly.ComputerAlgebra.intGcdDividesLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.intGcdDividesRight
#assert_no_axioms FX1Poly.ComputerAlgebra.intGcdGreatest
#assert_no_axioms FX1Poly.ComputerAlgebra.intGcdComm

end FX1PolyAudit
