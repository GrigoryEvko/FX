import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.IntMulAssociativity

/-! # Zero-axiom gate for `IntMulAssociativity`

Per-declaration zero-axiom gate for Nat/Int multiplication associativity and the four
mixed-sign mul helpers. Every declaration must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, and `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.natMulAssoc
#assert_no_axioms FX1Poly.ComputerAlgebra.intOfNatMulNegOfNat
#assert_no_axioms FX1Poly.ComputerAlgebra.intNegOfNatMulOfNat
#assert_no_axioms FX1Poly.ComputerAlgebra.intNegOfNatMulNegSucc
#assert_no_axioms FX1Poly.ComputerAlgebra.intNegSuccMulNegOfNat
#assert_no_axioms FX1Poly.ComputerAlgebra.intMulAssoc
#assert_no_axioms FX1Poly.ComputerAlgebra.intMulSwapMiddle
#assert_no_axioms FX1Poly.ComputerAlgebra.intMulRightComm

end FX1PolyAudit
