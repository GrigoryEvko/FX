import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.IntMulAssociativity

/-! # FX1PolyAudit/ComputerAlgebra/Number/IntMulAssociativity — zero-axiom gate
    (FLOAT-1 brick 5)

Per-declaration zero-axiom gate for the hand-rolled Nat/Int multiplication associativity
and the four mixed-sign mul helpers.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.natMulAssoc
#assert_no_axioms FX1Poly.ComputerAlgebra.intOfNatMulNegOfNat
#assert_no_axioms FX1Poly.ComputerAlgebra.intNegOfNatMulOfNat
#assert_no_axioms FX1Poly.ComputerAlgebra.intNegOfNatMulNegSucc
#assert_no_axioms FX1Poly.ComputerAlgebra.intNegSuccMulNegOfNat
#assert_no_axioms FX1Poly.ComputerAlgebra.intMulAssoc
#assert_no_axioms FX1Poly.ComputerAlgebra.intMulSwapMiddle

end FX1PolyAudit
