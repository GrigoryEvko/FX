import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.IntNegation

/-! # FX1PolyAudit/ComputerAlgebra/Number/IntNegation — zero-axiom gate (FLOAT-1 brick 6)

Per-declaration zero-axiom gate for the hand-rolled negation-vs-add/mul relations and
their `negOfNat`/`subNatNat` helpers.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.intNegNegOfNat
#assert_no_axioms FX1Poly.ComputerAlgebra.intNegSubNatNat
#assert_no_axioms FX1Poly.ComputerAlgebra.intNegAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.intNegMul
#assert_no_axioms FX1Poly.ComputerAlgebra.intMulNeg

end FX1PolyAudit
