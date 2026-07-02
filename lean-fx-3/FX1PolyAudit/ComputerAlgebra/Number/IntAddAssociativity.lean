import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.IntAddAssociativity

/-! # FX1PolyAudit/ComputerAlgebra/Number/IntAddAssociativity — zero-axiom gate (FLOAT-1 brick 3)

Per-declaration zero-axiom gate for the four mixed-sign add bridges and hand-rolled
`Int` addition associativity.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.intOfNatAddSubNatNat
#assert_no_axioms FX1Poly.ComputerAlgebra.intSubNatNatAddOfNat
#assert_no_axioms FX1Poly.ComputerAlgebra.intNegSuccAddSubNatNat
#assert_no_axioms FX1Poly.ComputerAlgebra.intSubNatNatAddNegSucc
#assert_no_axioms FX1Poly.ComputerAlgebra.intAddAssoc

end FX1PolyAudit
