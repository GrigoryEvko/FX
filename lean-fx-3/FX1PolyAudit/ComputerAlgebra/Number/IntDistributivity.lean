import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.IntDistributivity

/-! # FX1PolyAudit/ComputerAlgebra/Number/IntDistributivity — zero-axiom gate (FLOAT-1 brick 4)

Per-declaration zero-axiom gate for the `negOfNat` addition kit, the mul-over-`subNatNat`
bridges, and hand-rolled `Int` distributivity.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.intNegOfNatEqSubNatNatZero
#assert_no_axioms FX1Poly.ComputerAlgebra.intOfNatAddNegOfNat
#assert_no_axioms FX1Poly.ComputerAlgebra.intNegOfNatAddOfNat
#assert_no_axioms FX1Poly.ComputerAlgebra.intNegOfNatAddNegOfNat
#assert_no_axioms FX1Poly.ComputerAlgebra.intOfNatMulSubNatNat
#assert_no_axioms FX1Poly.ComputerAlgebra.intNegSuccMulSubNatNat
#assert_no_axioms FX1Poly.ComputerAlgebra.intLeftDistrib
#assert_no_axioms FX1Poly.ComputerAlgebra.intRightDistrib

end FX1PolyAudit
