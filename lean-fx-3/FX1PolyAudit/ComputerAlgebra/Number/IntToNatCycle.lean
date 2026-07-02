import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.IntToNatCycle

/-! # FX1PolyAudit/ComputerAlgebra/Number/IntToNatCycle — zero-axiom gate
    (FLOAT-2 brick 4a)

Per-declaration zero-axiom gate for the clamped-gap cycle-balance kit: the `toNat`
computation pins (promoted here from the RadixScaledInteger carrier), the positive-part
decomposition, the four-term AC exchange, the gap-cycle telescope, and the cycle
balance itself.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.intToNatOfNat
#assert_no_axioms FX1Poly.ComputerAlgebra.intToNatNegOfNat
#assert_no_axioms FX1Poly.ComputerAlgebra.intOfNatToNatDecomposition
#assert_no_axioms FX1Poly.ComputerAlgebra.intAddSwapMiddle
#assert_no_axioms FX1Poly.ComputerAlgebra.intGapCycleTelescopes
#assert_no_axioms FX1Poly.ComputerAlgebra.intToNatCycleBalance
#assert_no_axioms FX1Poly.ComputerAlgebra.intSplitClampsBalance

end FX1PolyAudit
