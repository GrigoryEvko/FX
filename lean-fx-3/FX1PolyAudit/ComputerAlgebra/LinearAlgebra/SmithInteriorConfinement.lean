import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithInteriorConfinement

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithInteriorConfinement — zero-axiom gate
    (H2-SMITH r26, #2261 — the keystone-survives-interior-fill-in adjudication)

Per-declaration zero-axiom gate for the NODE-2 witnesses (the pivot-`1` clearing sweep of
`diag(1, -12, -18, 10)` lands `g = 2 > 1`, fills the interior off-diagonal cell `(3, 2) = -90`, and `g`
divides that fill-in and every other window cell) and the general confinement projection
`landedPivotDividesInteriorOfOutputMinorDivides` (the keystone confines every interior cell to the landed
pivot's ideal).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`.  Both the fuel-based `#assert_no_axioms` AND the independent (non-fuel)
`#print axioms` are run on every declaration (the project macro is fuel-based — not trusted alone). -/

namespace FX1PolyAudit

/- The NODE-2 concrete witnesses (kernel-checked, at the 4x4 defeq ceiling). -/
#assert_no_axioms FX1Poly.ComputerAlgebra.smithClearingSweepLandsFillInWindowOutput
#assert_no_axioms FX1Poly.ComputerAlgebra.smithClearingSweepLandsPivotTwoOnFillInWindow
#assert_no_axioms FX1Poly.ComputerAlgebra.smithClearingSweepFillsInteriorOnFillInWindow
#assert_no_axioms FX1Poly.ComputerAlgebra.smithLandedPivotExactlyDividesInteriorFillIn
#assert_no_axioms FX1Poly.ComputerAlgebra.smithLandedPivotDividesEveryFillInWindowCell

/- The general confinement projection (conditional on the open keystone). -/
#assert_no_axioms FX1Poly.ComputerAlgebra.landedPivotDividesInteriorOfOutputMinorDivides

-- Independent (non-fuel) axiom prints on every declaration.
#print axioms FX1Poly.ComputerAlgebra.smithClearingSweepLandsFillInWindowOutput
#print axioms FX1Poly.ComputerAlgebra.smithClearingSweepLandsPivotTwoOnFillInWindow
#print axioms FX1Poly.ComputerAlgebra.smithClearingSweepFillsInteriorOnFillInWindow
#print axioms FX1Poly.ComputerAlgebra.smithLandedPivotExactlyDividesInteriorFillIn
#print axioms FX1Poly.ComputerAlgebra.smithLandedPivotDividesEveryFillInWindowCell
#print axioms FX1Poly.ComputerAlgebra.landedPivotDividesInteriorOfOutputMinorDivides

end FX1PolyAudit
