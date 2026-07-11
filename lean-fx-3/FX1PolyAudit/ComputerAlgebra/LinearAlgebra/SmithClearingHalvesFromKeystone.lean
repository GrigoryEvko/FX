import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithClearingHalvesFromKeystone

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithClearingHalvesFromKeystone — zero-axiom gate
    (H2-SMITH r28, #2261 — both r27 clearing-sweep residuals VANISH into the shipped keystone)

Per-declaration zero-axiom gate for the r28 detour-retirement: K2 vanishing
(`clearingOutputOffDiagonalDividesOfKeystone`), the find-`none` mirror
(`smithFindNonDividingLaterDiagonalNoneOfAllDivide`), the encode bridge (`smithPivotDividesEntryEncode`,
converse of the shipped decode), K1 vanishing (`clearingOutputFindNoneOfKeystone`), and the collapse to the
keystone via the r27 halves (`smithReduceCompleteDriverOfKeystoneViaHalves`).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`.  Both the fuel-based `#assert_no_axioms` AND the independent (non-fuel) `#print axioms` are run on
every declaration (the project macro is fuel-based — not trusted alone). -/

namespace FX1PolyAudit

/- Brick 1 — K2 vanishes into the keystone's off-diagonal slice. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.clearingOutputOffDiagonalDividesOfKeystone

/- Brick 2a — the find-`none` mirror (structural on the scan count). -/
#assert_no_axioms FX1Poly.ComputerAlgebra.smithFindNonDividingLaterDiagonalNoneOfAllDivide

/- Brick 2b — the encode bridge (converse of the shipped decode). -/
#assert_no_axioms FX1Poly.ComputerAlgebra.smithPivotDividesEntryEncode

/- Brick 2c — K1 vanishes into the keystone's diagonal reading. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.clearingOutputFindNoneOfKeystone

/- Brick 3 — the collapse: the driver from the keystone via the r27 halves. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.smithReduceCompleteDriverOfKeystoneViaHalves

-- Independent (non-fuel) axiom prints on every declaration.
#print axioms FX1Poly.ComputerAlgebra.clearingOutputOffDiagonalDividesOfKeystone
#print axioms FX1Poly.ComputerAlgebra.smithFindNonDividingLaterDiagonalNoneOfAllDivide
#print axioms FX1Poly.ComputerAlgebra.smithPivotDividesEntryEncode
#print axioms FX1Poly.ComputerAlgebra.clearingOutputFindNoneOfKeystone
#print axioms FX1Poly.ComputerAlgebra.smithReduceCompleteDriverOfKeystoneViaHalves

end FX1PolyAudit
