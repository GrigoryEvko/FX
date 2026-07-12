import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithReachablePrefixConfinement

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithReachablePrefixConfinement — zero-axiom gate
    (H2-SMITH r36 — the confinement invariant of the reachable trajectory)

Per-declaration zero-axiom gate for the three trajectory results: `reachableImpliesRectangular`
(reachable ⟹ rectangular), `reachableImpliesPrefixSettled` (THE confinement invariant — the reachable
trajectory keeps the processed prefix `< pivotIndex` settled, the corrected `[pivotIndex, ·)²` form), and
`reachableAtMinIsWindowDiagonal` (the seed-free terminal corollary — reachable at `Nat.min` ⟹ fully
window-diagonal).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`.  Both the fuel-based `#assert_no_axioms` AND the independent (non-fuel) `#print axioms` are run on
every declaration (the project macro is fuel-based — not trusted alone). -/

namespace FX1PolyAudit

/- The three trajectory results. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.reachableImpliesRectangular
#assert_no_axioms FX1Poly.ComputerAlgebra.reachableImpliesPrefixSettled
#assert_no_axioms FX1Poly.ComputerAlgebra.reachableAtMinIsWindowDiagonal

-- Independent (non-fuel) axiom prints on every declaration.
#print axioms FX1Poly.ComputerAlgebra.reachableImpliesRectangular
#print axioms FX1Poly.ComputerAlgebra.reachableImpliesPrefixSettled
#print axioms FX1Poly.ComputerAlgebra.reachableAtMinIsWindowDiagonal

end FX1PolyAudit
