import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithReachableKeystoneReduction

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithReachableKeystoneReduction — zero-axiom gate
    (H2-SMITH r37 — the reachable seed retired to the reachable keystone / gcd scalar)

Per-declaration zero-axiom gate for the NODE 2 assembly: `seedReachableOfLandedPivotDividesMinorReachable`
(the reachable KEYSTONE ⟹ the reachable SEED, byte-parallel of `seedOfLandedPivotDividesMinor` under the
reachability witness), `smithReduceCompleteDriverOfLandedPivotDividesMinorReachable` (the corrected-driver
totality on the reachable keystone alone), `keystoneReachableIffLandedDividesMinorGcdReachable` (the reachable
keystone ⟺ the crisp reachable scalar `landed ∣ gcd(minor)`, byte-parallel of
`keystoneIffLandedDividesMinorGcd`), and `smithReduceCompleteDriverOfLandedDividesMinorGcdReachable` (the
corrected-driver totality on the crispest reachable residual — the exact remaining leg).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`.  Both the fuel-based `#assert_no_axioms` AND the independent (non-fuel) `#print axioms` are run on
every declaration (the project macro is fuel-based — not trusted alone). -/

namespace FX1PolyAudit

/- The NODE 2 assembly: reduction, keystone driver, iff, and the crisp-scalar driver. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.seedReachableOfLandedPivotDividesMinorReachable
#assert_no_axioms FX1Poly.ComputerAlgebra.smithReduceCompleteDriverOfLandedPivotDividesMinorReachable
#assert_no_axioms FX1Poly.ComputerAlgebra.keystoneReachableIffLandedDividesMinorGcdReachable
#assert_no_axioms FX1Poly.ComputerAlgebra.smithReduceCompleteDriverOfLandedDividesMinorGcdReachable

-- Independent (non-fuel) axiom prints on every declaration.
#print axioms FX1Poly.ComputerAlgebra.seedReachableOfLandedPivotDividesMinorReachable
#print axioms FX1Poly.ComputerAlgebra.smithReduceCompleteDriverOfLandedPivotDividesMinorReachable
#print axioms FX1Poly.ComputerAlgebra.keystoneReachableIffLandedDividesMinorGcdReachable
#print axioms FX1Poly.ComputerAlgebra.smithReduceCompleteDriverOfLandedDividesMinorGcdReachable

end FX1PolyAudit
