import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithReachableMagnitudeResidual

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithReachableMagnitudeResidual — zero-axiom gate
    (H2-SMITH r38 — the reachable leg sharpened to a decidable `Nat` magnitude equality)

Per-declaration zero-axiom gate for the r38 magnitude-residual assembly:
`landedDividesMinorGcdReachableOfAbsEq` (the zero-safe forward bridge `|landed| = |gcd| ⟹ landed ∣ gcd`,
via the shipped `dividesExactlyOfNatAbsEq`), `landedAbsEqMinorGcdReachableOfDivides` (the antisymmetry
converse via `minorGcdDividesLanded` + `natDividesAntisymm`), `landedDividesMinorGcdReachableIffAbsEq` (the
two-way equivalence certifying the magnitude residual is the r37 leg faithfully restated), and
`smithReduceCompleteDriverOfLandedAbsEqMinorGcdReachable` (the corrected-driver totality on the magnitude
residual alone — the exact remaining leg in its crispest arithmetic form).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`.  Both the fuel-based `#assert_no_axioms` AND the independent (non-fuel) `#print axioms` are run on
every declaration (the project macro is fuel-based — not trusted alone). -/

namespace FX1PolyAudit

/- The r38 assembly: forward bridge, antisymmetry converse, equivalence, and the magnitude-residual driver. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.landedDividesMinorGcdReachableOfAbsEq
#assert_no_axioms FX1Poly.ComputerAlgebra.landedAbsEqMinorGcdReachableOfDivides
#assert_no_axioms FX1Poly.ComputerAlgebra.landedDividesMinorGcdReachableIffAbsEq
#assert_no_axioms FX1Poly.ComputerAlgebra.smithReduceCompleteDriverOfLandedAbsEqMinorGcdReachable

-- Independent (non-fuel) axiom prints on every declaration.
#print axioms FX1Poly.ComputerAlgebra.landedDividesMinorGcdReachableOfAbsEq
#print axioms FX1Poly.ComputerAlgebra.landedAbsEqMinorGcdReachableOfDivides
#print axioms FX1Poly.ComputerAlgebra.landedDividesMinorGcdReachableIffAbsEq
#print axioms FX1Poly.ComputerAlgebra.smithReduceCompleteDriverOfLandedAbsEqMinorGcdReachable

end FX1PolyAudit
