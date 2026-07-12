import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithSubBlockContentInvariantProof

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithSubBlockContentInvariantProof — zero-axiom gate
    (H2-SMITH r43, #2261 — the recorded across-rounds content carrier proven generally)

Per-declaration zero-axiom gate for the r43 general proof of `SmithSubBlockContentStableAcrossRound`:
the pivot-in-range recovery (N1), the minor-gcd nonnegativity (N2), the nonneg-natAbs `Int` equality
(N3), the reusable two-tower ideal-preservation core, and the main theorem.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`.  Both the fuel-based `#assert_no_axioms` AND the independent (non-fuel)
`#print axioms` are run on every declaration (the project macro is fuel-based — not trusted alone). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.smithFindSomeImpliesPivotInRange
#assert_no_axioms FX1Poly.ComputerAlgebra.minorGcdRowsNonneg
#assert_no_axioms FX1Poly.ComputerAlgebra.minorGcdWithinNonneg
#assert_no_axioms FX1Poly.ComputerAlgebra.intEqOfNonnegOfNatAbsEq
#assert_no_axioms FX1Poly.ComputerAlgebra.minorGcdStableUnderBoundedWord
#assert_no_axioms FX1Poly.ComputerAlgebra.smithSubBlockContentStableAcrossRoundHolds

-- Independent (non-fuel) axiom prints on every declaration.
#print axioms FX1Poly.ComputerAlgebra.smithFindSomeImpliesPivotInRange
#print axioms FX1Poly.ComputerAlgebra.minorGcdRowsNonneg
#print axioms FX1Poly.ComputerAlgebra.minorGcdWithinNonneg
#print axioms FX1Poly.ComputerAlgebra.intEqOfNonnegOfNatAbsEq
#print axioms FX1Poly.ComputerAlgebra.minorGcdStableUnderBoundedWord
#print axioms FX1Poly.ComputerAlgebra.smithSubBlockContentStableAcrossRoundHolds

end FX1PolyAudit
