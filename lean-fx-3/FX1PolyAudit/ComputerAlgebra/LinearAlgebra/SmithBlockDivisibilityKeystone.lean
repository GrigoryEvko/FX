import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithBlockDivisibilityKeystone

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithBlockDivisibilityKeystone — zero-axiom gate
    (H2-SMITH r44, #2261 — the keystone is STATE-LOCAL under whole-block divisibility; the OPERATIONAL
    landing condition is strictly weaker)

Per-declaration zero-axiom gate for the r44 block-divisibility keystone: the state-local keystone
`blockDivisibilityImpliesAbsEqMinorGcd`, its non-vacuity `unitPivotForcesBlockGcdOne`, the
driver-localized `landedDividesInputBlockImpliesAbsEqMinorGcd`, and the operational-landing insufficiency
certificate (`operationallyLandedYetMissesMinorGcd`, `offCrossEntryEscapesDiagonalFind`, and the second
anti-diagonal killer), together with the unit witness and both seed rectangularity facts.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`.  Both the fuel-based `#assert_no_axioms` AND the independent (non-fuel) `#print axioms` are run
on every declaration (the project macro is fuel-based — not trusted alone). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.oneDividesEntireBlock
#assert_no_axioms FX1Poly.ComputerAlgebra.blockDivisibilityImpliesAbsEqMinorGcd
#assert_no_axioms FX1Poly.ComputerAlgebra.unitPivotSeedIsRectangular
#assert_no_axioms FX1Poly.ComputerAlgebra.unitPivotForcesBlockGcdOne
#assert_no_axioms FX1Poly.ComputerAlgebra.landedDividesInputBlockImpliesAbsEqMinorGcd
#assert_no_axioms FX1Poly.ComputerAlgebra.operationallyLandedKillerSeedIsRectangular
#assert_no_axioms FX1Poly.ComputerAlgebra.operationallyLandedYetMissesMinorGcd
#assert_no_axioms FX1Poly.ComputerAlgebra.offCrossEntryEscapesDiagonalFind
#assert_no_axioms FX1Poly.ComputerAlgebra.operationallyLandedAntiDiagonalKillerSeedIsRectangular
#assert_no_axioms FX1Poly.ComputerAlgebra.antiDiagonalKillerOperationallyLandedYetMissesMinorGcd

-- Independent (non-fuel) axiom prints on every declaration.
#print axioms FX1Poly.ComputerAlgebra.oneDividesEntireBlock
#print axioms FX1Poly.ComputerAlgebra.blockDivisibilityImpliesAbsEqMinorGcd
#print axioms FX1Poly.ComputerAlgebra.unitPivotSeedIsRectangular
#print axioms FX1Poly.ComputerAlgebra.unitPivotForcesBlockGcdOne
#print axioms FX1Poly.ComputerAlgebra.landedDividesInputBlockImpliesAbsEqMinorGcd
#print axioms FX1Poly.ComputerAlgebra.operationallyLandedKillerSeedIsRectangular
#print axioms FX1Poly.ComputerAlgebra.operationallyLandedYetMissesMinorGcd
#print axioms FX1Poly.ComputerAlgebra.offCrossEntryEscapesDiagonalFind
#print axioms FX1Poly.ComputerAlgebra.operationallyLandedAntiDiagonalKillerSeedIsRectangular
#print axioms FX1Poly.ComputerAlgebra.antiDiagonalKillerOperationallyLandedYetMissesMinorGcd

end FX1PolyAudit
