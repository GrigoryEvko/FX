import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithLandedMagnitudeEquivalence

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithLandedMagnitudeEquivalence — zero-axiom gate
    (H2-SMITH r32, #2261 — THE DECISION ROUND)

Per-declaration zero-axiom gate for: the reverse magnitude bridge `dividesExactlyOfNatAbsEq`
(`natAbs`-equality forces exact divisibility); the crisp `∀`-magnitude form
`MinAbsEuclidLandsMinorGcdMagnitude` of the open wall; the FULL equivalence
`keystoneIffLandedMagnitudeEqMinorGcd` (`SmithCascadeLandedPivotDividesMinor ↔ |landed| = gcd(minor)`,
completing r29's forward-only half); and the five decisive hostile-seed magnitude fixtures + the
killer-seed `smithMinorAbsSum`-rise corroboration.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`.  Both the fuel-based `#assert_no_axioms` AND the independent (non-fuel)
`#print axioms` are run on every declaration (the project macro is fuel-based — not trusted alone). -/

namespace FX1PolyAudit

/- The reverse magnitude bridge, the crisp Prop, and the full equivalence. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.dividesExactlyOfNatAbsEq
#assert_no_axioms FX1Poly.ComputerAlgebra.MinAbsEuclidLandsMinorGcdMagnitude
#assert_no_axioms FX1Poly.ComputerAlgebra.keystoneIffLandedMagnitudeEqMinorGcd

/- The decisive hostile-seed magnitude fixtures + the killer-seed measure-rise corroboration. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.landedMagnitudeEqMinorGcdOnKillerSeedPivotZero
#assert_no_axioms FX1Poly.ComputerAlgebra.landedMagnitudeEqMinorGcdOnKillerSeedPivotTwo
#assert_no_axioms FX1Poly.ComputerAlgebra.landedMagnitudeEqMinorGcdOnFillInSeedPivotOne
#assert_no_axioms FX1Poly.ComputerAlgebra.landedMagnitudeEqMinorGcdOnHostileNonDiagonalSeed
#assert_no_axioms FX1Poly.ComputerAlgebra.landedMagnitudeEqMinorGcdOnCoprimeSeed
#assert_no_axioms FX1Poly.ComputerAlgebra.smithMinorAbsSumRisesOnKillerSeedFold

-- Independent (non-fuel) axiom prints on every declaration.
#print axioms FX1Poly.ComputerAlgebra.dividesExactlyOfNatAbsEq
#print axioms FX1Poly.ComputerAlgebra.MinAbsEuclidLandsMinorGcdMagnitude
#print axioms FX1Poly.ComputerAlgebra.keystoneIffLandedMagnitudeEqMinorGcd
#print axioms FX1Poly.ComputerAlgebra.landedMagnitudeEqMinorGcdOnKillerSeedPivotZero
#print axioms FX1Poly.ComputerAlgebra.landedMagnitudeEqMinorGcdOnKillerSeedPivotTwo
#print axioms FX1Poly.ComputerAlgebra.landedMagnitudeEqMinorGcdOnFillInSeedPivotOne
#print axioms FX1Poly.ComputerAlgebra.landedMagnitudeEqMinorGcdOnHostileNonDiagonalSeed
#print axioms FX1Poly.ComputerAlgebra.landedMagnitudeEqMinorGcdOnCoprimeSeed
#print axioms FX1Poly.ComputerAlgebra.smithMinorAbsSumRisesOnKillerSeedFold

end FX1PolyAudit
