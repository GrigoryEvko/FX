import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithMinorGcdReduction

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithMinorGcdReduction — zero-axiom gate
    (H2-SMITH r29, #2261 — the keystone sharpened to `landed | gcd(minor)`)

Per-declaration zero-axiom gate for: `dividesExactlyTrans` (transitivity of exact divisibility); the
minor-gcd fold `minorGcdRow` / `minorGcdRows` / `minorGcdWithin` and its two universal-property halves
(`minorGcdWithinDividesWithin` — gcd divides every minor cell, fill-in included;
`minorGcdWithinGreatest` — greatest common divisor of the minor) with their structural fold helpers;
the equivalence `keystoneIffLandedDividesMinorGcd`; the hypothesis-free converse `minorGcdDividesLanded`
(`gcd ∣ landed`); and the conditional symmetric magnitude `landedMagnitudeEqMinorGcdOfKeystone`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`.  Both the fuel-based `#assert_no_axioms` AND the independent (non-fuel)
`#print axioms` are run on every declaration (the project macro is fuel-based — not trusted alone). -/

namespace FX1PolyAudit

/- B1 — transitivity of exact divisibility. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.dividesExactlyTrans

/- B2 — the minor-gcd fold and its structural window-divides / greatest halves. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.minorGcdRow
#assert_no_axioms FX1Poly.ComputerAlgebra.minorGcdRows
#assert_no_axioms FX1Poly.ComputerAlgebra.minorGcdWithin
#assert_no_axioms FX1Poly.ComputerAlgebra.minorGcdRowDividesEntry
#assert_no_axioms FX1Poly.ComputerAlgebra.minorGcdRowsDividesRow
#assert_no_axioms FX1Poly.ComputerAlgebra.minorGcdRowsDividesEntry
#assert_no_axioms FX1Poly.ComputerAlgebra.minorGcdWithinDividesWithin
#assert_no_axioms FX1Poly.ComputerAlgebra.minorGcdRowGreatest
#assert_no_axioms FX1Poly.ComputerAlgebra.minorGcdRowsGreatest
#assert_no_axioms FX1Poly.ComputerAlgebra.minorGcdWithinGreatest

/- B3 — the keystone sharpened to `landed ∣ gcd(minor)`. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.LandedPivotDividesMinorGcd
#assert_no_axioms FX1Poly.ComputerAlgebra.keystoneIffLandedDividesMinorGcd

/- B4 — the shipped converse and the symmetric magnitude residual. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.minorGcdDividesLanded
#assert_no_axioms FX1Poly.ComputerAlgebra.landedMagnitudeEqMinorGcdOfKeystone

-- Independent (non-fuel) axiom prints on every declaration.
#print axioms FX1Poly.ComputerAlgebra.dividesExactlyTrans
#print axioms FX1Poly.ComputerAlgebra.minorGcdRow
#print axioms FX1Poly.ComputerAlgebra.minorGcdRows
#print axioms FX1Poly.ComputerAlgebra.minorGcdWithin
#print axioms FX1Poly.ComputerAlgebra.minorGcdRowDividesEntry
#print axioms FX1Poly.ComputerAlgebra.minorGcdRowsDividesRow
#print axioms FX1Poly.ComputerAlgebra.minorGcdRowsDividesEntry
#print axioms FX1Poly.ComputerAlgebra.minorGcdWithinDividesWithin
#print axioms FX1Poly.ComputerAlgebra.minorGcdRowGreatest
#print axioms FX1Poly.ComputerAlgebra.minorGcdRowsGreatest
#print axioms FX1Poly.ComputerAlgebra.minorGcdWithinGreatest
#print axioms FX1Poly.ComputerAlgebra.LandedPivotDividesMinorGcd
#print axioms FX1Poly.ComputerAlgebra.keystoneIffLandedDividesMinorGcd
#print axioms FX1Poly.ComputerAlgebra.minorGcdDividesLanded
#print axioms FX1Poly.ComputerAlgebra.landedMagnitudeEqMinorGcdOfKeystone

end FX1PolyAudit
