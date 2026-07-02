import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.IntExactDivision

/-! # FX1PolyAudit/ComputerAlgebra/Number/IntExactDivision — zero-axiom gate
    (FLOAT-2 brick 5a)

Per-declaration zero-axiom gate for the sign-aware exact-division kit: the magnitude
remainder/quotient pair over the counting divider, the exactness theorem a vanishing
remainder yields, and the nonnegative `toNat` round-trip.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.intMagnitudeRemainder
#assert_no_axioms FX1Poly.ComputerAlgebra.intMagnitudeQuotient
#assert_no_axioms FX1Poly.ComputerAlgebra.intMagnitudeDivisionExact
#assert_no_axioms FX1Poly.ComputerAlgebra.intOfNatToNatOfNonNeg

end FX1PolyAudit
