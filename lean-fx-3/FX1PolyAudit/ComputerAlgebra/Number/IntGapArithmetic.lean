import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.IntGapArithmetic

/-! # Zero-axiom gate for `IntGapArithmetic`

Per-declaration zero-axiom gate for the order-aware clamped-gap kit: the base-cancel
witness extractor, the clamped-gap floor symmetry, the two floor lower bounds, and the
gap-addition lemma across an intermediate bound. Every declaration must be free of
`propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, and `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.intAddCancelLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.intGapFloorSymm
#assert_no_axioms FX1Poly.ComputerAlgebra.intGapFloorLeMinuend
#assert_no_axioms FX1Poly.ComputerAlgebra.intGapFloorLeSubtrahend
#assert_no_axioms FX1Poly.ComputerAlgebra.intGapAdditionAcrossMiddle
#assert_no_axioms FX1Poly.ComputerAlgebra.intGapFloorAttainsLowerBound
#assert_no_axioms FX1Poly.ComputerAlgebra.intGapToNatEqZeroOfLe
#assert_no_axioms FX1Poly.ComputerAlgebra.intPumpedGapsBalance

end FX1PolyAudit
