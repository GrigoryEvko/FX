import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.IntGapArithmetic

/-! # FX1PolyAudit/ComputerAlgebra/Number/IntGapArithmetic — zero-axiom gate
    (FLOAT-2 brick 4e-i)

Per-declaration zero-axiom gate for the order-aware clamped-gap kit: the base-cancel
witness extractor, the clamped-gap floor symmetry (promoted here from the
RadixScaledInteger carrier), the two floor lower bounds, and the gap-addition lemma
across an intermediate bound.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.intAddCancelLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.intGapFloorSymm
#assert_no_axioms FX1Poly.ComputerAlgebra.intGapFloorLeMinuend
#assert_no_axioms FX1Poly.ComputerAlgebra.intGapFloorLeSubtrahend
#assert_no_axioms FX1Poly.ComputerAlgebra.intGapAdditionAcrossMiddle

end FX1PolyAudit
