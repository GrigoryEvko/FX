import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithCascadeTermination

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithCascadeTermination — zero-axiom gate
    (H2-SMITH r8)

Per-declaration zero-axiom gate for the Euclid-cascade descent-measure infrastructure: the
signed-residue reconstruction, the column ON-target entry formula (and its `mapAllRows` row-read),
the nonnegative-pivot magnitude bridge, and the single-clear residue landing.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.intMagnitudeSignedRemainder
#assert_no_axioms FX1Poly.ComputerAlgebra.intMagnitudeSignedRemainderNatAbs
#assert_no_axioms FX1Poly.ComputerAlgebra.intMagnitudeReconstructs
#assert_no_axioms FX1Poly.ComputerAlgebra.intOfNatNatAbsOfNonNeg
#assert_no_axioms FX1Poly.ComputerAlgebra.listGetWithDefaultMapAllRows
#assert_no_axioms FX1Poly.ComputerAlgebra.addColumnMultipleEntryOnTargetCol
#assert_no_axioms FX1Poly.ComputerAlgebra.smithSingleClearResidueLands

end FX1PolyAudit
