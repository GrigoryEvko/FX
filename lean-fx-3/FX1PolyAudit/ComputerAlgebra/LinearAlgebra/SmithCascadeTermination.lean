import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithCascadeTermination

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithCascadeTermination — zero-axiom gate
    (H2-SMITH r8)

Per-declaration zero-axiom gate for the Euclid-cascade descent-measure infrastructure: the
signed-residue reconstruction, the column ON-target entry formula (and its `mapAllRows` row-read),
the nonnegative-pivot magnitude bridge, the single-clear residue landing, and the minimal-magnitude
search lower bound (row + minor scan, with their update-step and `== 0` helpers).

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
#assert_no_axioms FX1Poly.ComputerAlgebra.smithSingleClearStrictlyDecreasesPivot
#assert_no_axioms FX1Poly.ComputerAlgebra.natBeqZeroFalseOfNe
#assert_no_axioms FX1Poly.ComputerAlgebra.smithScanRowUpdateSomeBound
#assert_no_axioms FX1Poly.ComputerAlgebra.smithScanRowUpdateNoneBound
#assert_no_axioms FX1Poly.ComputerAlgebra.smithScanRowUpdateSomeEntryBound
#assert_no_axioms FX1Poly.ComputerAlgebra.smithScanRowMinAbsPreservesSomeBound
#assert_no_axioms FX1Poly.ComputerAlgebra.smithScanRowMinAbsBoundsWitness
#assert_no_axioms FX1Poly.ComputerAlgebra.smithScanMinorMinAbsPreservesSomeBound
#assert_no_axioms FX1Poly.ComputerAlgebra.smithScanMinorMinAbsBoundsWitness
#assert_no_axioms FX1Poly.ComputerAlgebra.smithFindMinAbsInMinorBoundsWitness

/- H2-SMITH r9 — the clear-word lift + cross-clear fuel adequacy. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.addColumnMultipleEntryOffTargetCol
#assert_no_axioms FX1Poly.ComputerAlgebra.smithClearRowRightStepsPreservesColumn
#assert_no_axioms FX1Poly.ComputerAlgebra.smithClearRowRightStepsLandsAt

end FX1PolyAudit
