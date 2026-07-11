import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithMinNonzeroAbsDescent

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithMinNonzeroAbsDescent — zero-axiom gate
    (H2-SMITH r26, #2261 — the corrected `foldDescends` measure candidate + its stall seam)

Per-declaration zero-axiom gate for the corrected measure `minNonzeroAbsWithin` and its four fold-behaviour
witnesses: two strict descents (`diag(6,10,8)` where `minorAbsSum` rises, and `diag(6,9,10)`) and two
STALLS (`diag(15,10,6,4)` already-minimal, `diag(0,4)` zero-pivot bootstrap) that correct the r26 recon's
"strictly descends on every nonzero-pivot fold" claim.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`.  Both the fuel-based `#assert_no_axioms` AND the independent (non-fuel)
`#print axioms` are run on every declaration (the project macro is fuel-based — not trusted alone). -/

namespace FX1PolyAudit

/- The corrected measure and its accumulator. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.natMinNonzero
#assert_no_axioms FX1Poly.ComputerAlgebra.minNonzeroAbsWithin

/- The fold-behaviour witnesses (strict descents + stalls). -/
#assert_no_axioms FX1Poly.ComputerAlgebra.smithMinNonzeroAbsDescendsWhereMinorAbsSumRises
#assert_no_axioms FX1Poly.ComputerAlgebra.smithMinNonzeroAbsDescendsOnCoprimeSeed
#assert_no_axioms FX1Poly.ComputerAlgebra.smithMinNonzeroAbsStallsOnAlreadyMinimalFold
#assert_no_axioms FX1Poly.ComputerAlgebra.smithMinNonzeroAbsStallsOnZeroPivotBootstrap

-- Independent (non-fuel) axiom prints on every declaration.
#print axioms FX1Poly.ComputerAlgebra.natMinNonzero
#print axioms FX1Poly.ComputerAlgebra.minNonzeroAbsWithin
#print axioms FX1Poly.ComputerAlgebra.smithMinNonzeroAbsDescendsWhereMinorAbsSumRises
#print axioms FX1Poly.ComputerAlgebra.smithMinNonzeroAbsDescendsOnCoprimeSeed
#print axioms FX1Poly.ComputerAlgebra.smithMinNonzeroAbsStallsOnAlreadyMinimalFold
#print axioms FX1Poly.ComputerAlgebra.smithMinNonzeroAbsStallsOnZeroPivotBootstrap

end FX1PolyAudit
