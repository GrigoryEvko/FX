import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithConfinedColumnDescentInsufficient

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithConfinedColumnDescentInsufficient — zero-axiom gate
    (H2-SMITH r40, #2261 — the `belowPivotColumnConfined`-guarded one-round descent is FALSE; the corrected
    lever adds the below-pivot-column DEEP-ZERO conjunct)

Per-declaration zero-axiom gate for the r40 graveyard + guard-correction round: the counterexample
`smithConfinedColumnDescentCounterexample` and its pins, the GRAVEYARD
`smithFoldDescendsOnConfinedNonzeroPivotIsRefuted` (the r39 confined gate is machine-FALSE — a
confined-but-deep-dirty 3×3 STALLS the fold), the corrected lever `belowPivotColumnZeroDeep` /
`belowPivotColumnClean`, the separation battery (`smithConfinedGuardAdmitsRefuter`,
`smithCleanGuardExcludesRefuter`), the corrected candidate `SmithFoldDescendsOnColumnCleanNonzeroPivot` +
its clean-witness descent, the L2' free-preservation theorems (`smithClearingFoldStepColumnBelowZero`,
`smithClearingFoldStepColumnZeroDeep`, `smithClearingFoldStepConfined`, `smithClearingFoldStepColumnClean`),
and the re-shaped D3 `smithClearingOutputFindNoneFromColumnCleanFoldDescent`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`.  Both the fuel-based `#assert_no_axioms` AND the independent (non-fuel)
`#print axioms` are run on every declaration (the project macro is fuel-based — not trusted alone). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.smithConfinedColumnDescentCounterexample
#assert_no_axioms FX1Poly.ComputerAlgebra.smithConfinedColumnDescentCounterexampleIsRectangular
#assert_no_axioms FX1Poly.ComputerAlgebra.smithConfinedColumnDescentCounterexampleConfined
#assert_no_axioms FX1Poly.ComputerAlgebra.smithConfinedColumnDescentCounterexamplePivotPositive
#assert_no_axioms FX1Poly.ComputerAlgebra.smithConfinedColumnDescentCounterexampleFindsSome
#assert_no_axioms FX1Poly.ComputerAlgebra.smithConfinedColumnFoldStallsOnCounterexample
#assert_no_axioms FX1Poly.ComputerAlgebra.smithFoldDescendsOnConfinedNonzeroPivotIsRefuted
#assert_no_axioms FX1Poly.ComputerAlgebra.belowPivotColumnZeroDeep
#assert_no_axioms FX1Poly.ComputerAlgebra.belowPivotColumnClean
#assert_no_axioms FX1Poly.ComputerAlgebra.smithConfinedGuardAdmitsRefuter
#assert_no_axioms FX1Poly.ComputerAlgebra.smithCleanGuardExcludesRefuter
#assert_no_axioms FX1Poly.ComputerAlgebra.SmithFoldDescendsOnColumnCleanNonzeroPivot
#assert_no_axioms FX1Poly.ComputerAlgebra.smithColumnCleanCandidateDescendsOnCleanWitness
#assert_no_axioms FX1Poly.ComputerAlgebra.smithClearingFoldStepColumnBelowZero
#assert_no_axioms FX1Poly.ComputerAlgebra.smithClearingFoldStepColumnZeroDeep
#assert_no_axioms FX1Poly.ComputerAlgebra.smithClearingFoldStepConfined
#assert_no_axioms FX1Poly.ComputerAlgebra.smithClearingFoldStepColumnClean
#assert_no_axioms FX1Poly.ComputerAlgebra.smithClearingOutputFindNoneFromColumnCleanFoldDescent

-- Independent (non-fuel) axiom prints on every declaration.
#print axioms FX1Poly.ComputerAlgebra.smithConfinedColumnDescentCounterexample
#print axioms FX1Poly.ComputerAlgebra.smithConfinedColumnDescentCounterexampleIsRectangular
#print axioms FX1Poly.ComputerAlgebra.smithConfinedColumnDescentCounterexampleConfined
#print axioms FX1Poly.ComputerAlgebra.smithConfinedColumnDescentCounterexamplePivotPositive
#print axioms FX1Poly.ComputerAlgebra.smithConfinedColumnDescentCounterexampleFindsSome
#print axioms FX1Poly.ComputerAlgebra.smithConfinedColumnFoldStallsOnCounterexample
#print axioms FX1Poly.ComputerAlgebra.smithFoldDescendsOnConfinedNonzeroPivotIsRefuted
#print axioms FX1Poly.ComputerAlgebra.belowPivotColumnZeroDeep
#print axioms FX1Poly.ComputerAlgebra.belowPivotColumnClean
#print axioms FX1Poly.ComputerAlgebra.smithConfinedGuardAdmitsRefuter
#print axioms FX1Poly.ComputerAlgebra.smithCleanGuardExcludesRefuter
#print axioms FX1Poly.ComputerAlgebra.SmithFoldDescendsOnColumnCleanNonzeroPivot
#print axioms FX1Poly.ComputerAlgebra.smithColumnCleanCandidateDescendsOnCleanWitness
#print axioms FX1Poly.ComputerAlgebra.smithClearingFoldStepColumnBelowZero
#print axioms FX1Poly.ComputerAlgebra.smithClearingFoldStepColumnZeroDeep
#print axioms FX1Poly.ComputerAlgebra.smithClearingFoldStepConfined
#print axioms FX1Poly.ComputerAlgebra.smithClearingFoldStepColumnClean
#print axioms FX1Poly.ComputerAlgebra.smithClearingOutputFindNoneFromColumnCleanFoldDescent

end FX1PolyAudit
