import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithBezoutRoundReachableCorpus

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithBezoutRoundReachableCorpus — zero-axiom gate
    (H2-SMITH r47, #2261 — the Bezout-drop round's trajectory corpus + no-regression suite)

Per-declaration zero-axiom gate for the corpus: the K1 application `bezoutRoundDescendsOnKillerA`, the
no-regression Bezout-sweep-lands-minorGcd theorems (killers + clean diagonals + the dirty/zero-pivot
refuters), and the guard-honesty pins (`bezoutRoundRisesOnDirtyRefuter`,
`bezoutDirtyRefuterCrossNotClean`).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`.  Both the fuel-based `#assert_no_axioms` AND the independent (non-fuel)
`#print axioms` are run on every declaration. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.bezoutKillerAIsRectangular
#assert_no_axioms FX1Poly.ComputerAlgebra.bezoutRoundDescendsOnKillerA
#assert_no_axioms FX1Poly.ComputerAlgebra.bezoutSweepKillerALandsMinorGcd
#assert_no_axioms FX1Poly.ComputerAlgebra.bezoutSweepKillerBLandsMinorGcd
#assert_no_axioms FX1Poly.ComputerAlgebra.bezoutSweepSixTenFifteenLandsMinorGcd
#assert_no_axioms FX1Poly.ComputerAlgebra.bezoutSweepThirtyTwentyTwelveLandsMinorGcd
#assert_no_axioms FX1Poly.ComputerAlgebra.bezoutSweepTwoThreeLandsMinorGcd
#assert_no_axioms FX1Poly.ComputerAlgebra.bezoutSweepDirtyRefuterLandsMinorGcd
#assert_no_axioms FX1Poly.ComputerAlgebra.bezoutSweepZeroPivotSeedLandsMinorGcd
#assert_no_axioms FX1Poly.ComputerAlgebra.bezoutRoundRisesOnDirtyRefuter
#assert_no_axioms FX1Poly.ComputerAlgebra.bezoutDirtyRefuterCrossNotClean

-- Independent (non-fuel) axiom prints on every declaration.
#print axioms FX1Poly.ComputerAlgebra.bezoutKillerAIsRectangular
#print axioms FX1Poly.ComputerAlgebra.bezoutRoundDescendsOnKillerA
#print axioms FX1Poly.ComputerAlgebra.bezoutSweepKillerALandsMinorGcd
#print axioms FX1Poly.ComputerAlgebra.bezoutSweepKillerBLandsMinorGcd
#print axioms FX1Poly.ComputerAlgebra.bezoutSweepSixTenFifteenLandsMinorGcd
#print axioms FX1Poly.ComputerAlgebra.bezoutSweepThirtyTwentyTwelveLandsMinorGcd
#print axioms FX1Poly.ComputerAlgebra.bezoutSweepTwoThreeLandsMinorGcd
#print axioms FX1Poly.ComputerAlgebra.bezoutSweepDirtyRefuterLandsMinorGcd
#print axioms FX1Poly.ComputerAlgebra.bezoutSweepZeroPivotSeedLandsMinorGcd
#print axioms FX1Poly.ComputerAlgebra.bezoutRoundRisesOnDirtyRefuter
#print axioms FX1Poly.ComputerAlgebra.bezoutDirtyRefuterCrossNotClean

end FX1PolyAudit
