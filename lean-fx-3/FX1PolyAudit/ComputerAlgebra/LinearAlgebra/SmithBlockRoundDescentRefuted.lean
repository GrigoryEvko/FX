import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithBlockRoundDescentRefuted

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithBlockRoundDescentRefuted — zero-axiom gate
    (H2-SMITH r46, #2261 — the corrected whole-block round's per-round descent is FALSE)

Per-declaration zero-axiom gate for the r46 refutation of the CORRECTED whole-block round's per-round
pivot-magnitude descent: the headline `smithBlockRoundDescendsPerRoundIsRefuted`, the dirty-column
counterexample facts (`...RaisesPivotOnDirtyColumn`, `...LandsPivotThree`), the adequacy-holds pins
(`...FullLoopReachesFindNone`, `...FullLoopLandsMinorGcd`), and the zero-pivot bootstrap
(`...ZeroPivotBootstrapRises`, `...ZeroPivotSeedFindsSome`).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`.  Both the fuel-based `#assert_no_axioms` AND the independent (non-fuel)
`#print axioms` are run on every declaration (the project macro is fuel-based — not trusted alone). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.smithBlockRoundCounterexampleIsRectangular
#assert_no_axioms FX1Poly.ComputerAlgebra.smithBlockRoundCounterexamplePivotPositive
#assert_no_axioms FX1Poly.ComputerAlgebra.smithBlockRoundCounterexampleFindsSome
#assert_no_axioms FX1Poly.ComputerAlgebra.smithBlockRoundLandsPivotThree
#assert_no_axioms FX1Poly.ComputerAlgebra.smithBlockRoundRaisesPivotOnDirtyColumn
#assert_no_axioms FX1Poly.ComputerAlgebra.smithBlockRoundCounterexampleFullLoopReachesFindNone
#assert_no_axioms FX1Poly.ComputerAlgebra.smithBlockRoundCounterexampleFullLoopLandsMinorGcd
#assert_no_axioms FX1Poly.ComputerAlgebra.smithBlockRoundZeroPivotSeedIsRectangular
#assert_no_axioms FX1Poly.ComputerAlgebra.smithBlockRoundZeroPivotSeedPivotMagnitudeZero
#assert_no_axioms FX1Poly.ComputerAlgebra.smithBlockRoundZeroPivotSeedFindsSome
#assert_no_axioms FX1Poly.ComputerAlgebra.smithBlockRoundZeroPivotBootstrapRises
#assert_no_axioms FX1Poly.ComputerAlgebra.smithBlockRoundDescendsPerRoundIsRefuted

-- Independent (non-fuel) axiom prints on every declaration.
#print axioms FX1Poly.ComputerAlgebra.smithBlockRoundCounterexampleIsRectangular
#print axioms FX1Poly.ComputerAlgebra.smithBlockRoundCounterexamplePivotPositive
#print axioms FX1Poly.ComputerAlgebra.smithBlockRoundCounterexampleFindsSome
#print axioms FX1Poly.ComputerAlgebra.smithBlockRoundLandsPivotThree
#print axioms FX1Poly.ComputerAlgebra.smithBlockRoundRaisesPivotOnDirtyColumn
#print axioms FX1Poly.ComputerAlgebra.smithBlockRoundCounterexampleFullLoopReachesFindNone
#print axioms FX1Poly.ComputerAlgebra.smithBlockRoundCounterexampleFullLoopLandsMinorGcd
#print axioms FX1Poly.ComputerAlgebra.smithBlockRoundZeroPivotSeedIsRectangular
#print axioms FX1Poly.ComputerAlgebra.smithBlockRoundZeroPivotSeedPivotMagnitudeZero
#print axioms FX1Poly.ComputerAlgebra.smithBlockRoundZeroPivotSeedFindsSome
#print axioms FX1Poly.ComputerAlgebra.smithBlockRoundZeroPivotBootstrapRises
#print axioms FX1Poly.ComputerAlgebra.smithBlockRoundDescendsPerRoundIsRefuted

end FX1PolyAudit
