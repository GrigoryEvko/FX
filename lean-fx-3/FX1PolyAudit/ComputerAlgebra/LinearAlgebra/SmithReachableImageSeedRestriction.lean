import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithReachableImageSeedRestriction

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithReachableImageSeedRestriction — zero-axiom gate
    (H2-SMITH r35, #2261 — the reachable-image restriction round)

Per-declaration zero-axiom gate for: the reachability predicate `ReachableFromPhaseA`; the restricted
seed `SmithCascadeLandsDivisibleSubBlockReachable`; the parallel sibling carrier / reduction /
driver-collapse (`chainWindowedThroughPivotsReachable`, `repairChainHoldsOfSeedReachable`,
`smithReduceCompleteDriverOfSubBlockSeedReachable`); and the refuter-exclusion adjudication
(`reachableAtZeroIsWindowDiagonal`, `refuterNotWindowDiagonal`, `refuterNotReachableAtZero`).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`.  Both the fuel-based `#assert_no_axioms` AND the independent (non-fuel)
`#print axioms` are run on every declaration (the project macro is fuel-based — not trusted alone). -/

namespace FX1PolyAudit

/- The reachability predicate and the restricted seed. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.ReachableFromPhaseA
#assert_no_axioms FX1Poly.ComputerAlgebra.SmithCascadeLandsDivisibleSubBlockReachable

/- The parallel sibling carrier / reduction / driver-collapse. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.chainWindowedThroughPivotsReachable
#assert_no_axioms FX1Poly.ComputerAlgebra.repairChainHoldsOfSeedReachable
#assert_no_axioms FX1Poly.ComputerAlgebra.smithReduceCompleteDriverOfSubBlockSeedReachable

/- The refuter-exclusion adjudication. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.reachableAtZeroIsWindowDiagonal
#assert_no_axioms FX1Poly.ComputerAlgebra.refuterNotWindowDiagonal
#assert_no_axioms FX1Poly.ComputerAlgebra.refuterNotReachableAtZero

-- Independent (non-fuel) axiom prints on every declaration.
#print axioms FX1Poly.ComputerAlgebra.ReachableFromPhaseA
#print axioms FX1Poly.ComputerAlgebra.SmithCascadeLandsDivisibleSubBlockReachable
#print axioms FX1Poly.ComputerAlgebra.chainWindowedThroughPivotsReachable
#print axioms FX1Poly.ComputerAlgebra.repairChainHoldsOfSeedReachable
#print axioms FX1Poly.ComputerAlgebra.smithReduceCompleteDriverOfSubBlockSeedReachable
#print axioms FX1Poly.ComputerAlgebra.reachableAtZeroIsWindowDiagonal
#print axioms FX1Poly.ComputerAlgebra.refuterNotWindowDiagonal
#print axioms FX1Poly.ComputerAlgebra.refuterNotReachableAtZero

end FX1PolyAudit
